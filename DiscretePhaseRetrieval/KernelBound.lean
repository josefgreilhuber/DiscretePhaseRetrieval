import DiscretePhaseRetrieval.Bridge

/-!
# Claim K: the reproducing-kernel bound

The paper (p. 6) uses `|F(z)| ≤ C_{‖q‖₁} (1+|z|)^{‖q‖₁} e^{|z|²/2} ‖F‖`. In the coefficient model
this is Cauchy–Schwarz together with a bound on the diagonal of the kernel, `∑_α |Φ_{α,κ}(z)|²`.

One variable: for the level `k` and `w ∈ ℂ`, `t = |w|²`,
`∑_m |φ_{m,k}(w)|² ≤ C_k (1 + t)^{4k} e^{t}`. Proof: for every `m ≥ k` each term of the defining
sum satisfies `r! C(m,r) C(k,r) |w|^{m+k−2r} ≤ 2^k m^k |w|^{m−k} (1 + t^k)`, so
`|φ_{m,k}(w)|² ≤ ((k+1) 2^k (1+t^k))² m^{2k} t^{m−k}/m!`; for `m ≥ 4k` moreover
`m^{2k}/m! ≤ 4^k/(m−2k)!`, and reindexing by `j = m − 2k` the tail sums to at most
`C_k (1+t^k)² t^k e^t ≤ C_k' (1+t)^{4k} e^t`; the finitely many `m < 4k` contribute a
polynomial in `t`, which is again dominated by `C e^t`. Tensoring over the `d` coordinates gives
`∑_α ‖Φ_{α,κ}(z)‖² = ∏_i ∑_m |φ_{m,κᵢ}(zᵢ)|²` (a product of summable nonnegative series).

The two pointwise estimates used here, `sq_norm_phi_le_gen` (all `m ≥ k`) and
`sq_norm_phi_le_mid` (the finitely many `m ≤ 4k`), are not proved from scratch: they are the two
instances of the core estimate `PolyFock.norm_phi_le_of_term_le` of `PolyFock/PhiBound.lean` that
do not assume `‖w‖² ≤ m`, and each contributes only its term bound `T` (see the module docstring
there; the third instance is `PolyFock.sq_norm_phi_le`, used by the tail bound).

The mixed-level basis `Ψ_{α,h}` is handled at the end of the file: Cauchy–Schwarz over the
finitely many levels of `supp h` gives `‖Ψ_{α,h}(z)‖² ≤ ∑_{q ∈ supp h} ‖Φ_{α,q}(z)‖²`
(`sq_norm_Psi_le`), so the single-level bounds sum up, with the polynomial factor taken at the
largest level `L = levelBound h` (`kernel_bound_mixed`).
-/

open MeasureTheory PolyFock PolyFock.Fock

namespace DiscretePR

open Finset

variable {d : ℕ}

/-! ### Elementary auxiliary estimates -/

/-- Any power of `1 + t` is dominated by a multiple of `e^t` on `t ≥ 0`. -/
private lemma poly_le_exp (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ a ≤ C * Real.exp t := by
  refine ⟨2 ^ a * (1 + (a.factorial : ℝ)), by positivity, fun t ht => ?_⟩
  have hexp1 : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
  have hfacpos : (0 : ℝ) < (a.factorial : ℝ) := by exact_mod_cast a.factorial_pos
  have h2 : t ^ a ≤ (a.factorial : ℝ) * Real.exp t := by
    have h := Real.pow_div_factorial_le_exp t ht a
    rw [div_le_iff₀ hfacpos] at h
    linarith
  have hta : (0 : ℝ) ≤ t ^ a := by positivity
  have h2pow : (0 : ℝ) < 2 ^ a := by positivity
  have h1 : (1 + t) ^ a ≤ 2 ^ a * (1 + t ^ a) := by
    rcases le_total t 1 with h | h
    · have hb : (1 + t) ^ a ≤ 2 ^ a := pow_le_pow_left₀ (by linarith) (by linarith) a
      nlinarith
    · have hb : (1 + t) ^ a ≤ (2 * t) ^ a := pow_le_pow_left₀ (by linarith) (by linarith) a
      rw [mul_pow] at hb
      nlinarith
  calc (1 + t) ^ a ≤ 2 ^ a * (1 + t ^ a) := h1
    _ ≤ 2 ^ a * (Real.exp t + (a.factorial : ℝ) * Real.exp t) := by
        have : (1 : ℝ) + t ^ a ≤ Real.exp t + (a.factorial : ℝ) * Real.exp t := by linarith
        exact mul_le_mul_of_nonneg_left this h2pow.le
    _ = 2 ^ a * (1 + (a.factorial : ℝ)) * Real.exp t := by ring

/-- `(1+s)² s ≤ 4 P⁴` whenever `0 ≤ s ≤ P` and `1 ≤ P`. -/
private lemma aux_cube {s P : ℝ} (hs0 : 0 ≤ s) (hP1 : 1 ≤ P) (hsP : s ≤ P) :
    (1 + s) ^ 2 * s ≤ 4 * P ^ 4 := by
  have h1 : (1 + s) ^ 2 ≤ (1 + P) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : (1 + s) ^ 2 * s ≤ (1 + P) ^ 2 * P := mul_le_mul h1 hsP hs0 (by positivity)
  have h3 : (1 + P) ^ 2 * P ≤ (2 * P) ^ 2 * P := by nlinarith
  have h4 : P ^ 3 ≤ P ^ 4 := pow_le_pow_right₀ hP1 (by norm_num)
  nlinarith

/-- `∑_{m < M} (if m ≤ K then b else 0) ≤ (K+1) b`. -/
private lemma sum_ite_le_card {b : ℝ} (hb : 0 ≤ b) (K M : ℕ) :
    ∑ m ∈ range M, (if m ≤ K then b else 0) ≤ ((K : ℝ) + 1) * b := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((range M).filter (fun m => m ≤ K)).card ≤ K + 1 := by
    calc ((range M).filter (fun m => m ≤ K)).card ≤ (range (K + 1)).card := by
          refine Finset.card_le_card ?_
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
          omega
      _ = K + 1 := Finset.card_range _
  have : (((range M).filter (fun m => m ≤ K)).card : ℝ) ≤ (K : ℝ) + 1 := by
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right this hb

/-- The shifted exponential tail: `∑_{4k < m < M} t^{m-2k}/(m-2k)! ≤ e^t`. -/
private lemma sum_shift_exp_le {t : ℝ} (ht : 0 ≤ t) (k M : ℕ) :
    ∑ m ∈ range M, (if 4 * k < m then t ^ (m - 2 * k) / ((m - 2 * k).factorial : ℝ) else 0)
      ≤ Real.exp t := by
  rw [← Finset.sum_filter]
  have hinj : ∀ a ∈ (range M).filter (fun m => 4 * k < m),
      ∀ b ∈ (range M).filter (fun m => 4 * k < m), a - 2 * k = b - 2 * k → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    omega
  have hsub : ((range M).filter (fun m => 4 * k < m)).image (fun m => m - 2 * k) ⊆ range M := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨m, ⟨hm1, _⟩, rfl⟩ := hj
    simp only [Finset.mem_range]
    omega
  calc ∑ m ∈ (range M).filter (fun m => 4 * k < m), t ^ (m - 2 * k) / ((m - 2 * k).factorial : ℝ)
      = ∑ j ∈ ((range M).filter (fun m => 4 * k < m)).image (fun m => m - 2 * k),
          t ^ j / ((j.factorial : ℝ)) :=
        (Finset.sum_image (f := fun j : ℕ => t ^ j / ((j.factorial : ℝ))) hinj).symm
    _ ≤ ∑ j ∈ range M, t ^ j / ((j.factorial : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    _ ≤ Real.exp t := Real.sum_le_exp_of_nonneg ht M

/-! ### One-variable estimates for `φ_{m,k}` -/

/-- The general bound `‖φ_{m,k}(w)‖² ≤ ((k+1) 2^k (1+t^k))² m^{2k} t^{m-k}/m!` for `k ≤ m`,
where `t = ‖w‖²`.  Unlike `PolyFock.sq_norm_phi_le` this does not require `t ≤ m`.

The instance of the core estimate `PolyFock.norm_phi_le_of_term_le` with the term bound
`T = m^k 2^k (‖w‖^{m-k} (1 + (‖w‖²)^k))`. -/
private lemma sq_norm_phi_le_gen (k m : ℕ) (hkm : k ≤ m) (w : ℂ) :
    ‖HermitePoly m k w‖ ^ 2 ≤ (((k : ℝ) + 1) * 2 ^ k * (1 + (‖w‖ ^ 2) ^ k)) ^ 2 *
      ((m : ℝ) ^ (2 * k) * (‖w‖ ^ 2) ^ (m - k) / (m.factorial : ℝ)) := by
  have hmin : min m k = k := min_eq_right hkm
  have hterm : ∀ r ≤ min m k,
      (r.factorial : ℝ) * (m.choose r : ℝ) * (k.choose r : ℝ) * ‖w‖ ^ (m - r) * ‖w‖ ^ (k - r)
        ≤ (m : ℝ) ^ k * 2 ^ k * (‖w‖ ^ (m - k) * (1 + (‖w‖ ^ 2) ^ k)) := by
    intro r hr
    rw [hmin] at hr
    have hmpow : (m : ℝ) ^ r ≤ (m : ℝ) ^ k := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · have : r = k := by omega
        rw [this]
      · exact pow_le_pow_right₀ (by exact_mod_cast hm) hr
    have hchoose : (k.choose r : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.choose_le_two_pow k r
    have hxpow : (‖w‖ ^ 2) ^ (k - r) ≤ 1 + (‖w‖ ^ 2) ^ k := by
      rcases le_total (‖w‖ ^ 2) 1 with h | h
      · have h1 : (‖w‖ ^ 2) ^ (k - r) ≤ 1 := pow_le_one₀ (by positivity) h
        have h2 : (0 : ℝ) ≤ (‖w‖ ^ 2) ^ k := by positivity
        linarith
      · have h1 : (‖w‖ ^ 2) ^ (k - r) ≤ (‖w‖ ^ 2) ^ k := pow_le_pow_right₀ h (by omega)
        linarith
    exact PolyFock.phi_term_le hkm hr hmpow hchoose hxpow (by positivity)
  have h2k : (m : ℝ) ^ (2 * k) = ((m : ℝ) ^ k) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  have hzz : (‖w‖ ^ 2) ^ (m - k) = (‖w‖ ^ (m - k)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  calc ‖HermitePoly m k w‖ ^ 2
      ≤ (((k : ℝ) + 1) *
          ((m : ℝ) ^ k * 2 ^ k * (‖w‖ ^ (m - k) * (1 + (‖w‖ ^ 2) ^ k)))) ^ 2 /
            (m.factorial : ℝ) :=
        PolyFock.sq_norm_phi_le_of_norm_le
          (PolyFock.norm_phi_le_of_term_le (by positivity) hmin.le hterm)
    _ = (((k : ℝ) + 1) * 2 ^ k * (1 + (‖w‖ ^ 2) ^ k)) ^ 2 *
          ((m : ℝ) ^ (2 * k) * (‖w‖ ^ 2) ^ (m - k) / (m.factorial : ℝ)) := by
        rw [h2k, hzz]; ring

/-- `m^{2k}/m! ≤ 4^k/(m-2k)!` for `m ≥ 4k`. -/
private lemma pow_div_factorial_le' (k m : ℕ) (hm : 4 * k ≤ m) :
    (m : ℝ) ^ (2 * k) / (m.factorial : ℝ) ≤ 4 ^ k / ((m - 2 * k).factorial : ℝ) := by
  have h2k : 2 * k ≤ m := by omega
  have hD : ((m - 2 * k).factorial : ℝ) * (m.descFactorial (2 * k) : ℝ) = (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial h2k
  have hDpos : (0 : ℝ) < (m.descFactorial (2 * k) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr h2k
  have hFpos : (0 : ℝ) < ((m - 2 * k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m - 2 * k)
  have hpow : (m : ℝ) ^ (2 * k) ≤ 4 ^ k * (m.descFactorial (2 * k) : ℝ) := by
    have hn : m ^ (2 * k) ≤ 4 ^ k * m.descFactorial (2 * k) := by
      have h1 : m ^ (2 * k) ≤ (2 * (m + 1 - 2 * k)) ^ (2 * k) :=
        Nat.pow_le_pow_left (by omega) _
      have h2 : (2 * (m + 1 - 2 * k)) ^ (2 * k) = 4 ^ k * (m + 1 - 2 * k) ^ (2 * k) := by
        rw [mul_pow, pow_mul]
        norm_num
      have h3 := Nat.pow_sub_le_descFactorial m (2 * k)
      calc m ^ (2 * k) ≤ 4 ^ k * (m + 1 - 2 * k) ^ (2 * k) := by rw [← h2]; exact h1
        _ ≤ 4 ^ k * m.descFactorial (2 * k) := Nat.mul_le_mul_left _ h3
    exact_mod_cast hn
  rw [← hD, div_le_div_iff₀ (by positivity) hFpos]
  nlinarith [hFpos, hpow]

/-- The tail bound: for `4k ≤ m`, with `t = ‖w‖²`,
`‖φ_{m,k}(w)‖² ≤ ((k+1)2^k)² 4^k (1+t^k)² t^k · t^{m-2k}/(m-2k)!`. -/
private lemma sq_norm_phi_le_tail (k m : ℕ) (hm : 4 * k ≤ m) (w : ℂ) :
    ‖HermitePoly m k w‖ ^ 2 ≤ ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k * (1 + (‖w‖ ^ 2) ^ k) ^ 2 *
      (‖w‖ ^ 2) ^ k) * ((‖w‖ ^ 2) ^ (m - 2 * k) / ((m - 2 * k).factorial : ℝ)) := by
  have hkm : k ≤ m := by omega
  have ht0 : (0 : ℝ) ≤ ‖w‖ ^ 2 := by positivity
  have h1 := sq_norm_phi_le_gen k m hkm w
  have h2 := pow_div_factorial_le' k m hm
  have hsplit : (‖w‖ ^ 2) ^ (m - k) = (‖w‖ ^ 2) ^ k * (‖w‖ ^ 2) ^ (m - 2 * k) := by
    rw [← pow_add]
    congr 1
    omega
  have hc : (0 : ℝ) ≤ (((k : ℝ) + 1) * 2 ^ k * (1 + (‖w‖ ^ 2) ^ k)) ^ 2 := by positivity
  have hstep : (m : ℝ) ^ (2 * k) * (‖w‖ ^ 2) ^ (m - k) / (m.factorial : ℝ)
      ≤ 4 ^ k * (‖w‖ ^ 2) ^ k * ((‖w‖ ^ 2) ^ (m - 2 * k) / ((m - 2 * k).factorial : ℝ)) := by
    rw [hsplit]
    have hpos : (0 : ℝ) ≤ (‖w‖ ^ 2) ^ k * (‖w‖ ^ 2) ^ (m - 2 * k) := by positivity
    calc (m : ℝ) ^ (2 * k) * ((‖w‖ ^ 2) ^ k * (‖w‖ ^ 2) ^ (m - 2 * k)) / (m.factorial : ℝ)
        = ((m : ℝ) ^ (2 * k) / (m.factorial : ℝ)) *
            ((‖w‖ ^ 2) ^ k * (‖w‖ ^ 2) ^ (m - 2 * k)) := by ring
      _ ≤ (4 ^ k / ((m - 2 * k).factorial : ℝ)) *
            ((‖w‖ ^ 2) ^ k * (‖w‖ ^ 2) ^ (m - 2 * k)) := mul_le_mul_of_nonneg_right h2 hpos
      _ = 4 ^ k * (‖w‖ ^ 2) ^ k * ((‖w‖ ^ 2) ^ (m - 2 * k) / ((m - 2 * k).factorial : ℝ)) := by
          ring
  calc ‖HermitePoly m k w‖ ^ 2
      ≤ (((k : ℝ) + 1) * 2 ^ k * (1 + (‖w‖ ^ 2) ^ k)) ^ 2 *
          ((m : ℝ) ^ (2 * k) * (‖w‖ ^ 2) ^ (m - k) / (m.factorial : ℝ)) := h1
    _ ≤ (((k : ℝ) + 1) * 2 ^ k * (1 + (‖w‖ ^ 2) ^ k)) ^ 2 *
          (4 ^ k * (‖w‖ ^ 2) ^ k *
            ((‖w‖ ^ 2) ^ (m - 2 * k) / ((m - 2 * k).factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep hc
    _ = ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k * (1 + (‖w‖ ^ 2) ^ k) ^ 2 * (‖w‖ ^ 2) ^ k) *
          ((‖w‖ ^ 2) ^ (m - 2 * k) / ((m - 2 * k).factorial : ℝ)) := by ring

/-- The constant used for the finitely many indices `m ≤ 4k`. -/
private noncomputable def midConst (k : ℕ) : ℝ :=
  (((k : ℝ) + 1) * ((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k) ^ 2 * 2 ^ (5 * k)

private lemma midConst_nonneg (k : ℕ) : 0 ≤ midConst k := by
  unfold midConst; positivity

/-- The crude bound for the finitely many indices `m ≤ 4k`.

The instance of the core estimate `PolyFock.norm_phi_le_of_term_le` with the term bound
`T = (4k)! 2^{4k} 2^k (1 + ‖w‖)^{5k}`; here even the factor `(√(m!))⁻¹ ≤ 1` is discarded. -/
private lemma sq_norm_phi_le_mid (k m : ℕ) (hm : m ≤ 4 * k) (w : ℂ) :
    ‖HermitePoly m k w‖ ^ 2 ≤ midConst k * (1 + ‖w‖ ^ 2) ^ (5 * k) := by
  have hx : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  -- termwise bound of the defining sum
  have hterm : ∀ r ≤ min m k,
      (r.factorial : ℝ) * (m.choose r : ℝ) * (k.choose r : ℝ) * ‖w‖ ^ (m - r) * ‖w‖ ^ (k - r)
        ≤ ((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k * (1 + ‖w‖) ^ (5 * k) := by
    intro r hr
    rw [le_min_iff] at hr
    obtain ⟨hrm, hrk⟩ := hr
    have h1 : (r.factorial : ℝ) ≤ ((4 * k).factorial : ℝ) := by
      have : r.factorial ≤ (4 * k).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    have h2 : (m.choose r : ℝ) ≤ 2 ^ (4 * k) := by
      have : m.choose r ≤ 2 ^ (4 * k) :=
        (Nat.choose_le_two_pow m r).trans (Nat.pow_le_pow_right (by norm_num) hm)
      exact_mod_cast this
    have h3 : (k.choose r : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.choose_le_two_pow k r
    have h4 : ‖w‖ ^ (m - r) * ‖w‖ ^ (k - r) ≤ (1 + ‖w‖) ^ (5 * k) := by
      calc ‖w‖ ^ (m - r) * ‖w‖ ^ (k - r) = ‖w‖ ^ ((m - r) + (k - r)) := by rw [pow_add]
        _ ≤ (1 + ‖w‖) ^ ((m - r) + (k - r)) := pow_le_pow_left₀ hx (by linarith) _
        _ ≤ (1 + ‖w‖) ^ (5 * k) := pow_le_pow_right₀ (by linarith) (by omega)
    calc (r.factorial : ℝ) * (m.choose r : ℝ) * (k.choose r : ℝ) * ‖w‖ ^ (m - r) * ‖w‖ ^ (k - r)
        = ((r.factorial : ℝ) * (m.choose r : ℝ) * (k.choose r : ℝ)) *
            (‖w‖ ^ (m - r) * ‖w‖ ^ (k - r)) := by ring
      _ ≤ (((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k) * (1 + ‖w‖) ^ (5 * k) := by
          refine mul_le_mul ?_ h4 (by positivity) (by positivity)
          exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
            (by positivity) (by positivity)
      _ = ((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k * (1 + ‖w‖) ^ (5 * k) := by ring
  -- the core estimate, with the prefactor `(√(m!))⁻¹ ≤ 1` discarded
  have hprefac : (Real.sqrt (m.factorial : ℝ))⁻¹ ≤ 1 := by
    refine inv_le_one_of_one_le₀ ?_
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast m.factorial_pos)
  have hnorm : ‖HermitePoly m k w‖ ≤
      ((k : ℝ) + 1) * ((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k * (1 + ‖w‖) ^ (5 * k) := by
    calc ‖HermitePoly m k w‖
        ≤ ((k : ℝ) + 1) *
            (((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k * (1 + ‖w‖) ^ (5 * k)) *
              (Real.sqrt (m.factorial : ℝ))⁻¹ :=
          PolyFock.norm_phi_le_of_term_le (by positivity) (min_le_right m k) hterm
      _ ≤ ((k : ℝ) + 1) *
            (((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k * (1 + ‖w‖) ^ (5 * k)) * 1 :=
          mul_le_mul_of_nonneg_left hprefac (by positivity)
      _ = ((k : ℝ) + 1) * ((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k *
            (1 + ‖w‖) ^ (5 * k) := by ring
  -- square, and convert `(1+x)^{10k}` into `2^{5k} (1+x²)^{5k}`
  have hsq := pow_le_pow_left₀ (norm_nonneg (HermitePoly m k w)) hnorm 2
  have hconv : ((1 + ‖w‖) ^ (5 * k)) ^ 2 ≤ 2 ^ (5 * k) * (1 + ‖w‖ ^ 2) ^ (5 * k) := by
    have h1 : ((1 + ‖w‖) ^ (5 * k)) ^ 2 = ((1 + ‖w‖) ^ 2) ^ (5 * k) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have h2 : ((1 + ‖w‖) ^ 2) ^ (5 * k) ≤ (2 * (1 + ‖w‖ ^ 2)) ^ (5 * k) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      nlinarith [sq_nonneg (1 - ‖w‖)]
    rw [h1]
    calc ((1 + ‖w‖) ^ 2) ^ (5 * k) ≤ (2 * (1 + ‖w‖ ^ 2)) ^ (5 * k) := h2
      _ = 2 ^ (5 * k) * (1 + ‖w‖ ^ 2) ^ (5 * k) := by rw [mul_pow]
  calc ‖HermitePoly m k w‖ ^ 2
      ≤ (((k : ℝ) + 1) * ((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k *
          (1 + ‖w‖) ^ (5 * k)) ^ 2 := hsq
    _ = (((k : ℝ) + 1) * ((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k) ^ 2 *
          ((1 + ‖w‖) ^ (5 * k)) ^ 2 := by ring
    _ ≤ (((k : ℝ) + 1) * ((4 * k).factorial : ℝ) * 2 ^ (4 * k) * 2 ^ k) ^ 2 *
          (2 ^ (5 * k) * (1 + ‖w‖ ^ 2) ^ (5 * k)) :=
        mul_le_mul_of_nonneg_left hconv (by positivity)
    _ = midConst k * (1 + ‖w‖ ^ 2) ^ (5 * k) := by unfold midConst; ring

/-- One-variable kernel bound: `∑_m |φ_{m,k}(w)|² ≤ C_k (1+|w|²)^{4k} e^{|w|²}`. -/
theorem sum_sq_phi_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, Summable (fun m ↦ ‖HermitePoly m k w‖ ^ 2) ∧
      ∑' m, ‖HermitePoly m k w‖ ^ 2 ≤ C * (1 + ‖w‖ ^ 2) ^ (4 * k) * Real.exp (‖w‖ ^ 2) := by
  obtain ⟨Cexp, hCexp0, hCexp⟩ := poly_le_exp (5 * k)
  refine ⟨(4 * (k : ℝ) + 1) * midConst k * Cexp + 4 * ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k),
    add_nonneg (mul_nonneg (mul_nonneg (by positivity) (midConst_nonneg k)) hCexp0)
      (by positivity), fun w => ?_⟩
  set t : ℝ := ‖w‖ ^ 2 with htdef
  have ht0 : (0 : ℝ) ≤ t := by rw [htdef]; positivity
  have hf0 : ∀ m : ℕ, (0 : ℝ) ≤ ‖HermitePoly m k w‖ ^ 2 := fun m => by positivity
  -- the two pieces
  have hmid : ∀ m : ℕ, m ≤ 4 * k → ‖HermitePoly m k w‖ ^ 2 ≤ midConst k * (1 + t) ^ (5 * k) := by
    intro m hm
    rw [htdef]
    exact sq_norm_phi_le_mid k m hm w
  set G : ℝ := (((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k * (1 + t ^ k) ^ 2 * t ^ k with hGdef
  have hG0 : (0 : ℝ) ≤ G := by rw [hGdef]; positivity
  have htail : ∀ m : ℕ, 4 * k < m →
      ‖HermitePoly m k w‖ ^ 2 ≤ G * (t ^ (m - 2 * k) / (((m - 2 * k).factorial : ℝ))) := by
    intro m hm
    rw [hGdef, htdef]
    exact sq_norm_phi_le_tail k m (by omega) w
  -- the uniform bound on partial sums
  have hstep : ∀ M : ℕ, ∑ m ∈ range M, ‖HermitePoly m k w‖ ^ 2
      ≤ (4 * (k : ℝ) + 1) * (midConst k * (1 + t) ^ (5 * k)) + G * Real.exp t := by
    intro M
    have hptwise : ∀ m ∈ range M, ‖HermitePoly m k w‖ ^ 2
        ≤ (if m ≤ 4 * k then midConst k * (1 + t) ^ (5 * k) else 0)
          + G * (if 4 * k < m then t ^ (m - 2 * k) / (((m - 2 * k).factorial : ℝ)) else 0) := by
      intro m _
      rcases le_or_gt m (4 * k) with h | h
      · rw [if_pos h, if_neg (by omega), mul_zero, add_zero]
        exact hmid m h
      · rw [if_neg (by omega), if_pos h, zero_add]
        exact htail m h
    calc ∑ m ∈ range M, ‖HermitePoly m k w‖ ^ 2
        ≤ ∑ m ∈ range M, ((if m ≤ 4 * k then midConst k * (1 + t) ^ (5 * k) else 0)
            + G * (if 4 * k < m then t ^ (m - 2 * k) / (((m - 2 * k).factorial : ℝ)) else 0)) :=
          Finset.sum_le_sum hptwise
      _ = (∑ m ∈ range M, (if m ≤ 4 * k then midConst k * (1 + t) ^ (5 * k) else 0))
            + G * ∑ m ∈ range M,
              (if 4 * k < m then t ^ (m - 2 * k) / (((m - 2 * k).factorial : ℝ)) else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (4 * (k : ℝ) + 1) * (midConst k * (1 + t) ^ (5 * k)) + G * Real.exp t := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left (sum_shift_exp_le ht0 k M) hG0)
          have h := sum_ite_le_card
            (b := midConst k * (1 + t) ^ (5 * k))
            (mul_nonneg (midConst_nonneg k) (by positivity)) (4 * k) M
          have hcast : ((4 * k : ℕ) : ℝ) + 1 = 4 * (k : ℝ) + 1 := by push_cast; ring
          rw [hcast] at h
          exact h
  -- assemble the constant
  have hone : (1 : ℝ) ≤ (1 + t) ^ (4 * k) := one_le_pow₀ (by linarith)
  have hpart1 : (4 * (k : ℝ) + 1) * (midConst k * (1 + t) ^ (5 * k))
      ≤ (4 * (k : ℝ) + 1) * midConst k * Cexp * (1 + t) ^ (4 * k) * Real.exp t := by
    have h1 : (1 + t) ^ (5 * k) ≤ Cexp * Real.exp t := hCexp t ht0
    have h2 : (0 : ℝ) ≤ (4 * (k : ℝ) + 1) * midConst k := by
      have := midConst_nonneg k; positivity
    calc (4 * (k : ℝ) + 1) * (midConst k * (1 + t) ^ (5 * k))
        = ((4 * (k : ℝ) + 1) * midConst k) * (1 + t) ^ (5 * k) := by ring
      _ ≤ ((4 * (k : ℝ) + 1) * midConst k) * (Cexp * Real.exp t) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ ≤ (4 * (k : ℝ) + 1) * midConst k * Cexp * (1 + t) ^ (4 * k) * Real.exp t := by
          have hexp : (0 : ℝ) ≤ Real.exp t := (Real.exp_pos t).le
          have hCn : (0 : ℝ) ≤ ((4 * (k : ℝ) + 1) * midConst k) * Cexp := by positivity
          nlinarith [mul_nonneg hCn hexp]
  have hpart2 : G * Real.exp t
      ≤ 4 * ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k) * (1 + t) ^ (4 * k) * Real.exp t := by
    have hP1 : (1 : ℝ) ≤ (1 + t) ^ k := one_le_pow₀ (by linarith)
    have hPt : t ^ k ≤ (1 + t) ^ k := pow_le_pow_left₀ ht0 (by linarith) k
    have hs0 : (0 : ℝ) ≤ t ^ k := by positivity
    have hP4 : ((1 + t) ^ k) ^ 4 = (1 + t) ^ (4 * k) := by rw [← pow_mul, Nat.mul_comm]
    have hkey : (1 + t ^ k) ^ 2 * t ^ k ≤ 4 * (1 + t) ^ (4 * k) := by
      rw [← hP4]
      exact aux_cube hs0 hP1 hPt
    have hexp : (0 : ℝ) ≤ Real.exp t := (Real.exp_pos t).le
    have hc0 : (0 : ℝ) ≤ (((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k := by positivity
    have hG : G ≤ 4 * ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k) * (1 + t) ^ (4 * k) := by
      rw [hGdef]
      calc (((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k * (1 + t ^ k) ^ 2 * t ^ k
          = ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k) * ((1 + t ^ k) ^ 2 * t ^ k) := by ring
        _ ≤ ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k) * (4 * (1 + t) ^ (4 * k)) :=
            mul_le_mul_of_nonneg_left hkey hc0
        _ = 4 * ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k) * (1 + t) ^ (4 * k) := by ring
    exact mul_le_mul_of_nonneg_right hG hexp
  have hfinal : ∀ M : ℕ, ∑ m ∈ range M, ‖HermitePoly m k w‖ ^ 2
      ≤ ((4 * (k : ℝ) + 1) * midConst k * Cexp + 4 * ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k))
        * (1 + t) ^ (4 * k) * Real.exp t := by
    intro M
    calc ∑ m ∈ range M, ‖HermitePoly m k w‖ ^ 2
        ≤ (4 * (k : ℝ) + 1) * (midConst k * (1 + t) ^ (5 * k)) + G * Real.exp t := hstep M
      _ ≤ (4 * (k : ℝ) + 1) * midConst k * Cexp * (1 + t) ^ (4 * k) * Real.exp t
            + 4 * ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k) * (1 + t) ^ (4 * k) * Real.exp t :=
          add_le_add hpart1 hpart2
      _ = ((4 * (k : ℝ) + 1) * midConst k * Cexp + 4 * ((((k : ℝ) + 1) * 2 ^ k) ^ 2 * 4 ^ k))
            * (1 + t) ^ (4 * k) * Real.exp t := by ring
  exact ⟨summable_of_sum_range_le hf0 hfinal, Real.tsum_le_of_sum_range_le hf0 hfinal⟩

/-! ### Tensorisation -/

/-- A product of nonnegative summable series over the multi-indices `Fin d → ℕ`. -/
private lemma tsum_prod_le (f : Fin d → ℕ → ℝ) (B : Fin d → ℝ)
    (hf0 : ∀ i m, 0 ≤ f i m) (hfs : ∀ i, Summable (f i)) (hB : ∀ i, ∑' m, f i m ≤ B i) :
    Summable (fun α : Fin d → ℕ => ∏ i, f i (α i)) ∧
      ∑' α : Fin d → ℕ, ∏ i, f i (α i) ≤ ∏ i, B i := by
  have hnn : ∀ α : Fin d → ℕ, 0 ≤ ∏ i, f i (α i) :=
    fun α => Finset.prod_nonneg fun i _ => hf0 i (α i)
  have key : ∀ S : Finset (Fin d → ℕ), ∑ α ∈ S, ∏ i, f i (α i) ≤ ∏ i, B i := by
    intro S
    set M : ℕ := (S.sup fun α => ∑ i, α i) + 1 with hM
    have hsub : S ⊆ Fintype.piFinset (fun _ : Fin d => range M) := by
      intro α hα
      simp only [Fintype.mem_piFinset, Finset.mem_range]
      intro i
      have h1 : α i ≤ ∑ j, α j :=
        Finset.single_le_sum (f := fun j => α j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 : (∑ j, α j) ≤ S.sup fun α => ∑ i, α i := Finset.le_sup hα
      omega
    calc ∑ α ∈ S, ∏ i, f i (α i)
        ≤ ∑ α ∈ Fintype.piFinset (fun _ : Fin d => range M), ∏ i, f i (α i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun α _ _ => hnn α)
      _ = ∏ i, ∑ m ∈ range M, f i m := Finset.sum_prod_piFinset _ _
      _ ≤ ∏ i, B i := by
          refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun m _ => hf0 i m)
            (fun i _ => le_trans ?_ (hB i))
          exact (hfs i).sum_le_tsum _ (fun m _ => hf0 i m)
  exact ⟨summable_of_sum_le hnn key, Real.tsum_le_of_sum_le hnn key⟩

/-- The kernel bound in `d` variables:
`∑_α ‖Φ_{α,κ}(z)‖² ≤ C (1 + |z|²)^{4‖κ‖₁} e^{|z|²}`, and the series converges. -/
theorem kernel_bound (κ : Fin d → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin d → ℂ, Summable (fun α ↦ ‖Φ α κ z‖ ^ 2) ∧
      ∑' α, ‖Φ α κ z‖ ^ 2
        ≤ C * (1 + euclideanDist z 0 ^ 2) ^ (4 * ‖κ‖₁) * Real.exp (euclideanDist z 0 ^ 2) := by
  have H : ∀ i : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, Summable (fun m ↦ ‖HermitePoly m (κ i) w‖ ^ 2) ∧
      ∑' m, ‖HermitePoly m (κ i) w‖ ^ 2 ≤ C * (1 + ‖w‖ ^ 2) ^ (4 * κ i) * Real.exp (‖w‖ ^ 2) :=
    fun i => sum_sq_phi_le (κ i)
  choose C hC0 hC using H
  refine ⟨∏ i, C i, Finset.prod_nonneg fun i _ => hC0 i, fun z => ?_⟩
  set f : Fin d → ℕ → ℝ := fun i m => ‖HermitePoly m (κ i) (z i)‖ ^ 2 with hfdef
  set B : Fin d → ℝ := fun i => C i * (1 + ‖z i‖ ^ 2) ^ (4 * κ i) * Real.exp (‖z i‖ ^ 2) with hBdef
  have hf0 : ∀ i m, 0 ≤ f i m := fun i m => by rw [hfdef]; positivity
  have hfs : ∀ i, Summable (f i) := fun i => (hC i (z i)).1
  have hB : ∀ i, ∑' m, f i m ≤ B i := fun i => (hC i (z i)).2
  obtain ⟨hsum, hle⟩ := tsum_prod_le f B hf0 hfs hB
  have hnorm : ∀ α : Fin d → ℕ, ‖Φ α κ z‖ ^ 2 = ∏ i, f i (α i) := by
    intro α
    rw [Φ, norm_prod, ← Finset.prod_pow]
  -- transfer summability and the bound
  constructor
  · exact (funext (fun α => hnorm α) : (fun α => ‖Φ α κ z‖ ^ 2) = _) ▸ hsum
  · -- the product of the one-variable bounds
    have hs : euclideanDist z 0 ^ 2 = ∑ i, ‖z i‖ ^ 2 := euclideanDist_zero_sq z
    have hzi : ∀ i : Fin d, ‖z i‖ ^ 2 ≤ euclideanDist z 0 ^ 2 := by
      intro i
      rw [hs]
      exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)
    have hprod : ∏ i, B i
        ≤ (∏ i, C i) * (1 + euclideanDist z 0 ^ 2) ^ (4 * ‖κ‖₁)
            * Real.exp (euclideanDist z 0 ^ 2) := by
      have hstep : ∏ i, B i
          = (∏ i, C i) * (∏ i, (1 + ‖z i‖ ^ 2) ^ (4 * κ i)) * (∏ i, Real.exp (‖z i‖ ^ 2)) := by
        rw [hBdef]
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      have h1 : ∏ i, (1 + ‖z i‖ ^ 2) ^ (4 * κ i) ≤ (1 + euclideanDist z 0 ^ 2) ^ (4 * ‖κ‖₁) := by
        calc ∏ i, (1 + ‖z i‖ ^ 2) ^ (4 * κ i)
            ≤ ∏ i, (1 + euclideanDist z 0 ^ 2) ^ (4 * κ i) := by
              refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
              exact pow_le_pow_left₀ (by positivity) (by linarith [hzi i]) _
          _ = (1 + euclideanDist z 0 ^ 2) ^ (∑ i, 4 * κ i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ = (1 + euclideanDist z 0 ^ 2) ^ (4 * ‖κ‖₁) := by
              congr 1
              rw [size, Finset.mul_sum]
      have h2 : ∏ i, Real.exp (‖z i‖ ^ 2) = Real.exp (euclideanDist z 0 ^ 2) := by
        rw [hs, Real.exp_sum]
      have hC0' : (0 : ℝ) ≤ ∏ i, C i := Finset.prod_nonneg fun i _ => hC0 i
      have hp1 : (0 : ℝ) ≤ ∏ i, (1 + ‖z i‖ ^ 2) ^ (4 * κ i) :=
        Finset.prod_nonneg fun i _ => by positivity
      rw [hstep, h2]
      have hexp : (0 : ℝ) ≤ Real.exp (euclideanDist z 0 ^ 2) := (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left h1 hC0'
      nlinarith [mul_nonneg hC0' hp1]
    calc ∑' α, ‖Φ α κ z‖ ^ 2 = ∑' α : Fin d → ℕ, ∏ i, f i (α i) :=
          tsum_congr fun α => hnorm α
      _ ≤ ∏ i, B i := hle
      _ ≤ (∏ i, C i) * (1 + euclideanDist z 0 ^ 2) ^ (4 * ‖κ‖₁)
            * Real.exp (euclideanDist z 0 ^ 2) := hprod

theorem summable_Phi_sq (κ : Fin d → ℕ) (z : Fin d → ℂ) :
    Summable fun α ↦ ‖Φ α κ z‖ ^ 2 := by
  obtain ⟨C, _, h⟩ := kernel_bound κ
  exact (h z).1

/-! ### The mixed-level basis

Cauchy–Schwarz over the finitely many levels of `supp h` transfers the single-level estimates
to `Ψ_{α,h}`; the polynomial factor is then taken at the largest level `levelBound h`. -/

/-- Cauchy–Schwarz over the support: `‖Ψ_{α,h}(z)‖² ≤ ∑_{q ∈ supp h} ‖Φ_{α,q}(z)‖²`. -/
theorem sq_norm_Psi_le (α : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) (z : Fin d → ℂ) :
    ‖Ψ α h z‖ ^ 2 ≤ ∑ q ∈ h.support, ‖Φ α q z‖ ^ 2 := by
  classical
  set s : ℝ := ∑ q ∈ h.support, ‖h q‖ ^ 2 with hs
  set T : ℝ := ∑ q ∈ h.support, ‖Φ α q z‖ ^ 2
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  -- the numerator: `‖∑_q h_q Φ_{α,q}(z)‖² ≤ s · T`
  have hmix : ‖∑ q ∈ h.support, h q * Φ α q z‖ ^ 2 ≤ s * T := by
    have h1 : ‖∑ q ∈ h.support, h q * Φ α q z‖ ≤ ∑ q ∈ h.support, ‖h q‖ * ‖Φ α q z‖ :=
      (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun q _ ↦ norm_mul _ _)
    have h2 : (∑ q ∈ h.support, ‖h q‖ * ‖Φ α q z‖) ^ 2 ≤ s * T :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : (0 : ℝ) ≤ ∑ q ∈ h.support, ‖h q‖ * ‖Φ α q z‖ :=
      Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [norm_nonneg (∑ q ∈ h.support, h q * Φ α q z)]
  rcases eq_or_lt_of_le hs0 with hs00 | hspos
  · -- `h = 0` on its (empty) support: `Ψ` vanishes
    have hz : Real.sqrt s = 0 := by rw [← hs00, Real.sqrt_zero]
    rw [Ψ, ← hs, hz]
    simpa using hT0
  · have hinv : ‖((Real.sqrt s : ℝ) : ℂ)⁻¹‖ ^ 2 = s⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg s), ← Real.sqrt_inv,
        Real.sq_sqrt (by positivity)]
    rw [Ψ, ← hs, norm_mul, mul_pow, hinv]
    calc s⁻¹ * ‖∑ q ∈ h.support, h q * Φ α q z‖ ^ 2
        ≤ s⁻¹ * (s * T) := mul_le_mul_of_nonneg_left hmix (by positivity)
      _ = T := by field_simp

/-- W for the mixed-level basis: `∑_α ‖Ψ_{α,h}(z)‖²` converges. -/
theorem summable_Psi_sq (h : (Fin d → ℕ) →₀ ℂ) (z : Fin d → ℂ) :
    Summable fun α ↦ ‖Ψ α h z‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) (fun α ↦ sq_norm_Psi_le α h z)
    (summable_sum fun q _ ↦ summable_Phi_sq q z)

/-- K for the mixed-level basis: `∑_α ‖Ψ_{α,h}(z)‖² ≤ C (1 + |z|²)^{4L} e^{|z|²}`,
`L = levelBound h`. -/
theorem kernel_bound_mixed (h : (Fin d → ℕ) →₀ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin d → ℂ,
      ∑' α, ‖Ψ α h z‖ ^ 2
        ≤ C * (1 + euclideanDist z 0 ^ 2) ^ (4 * levelBound h)
            * Real.exp (euclideanDist z 0 ^ 2) := by
  classical
  choose C hC0 hC using fun q : Fin d → ℕ ↦ kernel_bound q
  refine ⟨∑ q ∈ h.support, C q, Finset.sum_nonneg fun q _ ↦ hC0 q, fun z ↦ ?_⟩
  set t : ℝ := euclideanDist z 0 ^ 2 with ht
  have ht0 : (0 : ℝ) ≤ t := by rw [ht]; positivity
  have hswap : ∑' α : Fin d → ℕ, ∑ q ∈ h.support, ‖Φ α q z‖ ^ 2
      = ∑ q ∈ h.support, ∑' α : Fin d → ℕ, ‖Φ α q z‖ ^ 2 :=
    Summable.tsum_finsetSum fun q _ ↦ summable_Phi_sq q z
  calc ∑' α, ‖Ψ α h z‖ ^ 2
      ≤ ∑' α : Fin d → ℕ, ∑ q ∈ h.support, ‖Φ α q z‖ ^ 2 :=
        (summable_Psi_sq h z).tsum_le_tsum (fun α ↦ sq_norm_Psi_le α h z)
          (summable_sum fun q _ ↦ summable_Phi_sq q z)
    _ = ∑ q ∈ h.support, ∑' α : Fin d → ℕ, ‖Φ α q z‖ ^ 2 := hswap
    _ ≤ ∑ q ∈ h.support, C q * (1 + t) ^ (4 * levelBound h) * Real.exp t := by
        refine Finset.sum_le_sum fun q hq ↦ ?_
        refine ((hC q z).2).trans ?_
        have hpow : (1 + t) ^ (4 * ‖q‖₁) ≤ (1 + t) ^ (4 * levelBound h) :=
          pow_le_pow_right₀ (by linarith) (by
            have := size_le_levelBound hq
            omega)
        have hexp : (0 : ℝ) ≤ Real.exp t := (Real.exp_pos t).le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (hC0 q)) hexp
    _ = (∑ q ∈ h.support, C q) * (1 + t) ^ (4 * levelBound h) * Real.exp t := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]

end DiscretePR
