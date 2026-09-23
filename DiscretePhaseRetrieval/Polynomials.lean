import DiscretePhaseRetrieval.Bridge

/-!
# Claims P1–P4: the finite-dimensional spaces `V_h^N`

* P1 `Φ_{α,q}` is a polynomial in `z, z̄` of degree `‖α‖₁ + ‖q‖₁`
  (`Hpoly i m n` has degree `≤ m + n`); hence `Ψ_{α,h}`, a combination of the `Φ_{α,q}` with
  `q ∈ supp h`, has degree `≤ ‖α‖₁ + L`, `L = levelBound h`.
* P2 `V_h^N` consists of polynomials of degree `≤ N + L`.
* P3 `1 ≤ dim V_h^N ≤ C(N+d, d)` (the number of multi-indices with `‖α‖₁ ≤ N` is `C(N+d, d)`,
  stars and bars).  The lower bound uses `h ≠ 0`: pairing `Ψ_{α,h}` with `Φ_{α,q₀}` for a level
  `q₀ ∈ supp h` under the Fock form returns `(hnorm h)⁻¹ h_{q₀} ≠ 0`, because the polynomial
  basis `Psihat` is orthonormal over **all** pairs `(n, q)` (`PolyFock.Fock.form_Psihat`).
* P4 `C(N+d, d) ≤ ((N+d) e / d)^d` (from `C(n,k) ≤ n^k/k!` and `k^k/k! ≤ e^k`).
-/

open MeasureTheory PolyFock PolyFock.Fock

namespace DiscretePR

variable {d : ℕ}

theorem mem_box {N : ℕ} {α : Fin d → ℕ} : α ∈ box d N ↔ ‖α‖₁ ≤ N := by
  classical
  rw [box, Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => Finset.mem_range.mpr ?_, h⟩⟩
  have hi : α i ≤ ∑ j, α j :=
    Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h' : ∑ j, α j ≤ N := h
  omega

/-! ### Stars and bars -/

/-- The hockey-stick identity in the form needed below. -/
private lemma sum_range_choose_add (k : ℕ) :
    ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), (j + k).choose k = (n + k + 1).choose (k + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, show n + 1 + k = n + k + 1 from by omega,
        Nat.choose_succ_succ (n + k + 1) k]
      simp only [Nat.succ_eq_add_one]
      omega

/-- `‖(k, α)‖₁ = k + ‖α‖₁` under `Fin.cons`. -/
private lemma deg_cons (k : ℕ) (α : Fin d → ℕ) :
    ‖(Fin.cons k α : Fin (d + 1) → ℕ)‖₁ = k + ‖α‖₁ := by
  simp [size, Fin.sum_univ_succ]

private lemma deg_eq_head_add_tail (β : Fin (d + 1) → ℕ) :
    ‖β‖₁ = β 0 + ‖Fin.tail β‖₁ := by
  simp [size, Fin.sum_univ_succ, Fin.tail]

/-- Splitting the box in `d+1` variables by the value of the first coordinate. -/
private lemma card_box_succ (d N : ℕ) :
    (box (d + 1) N).card = ∑ k ∈ Finset.range (N + 1), (box d (N - k)).card := by
  classical
  rw [← Finset.card_sigma]
  refine (Finset.card_bij' (s := (Finset.range (N + 1)).sigma fun k => box d (N - k))
    (t := box (d + 1) N) (fun x _ => Fin.cons x.1 x.2) (fun β _ => ⟨β 0, Fin.tail β⟩)
    ?_ ?_ ?_ ?_).symm
  · rintro ⟨k, α⟩ hx
    rw [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨hk, hα⟩ := hx
    rw [mem_box] at hα ⊢
    rw [deg_cons]
    omega
  · intro β hβ
    rw [mem_box] at hβ
    have hsplit := deg_eq_head_add_tail β
    simp only [Finset.mem_sigma, Finset.mem_range, mem_box]
    omega
  · rintro ⟨k, α⟩ _
    simp [Fin.tail_cons]
  · intro β _
    exact Fin.cons_self_tail β

/-- Stars and bars: `#{α : Fin d → ℕ | ‖α‖₁ ≤ N} = C(N+d, d)`. -/
theorem card_box (d N : ℕ) : (box d N).card = (N + d).choose d := by
  classical
  induction d generalizing N with
  | zero =>
      have h : box 0 N = {0} := by
        ext α
        simp only [Finset.mem_singleton, mem_box]
        exact ⟨fun _ => funext fun i => i.elim0, fun _ => by simp [size]⟩
      rw [h]
      simp
  | succ d ih =>
      rw [card_box_succ]
      have hstep : ∀ k ∈ Finset.range (N + 1), (box d (N - k)).card = (N - k + d).choose d :=
        fun k _ => ih (N - k)
      rw [Finset.sum_congr rfl hstep]
      have hrefl := Finset.sum_range_reflect (fun j => (j + d).choose d) (N + 1)
      simp only [Nat.add_sub_cancel] at hrefl
      rw [hrefl, sum_range_choose_add d N, show N + d + 1 = N + (d + 1) from by omega]

/-! ### P1: degrees -/

private lemma totalDegree_Hpoly_le (i : Fin d) (m n : ℕ) :
    (Hpoly i m n).totalDegree ≤ m + n := by
  rw [Hpoly]
  refine MvPolynomial.totalDegree_finsetSum_le fun r _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h1 : (MvPolynomial.C (cc m n r) *
      MvPolynomial.X (Sum.inl i) ^ (m - r) : P d).totalDegree ≤ m - r := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow]
    omega
  have h2 : ((MvPolynomial.X (Sum.inr i) : P d) ^ (n - r)).totalDegree ≤ n - r := by
    rw [MvPolynomial.totalDegree_X_pow]
  omega

private lemma totalDegree_Psi_le (α κ : Fin d → ℕ) :
    (Psi α κ).totalDegree ≤ ‖α‖₁ + ‖κ‖₁ := by
  rw [Psi]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  rw [size, size, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => totalDegree_Hpoly_le i (α i) (κ i)

/-- P1: `Φ_{α,κ}` has degree `≤ ‖α‖₁ + ‖κ‖₁` as a polynomial in `z, z̄`. -/
theorem totalDegree_Psihat_le (α κ : Fin d → ℕ) :
    (Psihat α κ).totalDegree ≤ ‖α‖₁ + ‖κ‖₁ := by
  rw [Psihat]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_Psi_le α κ

/-- P1 for the mixed-level basis: `Ψ_{α,h}` has degree `≤ ‖α‖₁ + levelBound h`. -/
theorem totalDegree_PsihatH_le (α : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) :
    (PsihatH α h).totalDegree ≤ ‖α‖₁ + levelBound h := by
  rw [PsihatH]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine MvPolynomial.totalDegree_finsetSum_le fun q hq ↦ ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (totalDegree_Psihat_le α q).trans
    (Nat.add_le_add_left (size_le_levelBound hq) _)

/-- P2: `V_h^N ⊆ Poly_{N+L}`, `L = levelBound h`. -/
theorem totalDegree_le_of_mem_VhN {h : (Fin d → ℕ) →₀ ℂ} {N : ℕ} {F : P d} (hF : F ∈ VhN h N) :
    F.totalDegree ≤ N + levelBound h := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨α, rfl⟩ := hx
      exact (totalDegree_PsihatH_le _ _).trans
        (Nat.add_le_add_right (mem_box.mp α.2) _)
  | zero => simp
  | add x y _ _ hx hy => exact (MvPolynomial.totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx => exact (MvPolynomial.totalDegree_smul_le c x).trans hx

/-! ### P3: the dimension -/

/-- Pairing `Ψ_{α,h}` with a single-level basis polynomial `Φ_{α,q₀}` under the Fock form.
`form_Psihat` is orthonormality over all pairs, so only the level `q₀` survives. -/
theorem form_PsihatH_Psihat (α : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) (q₀ : Fin d → ℕ) :
    form (PsihatH α h) (Psihat α q₀)
      = (hnorm h : ℂ)⁻¹ * (if q₀ ∈ h.support then h q₀ else 0) := by
  classical
  rw [PsihatH, ← MvPolynomial.smul_eq_C_mul _ ((hnorm h : ℂ)⁻¹), form_smul_left, form_sum_left,
    ← Finset.sum_ite_eq' h.support q₀ fun q ↦ h q]
  congr 1
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← MvPolynomial.smul_eq_C_mul _ (h q), form_smul_left, form_Psihat]
  by_cases hqq : q = q₀
  · subst hqq; simp
  · simp [hqq]

/-- For `h ≠ 0` the mixed-level basis polynomials are nonzero. -/
theorem PsihatH_ne_zero {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0) (α : Fin d → ℕ) :
    PsihatH α h ≠ 0 := by
  classical
  obtain ⟨q₀, hq₀⟩ := Finsupp.support_nonempty_iff.mpr hnonzero
  intro hPsi
  have h1 : form (PsihatH α h) (Psihat α q₀) = 0 := by rw [hPsi, form_zero_left]
  rw [form_PsihatH_Psihat, if_pos hq₀] at h1
  have hinv : ((hnorm h : ℂ))⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
    exact (hnorm_pos hnonzero).ne'
  exact (Finsupp.mem_support_iff.mp hq₀) ((mul_eq_zero.mp h1).resolve_left hinv)

instance instFiniteDimensionalVhN (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) :
    FiniteDimensional ℂ (VhN h N) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem one_le_finrank_VhN {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0) (N : ℕ) :
    1 ≤ Module.finrank ℂ (VhN h N) := by
  rw [Submodule.one_le_finrank_iff]
  intro hbot
  have hzero : (0 : Fin d → ℕ) ∈ box d N := mem_box.mpr (by simp [size])
  have hmem : PsihatH (0 : Fin d → ℕ) h ∈ VhN h N :=
    Submodule.subset_span ⟨⟨0, hzero⟩, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact PsihatH_ne_zero hnonzero 0 hmem

/-- P3: `dim V_h^N ≤ C(N+d, d)`. -/
theorem finrank_VhN_le (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) :
    Module.finrank ℂ (VhN h N) ≤ (N + d).choose d := by
  have hfr := finrank_range_le_card (R := ℂ)
    (fun α : (box d N : Finset (Fin d → ℕ)) => PsihatH (α : Fin d → ℕ) h)
  rw [Set.finrank] at hfr
  calc Module.finrank ℂ (VhN h N) ≤ Fintype.card (box d N : Finset (Fin d → ℕ)) := hfr
    _ = (box d N).card := Fintype.card_coe _
    _ = (N + d).choose d := card_box d N

/-! ### P4: the binomial bound -/

/-- P4: `C(N+d, d) ≤ ((N+d) e / d)^d` for `d ≥ 1`. -/
theorem choose_le_pow_mul_exp (N : ℕ) (hd : 0 < d) :
    ((N + d).choose d : ℝ) ≤ ((N + d : ℝ) * Real.exp 1 / d) ^ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hfac : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast d.factorial_pos
  have hdd : (0 : ℝ) < (d : ℝ) ^ d := pow_pos hdpos d
  have hA : (0 : ℝ) ≤ ((N : ℝ) + d) ^ d := by positivity
  -- `C(N+d, d) ≤ (N+d)^d / d!`
  have h1 : ((N + d).choose d : ℝ) ≤ ((N : ℝ) + d) ^ d / (d.factorial : ℝ) := by
    have := Nat.choose_le_pow_div (α := ℝ) d (N + d)
    push_cast at this
    exact this
  -- `d^d ≤ e^d · d!`
  have h2 : ((d : ℝ)) ^ d / (d.factorial : ℝ) ≤ Real.exp 1 ^ d := by
    rw [Real.exp_one_pow]
    exact Real.pow_div_factorial_le_exp (d : ℝ) hdpos.le d
  have h3 : ((d : ℝ)) ^ d ≤ Real.exp 1 ^ d * (d.factorial : ℝ) := by
    rw [div_le_iff₀ hfac] at h2
    exact h2
  refine h1.trans ?_
  have h4 : ((N : ℝ) + d) ^ d / (d.factorial : ℝ)
      ≤ ((N : ℝ) + d) ^ d * Real.exp 1 ^ d / ((d : ℝ) ^ d) := by
    rw [div_le_div_iff₀ hfac hdd]
    calc ((N : ℝ) + d) ^ d * (d : ℝ) ^ d
        ≤ ((N : ℝ) + d) ^ d * (Real.exp 1 ^ d * (d.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 hA
      _ = ((N : ℝ) + d) ^ d * Real.exp 1 ^ d * (d.factorial : ℝ) := by ring
  refine h4.trans_eq ?_
  rw [div_pow, mul_pow]

end DiscretePR
