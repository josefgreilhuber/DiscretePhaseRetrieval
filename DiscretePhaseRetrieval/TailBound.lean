import DiscretePhaseRetrieval.Coefficients

/-!
# Claims T, E1, E2: the truncation error

* T: Lemma 3.1 (`PolyFock.tail_bound`, proved) applied to `F − F_N`:
  `|F(z) − F_N(z)| ≤ ‖F‖ · ‖K_{L,N}(z,·)‖`.  For a single level `q`, `∑_{‖α‖₁>N} ‖Φ_{α,q}(z)‖²`
  is part of the sum defining `PolyFock.tailKernelDiag ‖q‖₁ N z`; for the mixed basis `Ψ · h`,
  Cauchy–Schwarz over `supp h` (`sq_norm_Psi_le`) sums these level tails, and each level obeys
  the single-level bound with the exponents taken at `L = levelBound h`
  (`tail_le_tailKernelDiag_mixed`, `tail_bound_mixed`, constant `tailConstH d h`).
* E1: `||z|² − |w|²| ≤ 2 max(|z|,|w|) |z − w|`.
* E2 (paper p. 6): for `|z| ≤ μ√N`,
  `||F(z)|² − |F_N(z)|²| ≤ C N^{c} e^{(μ²/2 + 1/2 + log μ) N} ‖F‖²`
  (kernel bound for `max(|F(z)|, |F_N(z)|)`, T for `|F(z) − F_N(z)|`, and
  `(eμ²)^{N/2} = e^{(1/2 + log μ) N}`).
-/

open MeasureTheory PolyFock PolyFock.Fock

namespace DiscretePR

variable {d : ℕ}

/-- The family defining `PolyFock.tailKernelDiag L N z` is summable: it is supported on the
finitely many `𝐪` with `‖𝐪‖₁ = L`, and for each such `𝐪` the series `∑_𝐧 ‖Φ_{𝐧,𝐪}(z)‖²`
converges (`summable_Phi_sq`). -/
theorem summable_tail_family (L N : ℕ) (z : Fin d → ℂ) :
    Summable fun p : (Fin d → ℕ) × (Fin d → ℕ) =>
      (if ‖p.2‖₁ = L ∧ N < ‖p.1‖₁ then ‖Φ p.1 p.2 z‖ ^ 2 else 0) := by
  classical
  have hmemQ : ∀ q : Fin d → ℕ, q ∈ Finset.Nat.antidiagonalTuple d L ↔ ∑ i, q i = L := by
    intro q; exact Finset.Nat.mem_antidiagonalTuple
  have hsum_n : ∀ q : Fin d → ℕ, Summable fun n : Fin d → ℕ => ‖Φ n q z‖ ^ 2 :=
    fun q => summable_Phi_sq q z
  rw [summable_prod_of_nonneg (fun p => by dsimp only; split <;> positivity)]
  refine ⟨fun n => ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := Finset.Nat.antidiagonalTuple d L) fun q hq => ?_
    rw [if_neg]
    rintro ⟨h1, -⟩
    exact hq ((hmemQ q).mpr h1)
  · have hre : ∀ n : Fin d → ℕ,
        (∑' q : Fin d → ℕ, if ‖q‖₁ = L ∧ N < ‖n‖₁ then ‖Φ n q z‖ ^ 2 else 0)
          = ∑ q ∈ Finset.Nat.antidiagonalTuple d L,
              (if ‖q‖₁ = L ∧ N < ‖n‖₁ then ‖Φ n q z‖ ^ 2 else 0) := by
      intro n
      refine tsum_eq_sum fun q hq => ?_
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hq ((hmemQ q).mpr h1)
    simp only [hre]
    refine summable_sum fun q _ => ?_
    refine Summable.of_nonneg_of_le (fun n => by split <;> positivity)
      (fun n => ?_) (hsum_n q)
    split
    · exact le_rfl
    · positivity

/-- The tail of the level-`κ` kernel is bounded by the tail kernel of `𝓕^d_{‖κ‖₁}`. -/
theorem tail_le_tailKernelDiag (κ : Fin d → ℕ) (N : ℕ) (z : Fin d → ℂ) :
    ∑' α, (if N < ‖α‖₁ then ‖Φ α κ z‖ ^ 2 else 0) ≤ tailKernelDiag (‖κ‖₁) N z := by
  classical
  have hinj : Function.Injective (fun α : Fin d → ℕ => (α, κ)) := fun a b h => congrArg Prod.fst h
  have hf : Summable fun α : Fin d → ℕ => (if N < ‖α‖₁ then ‖Φ α κ z‖ ^ 2 else 0) := by
    refine Summable.of_nonneg_of_le (fun α => by split <;> positivity) (fun α => ?_)
      (summable_Phi_sq κ z)
    split
    · exact le_rfl
    · positivity
  refine Summable.tsum_le_tsum_of_inj (fun α => (α, κ)) hinj (fun c _ => ?_) (fun α => ?_) hf
    (summable_tail_family (‖κ‖₁) N z)
  · split <;> positivity
  · simp only [true_and]
    exact le_rfl

/-! ### The mixed tail -/

/-- The tail of the mixed-level kernel is dominated by the level tails of `supp h`. -/
theorem tail_le_tailKernelDiag_mixed (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) (z : Fin d → ℂ) :
    ∑' α, (if N < ‖α‖₁ then ‖Ψ α h z‖ ^ 2 else 0)
      ≤ ∑ q ∈ h.support, tailKernelDiag (‖q‖₁) N z := by
  classical
  have hterm : ∀ q : Fin d → ℕ,
      Summable fun α : Fin d → ℕ => (if N < ‖α‖₁ then ‖Φ α q z‖ ^ 2 else 0) := by
    intro q
    refine Summable.of_nonneg_of_le (fun α => by split <;> positivity) (fun α => ?_)
      (summable_Phi_sq q z)
    split
    · exact le_rfl
    · positivity
  have hsumPsi : Summable fun α : Fin d → ℕ => (if N < ‖α‖₁ then ‖Ψ α h z‖ ^ 2 else 0) := by
    refine Summable.of_nonneg_of_le (fun α => by split <;> positivity) (fun α => ?_)
      (summable_Psi_sq h z)
    split
    · exact le_rfl
    · positivity
  calc ∑' α, (if N < ‖α‖₁ then ‖Ψ α h z‖ ^ 2 else 0)
      ≤ ∑' α : Fin d → ℕ, ∑ q ∈ h.support, (if N < ‖α‖₁ then ‖Φ α q z‖ ^ 2 else 0) := by
        refine hsumPsi.tsum_le_tsum (fun α => ?_) (summable_sum fun q _ => hterm q)
        by_cases hαN : N < ‖α‖₁
        · simp only [if_pos hαN]
          exact sq_norm_Psi_le α h z
        · simp [hαN]
    _ = ∑ q ∈ h.support, ∑' α : Fin d → ℕ, (if N < ‖α‖₁ then ‖Φ α q z‖ ^ 2 else 0) :=
        Summable.tsum_finsetSum fun q _ => hterm q
    _ ≤ ∑ q ∈ h.support, tailKernelDiag (‖q‖₁) N z :=
        Finset.sum_le_sum fun q _ => tail_le_tailKernelDiag q N z

/-- The constant of the mixed tail bound: the sum of the single-level constants over the
support of `h`. -/
noncomputable def tailConstH (d : ℕ) (h : (Fin d → ℕ) →₀ ℂ) : ℝ :=
  ∑ q ∈ h.support, tailConst d ‖q‖₁

theorem tailConstH_nonneg (d : ℕ) (h : (Fin d → ℕ) →₀ ℂ) : 0 ≤ tailConstH d h :=
  Finset.sum_nonneg fun _ _ => tailConst_nonneg d _

/-- Lemma 3.1 for the mixed-level basis: every level of `supp h` obeys the single-level bound
with the exponents taken at `L = levelBound h`. -/
theorem tail_bound_mixed (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) {N : ℕ}
    (hN3 : 3 * levelBound h ≤ N) (hN9 : levelBound h + 9 ≤ N) (z : Fin d → ℂ)
    (hz : Real.exp 1 * euclideanDist z 0 ^ 2 < N) :
    ∑ q ∈ h.support, tailKernelDiag (‖q‖₁) N z
      ≤ tailConstH d h * (N : ℝ) ^ levelBound h
          * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
            / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0
  set θ : ℝ := Real.exp 1 * euclideanDist z 0 ^ 2 / N with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθlt : θ < 1 := by rw [hθdef, div_lt_one hNpos]; exact hz
  have hden : (0 : ℝ) < 1 - θ := by linarith
  have hstep : ∀ q ∈ h.support, tailKernelDiag (‖q‖₁) N z
      ≤ tailConst d ‖q‖₁ * (N : ℝ) ^ levelBound h * θ ^ (N - 2 * levelBound h) / (1 - θ) := by
    intro q hq
    have hqL : ‖q‖₁ ≤ levelBound h := size_le_levelBound hq
    have h1 : tailKernelDiag (‖q‖₁) N z
        ≤ tailConst d ‖q‖₁ * (N : ℝ) ^ ‖q‖₁ * θ ^ (N - 2 * ‖q‖₁) / (1 - θ) :=
      tail_bound (by omega) (by omega) z hz
    refine h1.trans ?_
    have hC : (0 : ℝ) ≤ tailConst d ‖q‖₁ := tailConst_nonneg d _
    have hpowN : (N : ℝ) ^ ‖q‖₁ ≤ (N : ℝ) ^ levelBound h := pow_le_pow_right₀ hNR1 hqL
    have hpowθ : θ ^ (N - 2 * ‖q‖₁) ≤ θ ^ (N - 2 * levelBound h) :=
      pow_le_pow_of_le_one hθ0 hθlt.le (by omega)
    have hnum : tailConst d ‖q‖₁ * (N : ℝ) ^ ‖q‖₁ * θ ^ (N - 2 * ‖q‖₁)
        ≤ tailConst d ‖q‖₁ * (N : ℝ) ^ levelBound h * θ ^ (N - 2 * levelBound h) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpowN hC) hpowθ (pow_nonneg hθ0 _)
        (mul_nonneg hC (by positivity))
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc ∑ q ∈ h.support, tailKernelDiag (‖q‖₁) N z
      ≤ ∑ q ∈ h.support,
          tailConst d ‖q‖₁ * (N : ℝ) ^ levelBound h * θ ^ (N - 2 * levelBound h) / (1 - θ) :=
        Finset.sum_le_sum hstep
    _ = tailConstH d h * (N : ℝ) ^ levelBound h * θ ^ (N - 2 * levelBound h) / (1 - θ) := by
        rw [tailConstH, ← Finset.sum_div, ← Finset.sum_mul, ← Finset.sum_mul]

/-- T: Lemma 3.1 for `F − F_N`. -/
theorem truncation_error (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) {N : ℕ} (hN3 : 3 * levelBound h ≤ N)
    (hN9 : levelBound h + 9 ≤ N) (F : PolyFock d) (z : Fin d → ℂ)
    (hz : Real.exp 1 * euclideanDist z 0 ^ 2 < N) :
    ‖polyanalyticEval h F z - polyanalyticEval h (truncate N F) z‖
      ≤ ‖F‖ * Real.sqrt (tailConstH d h * (N : ℝ) ^ levelBound h
          * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
            / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hden : 0 < 1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N := by
    have : Real.exp 1 * euclideanDist z 0 ^ 2 / N < 1 := by rw [div_lt_one hNpos]; exact hz
    linarith
  set B : ℝ := tailConstH d h * (N : ℝ) ^ levelBound h
      * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
        / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    have := tailConstH_nonneg d h
    have h1 : (0:ℝ) ≤ (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h) := by
      positivity
    positivity
  have hsq : ‖polyanalyticEval h F z
      - polyanalyticEval h (truncate N F) z‖ ^ 2 ≤ ‖F‖ ^ 2 * B := by
    refine (tail_eval_le h N F z).trans ?_
    have h2 := (tail_le_tailKernelDiag_mixed h N z).trans (tail_bound_mixed hd h hN3 hN9 z hz)
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  exact norm_le_of_sq_le hsq (norm_nonneg _)

/-- E1. -/
theorem abs_sq_sub_sq_le (a b : ℂ) : |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * max ‖a‖ ‖b‖ * ‖a - b‖ := by
  have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h2 : ‖a‖ + ‖b‖ ≤ 2 * max ‖a‖ ‖b‖ := by
    rcases le_total ‖a‖ ‖b‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have key : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
  rw [key, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖a‖ + ‖b‖), mul_comm (2 * max ‖a‖ ‖b‖)]
  exact mul_le_mul h1 h2 (by positivity) (norm_nonneg _)

/-- E2: the modulus error of truncation on the ball `B_{μ√N}`. -/
theorem modulus_error (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) :
    ∃ C : ℝ, ∃ c : ℕ, 0 ≤ C ∧ ∀ N : ℕ, max (3 * levelBound h) (levelBound h + 9) ≤ N →
      ∀ (F : PolyFock d) (z : Fin d → ℂ), euclideanDist z 0 ≤ mu * Real.sqrt N →
        |‖polyanalyticEval h F z‖ ^ 2
            - ‖polyanalyticEval h (truncate N F) z‖ ^ 2|
          ≤ C * (N : ℝ) ^ c * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N) * ‖F‖ ^ 2 := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨C₀, hC₀, hK⟩ := kernel_bound_mixed h
  have hmu : mu = 1 / 100 := rfl
  have hmupos : (0 : ℝ) < mu := by rw [hmu]; norm_num
  have hmu1 : mu ^ 2 ≤ 1 := by rw [hmu]; norm_num
  have he9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hεpos : (0 : ℝ) < Real.exp 1 * mu ^ 2 := by positivity
  have hεhalf : Real.exp 1 * mu ^ 2 < 1 / 2 := by rw [hmu]; nlinarith
  have hA0 : (0 : ℝ) ≤ 2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h) := by
    have h0 := tailConstH_nonneg d h
    have h1 : (0 : ℝ) < (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h) := by positivity
    positivity
  refine ⟨2 * 2 ^ (2 * levelBound h) * Real.sqrt (2 * C₀ * tailConstH d h /
    (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)), 3 * levelBound h, by positivity, ?_⟩
  intro N hN F z hz
  have hN3 : 3 * levelBound h ≤ N := le_trans (le_max_left _ _) hN
  have hN9 : levelBound h + 9 ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hrad2 : euclideanDist z 0 ^ 2 ≤ mu ^ 2 * N := by
    have hp2 := pow_le_pow_left₀ (euclideanDist_zero_nonneg z) hz 2
    rwa [mul_pow, Real.sq_sqrt hNpos.le] at hp2
  have hθ0 : (0 : ℝ) ≤ Real.exp 1 * euclideanDist z 0 ^ 2 / N := by positivity
  have hθ : Real.exp 1 * euclideanDist z 0 ^ 2 / N ≤ Real.exp 1 * mu ^ 2 := by
    rw [div_le_iff₀ hNpos]
    nlinarith [Real.exp_pos 1]
  have hzlt : Real.exp 1 * euclideanDist z 0 ^ 2 < N := by
    have hθ' := hθ
    rw [div_le_iff₀ hNpos] at hθ'
    nlinarith
  have hKb0 : (0 : ℝ)
      ≤ C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) * Real.exp (mu ^ 2 * N) := by
    positivity
  have hKb : ∑' α, ‖Ψ α h z‖ ^ 2
      ≤ C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) * Real.exp (mu ^ 2 * N) := by
    refine (hK z).trans ?_
    have h1 : (1 : ℝ) + euclideanDist z 0 ^ 2 ≤ 1 + mu ^ 2 * N := by linarith
    have h2 : Real.exp (euclideanDist z 0 ^ 2) ≤ Real.exp (mu ^ 2 * N) := Real.exp_le_exp.mpr hrad2
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) h1 _) hC₀) h2 (Real.exp_pos _).le (by positivity)
  have hgen : ∀ G : PolyFock d, ‖G‖ ≤ ‖F‖ →
      ‖polyanalyticEval h G z‖
        ≤ ‖F‖ * Real.sqrt (C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h)
            * Real.exp (mu ^ 2 * N)) := by
    intro G hG
    have h1 : ‖polyanalyticEval h G z‖ ^ 2
        ≤ ‖F‖ ^ 2 * (C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) * Real.exp (mu ^ 2 * N)) := by
      refine (eval_le h G z).trans ?_
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg G) hG 2) hKb
        (tsum_nonneg fun _ => sq_nonneg _) (sq_nonneg _)
    exact norm_le_of_sq_le h1 (norm_nonneg _)
  have hmax : max ‖polyanalyticEval h F z‖
        ‖polyanalyticEval h (truncate N F) z‖
      ≤ ‖F‖ * Real.sqrt (C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h)
          * Real.exp (mu ^ 2 * N)) :=
    max_le (hgen F le_rfl) (hgen _ (norm_truncate_le N F))
  have hdiff := truncation_error hd h hN3 hN9 F z hzlt
  have hY0 : (0 : ℝ) ≤ tailConstH d h * (N : ℝ) ^ levelBound h *
      (Real.exp 1 * mu ^ 2) ^ (N - 2 * levelBound h) :=
    mul_nonneg (mul_nonneg (tailConstH_nonneg d h) (by positivity)) (by positivity)
  have hBle : tailConstH d h * (N : ℝ) ^ levelBound h
        * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
          / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)
      ≤ 2 * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h) *
          ((N : ℝ) ^ levelBound h * (Real.exp 1 * mu ^ 2) ^ N) := by
    have hpow : (Real.exp 1 * mu ^ 2) ^ (N - 2 * levelBound h)
          * (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)
        = (Real.exp 1 * mu ^ 2) ^ N := by
      rw [← pow_add]; congr 1; omega
    have hkey : 2 * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h) *
        ((N : ℝ) ^ levelBound h * (Real.exp 1 * mu ^ 2) ^ N)
        = 2 * (tailConstH d h * (N : ℝ) ^ levelBound h *
            (Real.exp 1 * mu ^ 2) ^ (N - 2 * levelBound h)) := by
      rw [← hpow]
      field_simp
    have h1 : tailConstH d h * (N : ℝ) ^ levelBound h
          * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
        ≤ tailConstH d h * (N : ℝ) ^ levelBound h
            * (Real.exp 1 * mu ^ 2) ^ (N - 2 * levelBound h) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ0 hθ _)
        (mul_nonneg (tailConstH_nonneg d h) (by positivity))
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N), hkey]
    nlinarith [mul_nonneg hY0
      (by linarith : (0 : ℝ) ≤ 1 - 2 * (Real.exp 1 * euclideanDist z 0 ^ 2 / N))]
  have hprod : (C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) * Real.exp (mu ^ 2 * N)) *
        (tailConstH d h * (N : ℝ) ^ levelBound h
          * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
            / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N))
      ≤ 2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h) *
          ((1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) *
            ((N : ℝ) ^ levelBound h * (Real.exp (mu ^ 2 * N) * (Real.exp 1 * mu ^ 2) ^ N))) := by
    refine (mul_le_mul_of_nonneg_left hBle hKb0).trans ?_
    apply le_of_eq
    field_simp
  have e1 : Real.sqrt ((1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h))
      = (1 + mu ^ 2 * (N : ℝ)) ^ (2 * levelBound h) := by
    rw [show 4 * levelBound h = 2 * levelBound h * 2 by ring, pow_mul, Real.sqrt_sq (by positivity)]
  have hlogε : Real.log (Real.exp 1 * mu ^ 2) = 1 + 2 * Real.log mu := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp, Real.log_pow]
    norm_num
  have hεN : (Real.exp 1 * mu ^ 2) ^ N = Real.exp ((1 + 2 * Real.log mu) * N) := by
    rw [mul_comm (1 + 2 * Real.log mu) (N : ℝ), Real.exp_nat_mul, ← hlogε, Real.exp_log hεpos]
  have e2 : Real.sqrt (Real.exp (mu ^ 2 * N) * (Real.exp 1 * mu ^ 2) ^ N)
      = Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N) := by
    rw [hεN, ← Real.exp_add,
      show mu ^ 2 * (N : ℝ) + (1 + 2 * Real.log mu) * N
        = (mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N + (mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N by ring,
      Real.exp_add]
    exact Real.sqrt_mul_self (Real.exp_nonneg _)
  have e3 : Real.sqrt ((N : ℝ) ^ levelBound h) ≤ (N : ℝ) ^ levelBound h := by
    have hNL1 : (1 : ℝ) ≤ (N : ℝ) ^ levelBound h := one_le_pow₀ hNR
    have h1 : (N : ℝ) ^ levelBound h ≤ ((N : ℝ) ^ levelBound h) ^ 2 := by nlinarith
    calc Real.sqrt ((N : ℝ) ^ levelBound h)
        ≤ Real.sqrt (((N : ℝ) ^ levelBound h) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (N : ℝ) ^ levelBound h := Real.sqrt_sq (by positivity)
  have e4 : (1 + mu ^ 2 * (N : ℝ)) ^ (2 * levelBound h)
      ≤ 2 ^ (2 * levelBound h) * (N : ℝ) ^ (2 * levelBound h) := by
    have h1 : 1 + mu ^ 2 * (N : ℝ) ≤ 2 * N := by nlinarith
    calc (1 + mu ^ 2 * (N : ℝ)) ^ (2 * levelBound h) ≤ (2 * (N : ℝ)) ^ (2 * levelBound h) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = 2 ^ (2 * levelBound h) * (N : ℝ) ^ (2 * levelBound h) := mul_pow 2 _ _
  have hsqrt : Real.sqrt ((C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h)
        * Real.exp (mu ^ 2 * N)) *
        (tailConstH d h * (N : ℝ) ^ levelBound h
          * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
            / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)))
      ≤ Real.sqrt (2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)) *
          ((1 + mu ^ 2 * (N : ℝ)) ^ (2 * levelBound h) *
            ((N : ℝ) ^ levelBound h * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N))) := by
    refine (Real.sqrt_le_sqrt hprod).trans ?_
    rw [Real.sqrt_mul hA0, Real.sqrt_mul (by positivity : (0 : ℝ) ≤
      (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h)),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ levelBound h), e1, e2]
    gcongr
  have hpowN : (N : ℝ) ^ (2 * levelBound h) * (N : ℝ) ^ levelBound h
      = (N : ℝ) ^ (3 * levelBound h) := by
    rw [← pow_add]; congr 1; ring
  have hfinal : 2 * Real.sqrt ((C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) *
        Real.exp (mu ^ 2 * N)) * (tailConstH d h * (N : ℝ) ^ levelBound h
          * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
            / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)))
      ≤ 2 * 2 ^ (2 * levelBound h) *
          Real.sqrt (2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)) *
          (N : ℝ) ^ (3 * levelBound h) * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N) := by
    have h5 : Real.sqrt (2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)) *
        ((1 + mu ^ 2 * (N : ℝ)) ^ (2 * levelBound h) *
          ((N : ℝ) ^ levelBound h * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N)))
        ≤ Real.sqrt (2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)) *
          ((2 ^ (2 * levelBound h) * (N : ℝ) ^ (2 * levelBound h)) *
            ((N : ℝ) ^ levelBound h * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N))) := by
      gcongr
    have h6 := hsqrt.trans h5
    calc 2 * Real.sqrt ((C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) * Real.exp (mu ^ 2 * N)) *
          (tailConstH d h * (N : ℝ) ^ levelBound h
            * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
              / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)))
        ≤ 2 * (Real.sqrt (2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)) *
            ((2 ^ (2 * levelBound h) * (N : ℝ) ^ (2 * levelBound h)) *
              ((N : ℝ) ^ levelBound h * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N)))) := by
          linarith
      _ = 2 * 2 ^ (2 * levelBound h) *
            Real.sqrt (2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)) *
            ((N : ℝ) ^ (2 * levelBound h) * (N : ℝ) ^ levelBound h) *
            Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N) := by ring
      _ = 2 * 2 ^ (2 * levelBound h) *
            Real.sqrt (2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)) *
            (N : ℝ) ^ (3 * levelBound h) *
            Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N) := by rw [hpowN]
  calc |‖polyanalyticEval h F z‖ ^ 2
          - ‖polyanalyticEval h (truncate N F) z‖ ^ 2|
      ≤ 2 * max ‖polyanalyticEval h F z‖
            ‖polyanalyticEval h (truncate N F) z‖ *
          ‖polyanalyticEval h F z - polyanalyticEval h (truncate N F) z‖ :=
        abs_sq_sub_sq_le _ _
    _ ≤ 2 * (‖F‖ * Real.sqrt (C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) *
            Real.exp (mu ^ 2 * N))) *
          (‖F‖ * Real.sqrt (tailConstH d h * (N : ℝ) ^ levelBound h
            * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
              / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N))) := by
        gcongr
    _ = (2 * (Real.sqrt (C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) * Real.exp (mu ^ 2 * N)) *
            Real.sqrt (tailConstH d h * (N : ℝ) ^ levelBound h
              * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
                / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)))) * ‖F‖ ^ 2 := by ring
    _ = (2 * Real.sqrt ((C₀ * (1 + mu ^ 2 * (N : ℝ)) ^ (4 * levelBound h) * Real.exp (mu ^ 2 * N)) *
            (tailConstH d h * (N : ℝ) ^ levelBound h
              * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
                / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)))) * ‖F‖ ^ 2 := by
        rw [Real.sqrt_mul hKb0]
    _ ≤ (2 * 2 ^ (2 * levelBound h) *
            Real.sqrt (2 * C₀ * tailConstH d h / (Real.exp 1 * mu ^ 2) ^ (2 * levelBound h)) *
            (N : ℝ) ^ (3 * levelBound h) *
            Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N)) * ‖F‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hfinal (sq_nonneg _)

end DiscretePR
