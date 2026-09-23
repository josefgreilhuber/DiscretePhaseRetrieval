import DiscretePhaseRetrieval.Bridge
import DiscretePhaseRetrieval.KernelBound
import DiscretePhaseRetrieval.Polynomials

/-!
# Claims W and L1: the coefficient model

`PolyFock d = ℓ²(ℕ^d)`. With `∑_α ‖Ψ_{α,h}(z)‖² < ∞` (`summable_Psi_sq`), Cauchy–Schwarz gives
absolute convergence of `polyanalyticEval h F z = ∑_α F_α Ψ_{α,h}(z)`, the bound
`|F(z)|² ≤ ‖F‖² ∑_α ‖Ψ_{α,h}(z)‖²`, the tail bound for `F − F_N`, and `F_N(z) → F(z)`.
Also the basic facts on `truncate` (`F_N`) and `truncPoly` (`F_N` as an element of `V_h^N`).
-/

open MeasureTheory PolyFock PolyFock.Fock Filter Topology
open scoped ENNReal

namespace DiscretePR

variable {d : ℕ}

/-! ### Auxiliary facts -/

/-- Cauchy–Schwarz for infinite sums of complex numbers. -/
private theorem tsum_mul_sq_le {ι : Type*} (a b : ι → ℂ) (ha : Summable fun i ↦ ‖a i‖ ^ 2)
    (hb : Summable fun i ↦ ‖b i‖ ^ 2) (hab : Summable fun i ↦ a i * b i) :
    ‖∑' i, a i * b i‖ ^ 2 ≤ (∑' i, ‖a i‖ ^ 2) * ∑' i, ‖b i‖ ^ 2 := by
  have hfin : ∀ s : Finset ι, ‖∑ i ∈ s, a i * b i‖ ^ 2
      ≤ (∑' i, ‖a i‖ ^ 2) * ∑' i, ‖b i‖ ^ 2 := by
    intro s
    have h1 : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
      refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ ↦ norm_mul _ _)
    have h2 : (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2
        ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    have h3 : (∑ i ∈ s, ‖a i‖ ^ 2) ≤ ∑' i, ‖a i‖ ^ 2 :=
      ha.sum_le_tsum s (fun i _ ↦ sq_nonneg _)
    have h4 : (∑ i ∈ s, ‖b i‖ ^ 2) ≤ ∑' i, ‖b i‖ ^ 2 :=
      hb.sum_le_tsum s (fun i _ ↦ sq_nonneg _)
    have h5 : ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 := by
      have := norm_nonneg (∑ i ∈ s, a i * b i)
      nlinarith
    have h6 : (0:ℝ) ≤ ∑ i ∈ s, ‖b i‖ ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    have h7 : (0:ℝ) ≤ ∑ i ∈ s, ‖a i‖ ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    nlinarith
  have htend : Tendsto (fun s : Finset ι ↦ ‖∑ i ∈ s, a i * b i‖ ^ 2) atTop
      (𝓝 (‖∑' i, a i * b i‖ ^ 2)) := by
    have hcont : Continuous fun x : ℂ ↦ ‖x‖ ^ 2 := by fun_prop
    exact (hcont.tendsto _).comp hab.hasSum
  exact le_of_tendsto htend (Filter.Eventually.of_forall hfin)

/-! ### The `ℓ²` norm -/

theorem norm_sq_eq_tsum (F : PolyFock d) : ‖F‖ ^ 2 = ∑' α, ‖F α‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp F
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at h
  simpa only [Real.rpow_natCast] using h

theorem summable_norm_sq (F : PolyFock d) : Summable fun α ↦ ‖F α‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h := (lp.memℓp F).summable hp
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at h
  simpa only [Real.rpow_natCast] using h

/-! ### Convergence of the evaluation series -/

/-- W: the evaluation series converges absolutely. -/
theorem summable_eval (h : (Fin d → ℕ) →₀ ℂ) (F : PolyFock d) (z : Fin d → ℂ) :
    Summable fun α ↦ coeff F α * Ψ α h z := by
  refine Summable.of_norm_bounded
    (g := fun α ↦ (‖F α‖ ^ 2 + ‖Ψ α h z‖ ^ 2) / 2)
    (((summable_norm_sq F).add (summable_Psi_sq h z)).div_const 2) fun α ↦ ?_
  rw [coeff, norm_mul]
  nlinarith [sq_nonneg (‖F α‖ - ‖Ψ α h z‖)]

/-- Cauchy–Schwarz: `|F(z)|² ≤ ‖F‖² ∑_α ‖Ψ_{α,h}(z)‖²`. -/
theorem eval_le (h : (Fin d → ℕ) →₀ ℂ) (F : PolyFock d) (z : Fin d → ℂ) :
    ‖polyanalyticEval h F z‖ ^ 2 ≤ ‖F‖ ^ 2 * ∑' α, ‖Ψ α h z‖ ^ 2 := by
  rw [polyanalyticEval, norm_sq_eq_tsum]
  exact tsum_mul_sq_le _ _ (summable_norm_sq F) (summable_Psi_sq h z) (summable_eval h F z)

/-! ### Truncation -/

theorem truncate_apply (N : ℕ) (F : PolyFock d) (α : Fin d → ℕ) :
    truncate N F α = if ‖α‖₁ ≤ N then F α else 0 := by
  rw [truncate, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single, Pi.single_apply]
  rw [Finset.sum_ite_eq (box d N) α fun β ↦ F β]
  simp only [mem_box]

theorem norm_truncate_le (N : ℕ) (F : PolyFock d) : ‖truncate N F‖ ≤ ‖F‖ := by
  have hsq : ‖truncate N F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    have hcongr : ∀ α : Fin d → ℕ,
        ‖truncate N F α‖ ^ 2 = if ‖α‖₁ ≤ N then ‖F α‖ ^ 2 else 0 := by
      intro α
      rw [truncate_apply]
      split <;> simp
    rw [tsum_congr hcongr, tsum_eq_sum (s := box d N) ?_]
    · rw [Finset.sum_congr rfl fun α hα ↦ if_pos (mem_box.1 hα)]
      exact (summable_norm_sq F).sum_le_tsum _ fun α _ ↦ sq_nonneg _
    · intro β hβ
      exact if_neg fun h ↦ hβ (mem_box.2 h)
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- `F_N` is the finite sum of the terms of the series with `‖α‖₁ ≤ N`. -/
theorem eval_truncate_eq_sum (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) (F : PolyFock d) (z : Fin d → ℂ) :
    polyanalyticEval h (truncate N F) z = ∑ α ∈ box d N, coeff F α * Ψ α h z := by
  rw [polyanalyticEval]
  have hcongr : ∀ α : Fin d → ℕ,
      coeff (truncate N F) α * Ψ α h z
        = if ‖α‖₁ ≤ N then coeff F α * Ψ α h z else 0 := by
    intro α
    simp only [coeff, truncate_apply]
    split <;> simp
  rw [tsum_congr hcongr, tsum_eq_sum (s := box d N) fun β hβ ↦ if_neg fun hb ↦
    hβ (mem_box.2 hb)]
  exact Finset.sum_congr rfl fun α hα ↦ if_pos (mem_box.1 hα)

/-- `F_N` is the evaluation of the polynomial `truncPoly h N F ∈ ℂ[z, z̄]`. -/
theorem eval_truncate (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) (F : PolyFock d) (z : Fin d → ℂ) :
    polyanalyticEval h (truncate N F) z = ev z (truncPoly h N F) := by
  rw [eval_truncate_eq_sum, truncPoly, map_sum]
  exact Finset.sum_congr rfl fun α _ ↦ by
    rw [map_mul, ev_C, coeff, Psi_eq_ev]

theorem truncPoly_mem (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) (F : PolyFock d) :
    truncPoly h N F ∈ VhN h N := by
  refine Submodule.sum_mem _ fun α hα ↦ ?_
  rw [← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨α, hα⟩, rfl⟩)

/-! ### The tail -/

/-- The tail of the series: `|F(z) − F_N(z)|² ≤ ‖F‖² ∑_{‖α‖₁>N} ‖Ψ_{α,h}(z)‖²`. -/
theorem tail_eval_le (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) (F : PolyFock d) (z : Fin d → ℂ) :
    ‖polyanalyticEval h F z - polyanalyticEval h (truncate N F) z‖ ^ 2
      ≤ ‖F‖ ^ 2 * ∑' α, (if N < ‖α‖₁ then ‖Ψ α h z‖ ^ 2 else 0) := by
  set a : (Fin d → ℕ) → ℂ := fun α ↦ if N < ‖α‖₁ then F α else 0 with ha_def
  set b : (Fin d → ℕ) → ℂ := fun α ↦ if N < ‖α‖₁ then Ψ α h z else 0 with hb_def
  have hprod : ∀ α : Fin d → ℕ, a α * b α
      = coeff F α * Ψ α h z
        - coeff (truncate N F) α * Ψ α h z := by
    intro α
    simp only [ha_def, hb_def, coeff, truncate_apply]
    by_cases hαN : ‖α‖₁ ≤ N
    · simp only [if_neg (by omega : ¬ N < ‖α‖₁), if_pos hαN, zero_mul, sub_self]
    · simp only [if_pos (by omega : N < ‖α‖₁), if_neg hαN, zero_mul, sub_zero]
  have hab : Summable fun α ↦ a α * b α := by
    refine ((summable_eval h F z).sub (summable_eval h (truncate N F) z)).congr fun α ↦ ?_
    exact (hprod α).symm
  have hna : ∀ α : Fin d → ℕ, ‖a α‖ ^ 2 = if N < ‖α‖₁ then ‖F α‖ ^ 2 else 0 := by
    intro α; simp only [ha_def]; split <;> simp
  have hnb : ∀ α : Fin d → ℕ,
      ‖b α‖ ^ 2 = if N < ‖α‖₁ then ‖Ψ α h z‖ ^ 2 else 0 := by
    intro α; simp only [hb_def]; split <;> simp
  have hsa : Summable fun α ↦ ‖a α‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun α ↦ sq_nonneg _) (fun α ↦ ?_) (summable_norm_sq F)
    rw [hna α]; split <;> [rfl; positivity]
  have hsb : Summable fun α ↦ ‖b α‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun α ↦ sq_nonneg _) (fun α ↦ ?_) (summable_Psi_sq h z)
    rw [hnb α]; split <;> [rfl; positivity]
  have hCS := tsum_mul_sq_le a b hsa hsb hab
  have hdiff : polyanalyticEval h F z
      - polyanalyticEval h (truncate N F) z = ∑' α, a α * b α := by
    rw [polyanalyticEval, polyanalyticEval,
      ← Summable.tsum_sub (summable_eval h F z) (summable_eval h (truncate N F) z)]
    exact (tsum_congr hprod).symm
  have hle : (∑' α, ‖a α‖ ^ 2) ≤ ‖F‖ ^ 2 := by
    rw [norm_sq_eq_tsum]
    refine hsa.tsum_le_tsum (fun α ↦ ?_) (summable_norm_sq F)
    rw [hna α]; split
    · rfl
    · positivity
  have hbnonneg : (0:ℝ) ≤ ∑' α, ‖b α‖ ^ 2 := tsum_nonneg fun α ↦ sq_nonneg _
  rw [hdiff]
  calc ‖∑' α, a α * b α‖ ^ 2 ≤ (∑' α, ‖a α‖ ^ 2) * ∑' α, ‖b α‖ ^ 2 := hCS
    _ ≤ ‖F‖ ^ 2 * ∑' α, ‖b α‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hle hbnonneg
    _ = ‖F‖ ^ 2 * ∑' α, (if N < ‖α‖₁ then ‖Ψ α h z‖ ^ 2 else 0) := by
        rw [tsum_congr hnb]

/-! ### The limit -/

/-- L1: `F_N(z) → F(z)` as `N → ∞`. -/
theorem tendsto_truncate (h : (Fin d → ℕ) →₀ ℂ) (F : PolyFock d) (z : Fin d → ℂ) :
    Tendsto (fun N ↦ polyanalyticEval h (truncate N F) z) atTop
      (𝓝 (polyanalyticEval h F z)) := by
  have hmono : Monotone (box d) := by
    intro M N hMN α hα
    exact mem_box.2 ((mem_box.1 hα).trans hMN)
  have hcof : ∀ α : Fin d → ℕ, ∃ N, α ∈ box d N := fun α ↦ ⟨‖α‖₁, mem_box.2 le_rfl⟩
  have hbox : Tendsto (box d) atTop atTop := tendsto_atTop_finset_of_monotone hmono hcof
  have hsum := (summable_eval h F z).hasSum
  have hpe : polyanalyticEval h F z
      = ∑' α, coeff F α * Ψ α h z := rfl
  rw [hpe]
  simpa only [eval_truncate_eq_sum, Function.comp_def] using hsum.comp hbox

end DiscretePR
