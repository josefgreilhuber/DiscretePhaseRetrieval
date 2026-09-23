import VCInequality.Defs

/-!
# Hoeffding's inequality for a Rademacher sum

Under uniform random signs `σ : Fin m → Bool`, the sum `∑ i, ± d i` (sign `−` where `σ i = true`)
exceeds `ε √(m T / 2)` with probability at most `exp(−m ε² / 4)` whenever `∑ (d i)² ≤ T`.

Mathlib input: `uniformOn_pi`, `iIndepFun_pi`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`,
`HasSubgaussianMGF.zero`, `measure_sum_ge_le_of_iIndepFun`, `uniformOn_apply_finset`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace VCInequality

/-- `signMeasure m` is uniform: the measure of a set is its cardinality over `2^m`. -/
theorem signMeasure_real_eq (m : ℕ) (S : Set (Fin m → Bool)) :
    (signMeasure m).real S = (∑ σ : Fin m → Bool, S.indicator (fun _ ↦ (1 : ℝ)) σ) / 2 ^ m := by
  classical
  set s : Finset (Fin m → Bool) := univ.filter (fun σ ↦ σ ∈ S) with hs
  have hSs : S = (s : Set (Fin m → Bool)) := by ext σ; simp [hs]
  have hsum : (∑ σ : Fin m → Bool, S.indicator (fun _ ↦ (1 : ℝ)) σ) = (#s : ℝ) := by
    simp [Set.indicator_apply, hs]
  have hcard : (Fintype.card (Fin m → Bool) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ m := by simp
  have hmeas : (signMeasure m) S = (#s : ℝ≥0∞) / (2 : ℝ≥0∞) ^ m := by
    change uniformOn Set.univ S = _
    rw [uniformOn_univ, hSs, Measure.count_apply_finset, hcard]
  rw [measureReal_def, hmeas, hsum, ENNReal.toReal_div]
  simp

/-! ### Auxiliary facts about a single uniform sign -/

/-- Each of the two signs has probability `1 / 2`. -/
private lemma uniformOn_bool_real_singleton (b : Bool) :
    (uniformOn (Set.univ : Set Bool)).real {b} = 1 / 2 := by
  rw [measureReal_def, uniformOn_univ, Measure.count_singleton, Fintype.card_bool,
    ENNReal.toReal_div]
  norm_num

/-- A single Rademacher variable `±a` has mean zero. -/
private lemma bool_integral_eq_zero (a : ℝ) :
    ∫ b : Bool, (if b then -a else a) ∂(uniformOn (Set.univ : Set Bool)) = 0 := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool, uniformOn_bool_real_singleton,
    uniformOn_bool_real_singleton]
  norm_num

/-- Hoeffding's lemma for a single Rademacher variable: `±a` is sub-Gaussian with parameter
`a ^ 2`. -/
private lemma bool_subgaussian (a : ℝ) :
    HasSubgaussianMGF (fun b : Bool ↦ if b then -a else a)
      (‖a‖₊ ^ 2) (uniformOn (Set.univ : Set Bool)) := by
  have hIcc : ∀ᵐ b ∂(uniformOn (Set.univ : Set Bool)),
      (if b then -a else a) ∈ Set.Icc (-|a|) |a| := by
    refine ae_of_all _ fun b ↦ ?_
    cases b <;> simp [le_abs_self, neg_le_abs, neg_abs_le]
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fun b : Bool ↦ if b then -a else a) (μ := uniformOn (Set.univ : Set Bool))
    (a := -|a|) (b := |a|) (Measurable.of_discrete).aemeasurable hIcc (bool_integral_eq_zero a)
  have hc : ((‖|a| - -|a|‖₊ / 2 : ℝ≥0)) ^ 2 = ‖a‖₊ ^ 2 := by
    refine NNReal.coe_injective ?_
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    rw [show |a| - -|a| = 2 * |a| by ring, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * |a|)]
    norm_num
  rwa [hc] at h

/-- `signMeasure m` is the `m`-fold product of the uniform measure on `Bool`. -/
private lemma signMeasure_eq_pi (m : ℕ) :
    signMeasure m = Measure.pi (fun _ : Fin m ↦ uniformOn (Set.univ : Set Bool)) := by
  have h := uniformOn_pi (ι := Fin m) (Ω := Bool) (f := fun _ ↦ (Set.univ : Set Bool))
  rwa [Set.pi_univ] at h

/-- Hoeffding for a Rademacher sum: `P[∑ ± d i > ε √(m T / 2)] ≤ exp(−m ε² / 4)` if `∑ d i² ≤ T`. -/
theorem rademacher_tail (m : ℕ) (d : Fin m → ℝ) {T : ℝ} (hT : ∑ i, (d i) ^ 2 ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    (signMeasure m).real
        {σ | ε * Real.sqrt (m * T / 2) < ∑ i, (if σ i then -(d i) else d i)}
      ≤ Real.exp (-(m * ε ^ 2) / 4) := by
  classical
  have hC0 : (0 : ℝ) ≤ ∑ i, (d i) ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hT0 : (0 : ℝ) ≤ T := le_trans hC0 hT
  set t : ℝ := ε * Real.sqrt (m * T / 2) with ht
  have ht0 : 0 ≤ t := mul_nonneg hε.le (Real.sqrt_nonneg _)
  by_cases hC : ∑ i, (d i) ^ 2 = 0
  · -- Degenerate case: every `d i` vanishes, so the event is empty.
    have hd : ∀ i, d i = 0 := by
      intro i
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (d i))).1 hC i (mem_univ i)
      exact sq_eq_zero_iff.1 h
    have hset : {σ : Fin m → Bool | t < ∑ i, (if σ i then -(d i) else d i)} = ∅ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have hz : ∑ i, (if σ i then -(d i) else d i) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by simp [hd i]
      rw [hz]; exact ht0
    rw [hset, measureReal_empty]
    positivity
  · have hCpos : 0 < ∑ i, (d i) ^ 2 := lt_of_le_of_ne hC0 (Ne.symm hC)
    have hpi := signMeasure_eq_pi m
    -- The coordinates are independent under the product measure.
    have hindep : iIndepFun (fun (i : Fin m) (σ : Fin m → Bool) ↦ if σ i then -(d i) else d i)
        (signMeasure m) := by
      rw [hpi]
      exact iIndepFun_pi (X := fun (i : Fin m) (b : Bool) ↦ if b then -(d i) else d i)
        (fun _ ↦ (Measurable.of_discrete).aemeasurable)
    -- Each summand is sub-Gaussian with parameter `(d i) ^ 2`.
    have hsubg : ∀ i ∈ (univ : Finset (Fin m)),
        HasSubgaussianMGF (fun σ : Fin m → Bool ↦ if σ i then -(d i) else d i)
          (‖d i‖₊ ^ 2) (signMeasure m) := by
      intro i _
      have hmap : (signMeasure m).map (fun σ : Fin m → Bool ↦ σ i)
          = uniformOn (Set.univ : Set Bool) := by
        rw [hpi]; exact (measurePreserving_eval _ i).map_eq
      exact HasSubgaussianMGF.of_map (Y := fun σ : Fin m → Bool ↦ σ i)
        (X := fun b : Bool ↦ if b then -(d i) else d i)
        (c := ‖d i‖₊ ^ 2) (μ := signMeasure m)
        (measurable_pi_apply i).aemeasurable (by rw [hmap]; exact bool_subgaussian (d i))
    have hHoeff := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (s := (univ : Finset (Fin m))) (c := fun i ↦ ‖d i‖₊ ^ 2) hindep hsubg ht0
    have hmono : (signMeasure m).real
        {σ : Fin m → Bool | t < ∑ i, (if σ i then -(d i) else d i)}
        ≤ (signMeasure m).real
          {σ : Fin m → Bool | t ≤ ∑ i, (if σ i then -(d i) else d i)} :=
      measureReal_mono (Set.setOf_subset_setOf.2 fun σ hσ ↦ hσ.le)
    refine hmono.trans (hHoeff.trans ?_)
    rw [Real.exp_le_exp]
    have hcs : ((∑ i : Fin m, ‖d i‖₊ ^ 2 : ℝ≥0) : ℝ) = ∑ i, (d i) ^ 2 := by
      push_cast
      simp [Real.norm_eq_abs, sq_abs]
    rw [hcs]
    have hts : t ^ 2 = ε ^ 2 * (m * T / 2) := by
      rw [ht, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hts, neg_div, neg_div]
    have key : (m * ε ^ 2) / 4 ≤ (ε ^ 2 * (m * T / 2)) / (2 * ∑ i, (d i) ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) (sq_nonneg ε))
        (sub_nonneg.2 hT)]
    linarith

end VCInequality
