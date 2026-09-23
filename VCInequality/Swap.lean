import VCInequality.Defs

/-!
# Coordinate swaps of the double sample

* `swap σ` preserves `doubleMeasure μ m = (μ ⊗ μ)^{⊗ m}` (`measurePreserving_pi` + `Measure.prod_swap`).
* Averaging identity: the measure of a measurable event is the integral of its average over all
  `2^m` swaps, hence is bounded by any pointwise bound on that average.
* The two representations of the double sample, `(Fin m → X) × (Fin m → X)` with
  `(sampleMeasure μ m).prod (sampleMeasure μ m)` and `Fin m → X × X` with `doubleMeasure μ m`,
  are identified by `MeasureTheory.measurePreserving_arrowProdEquivProdArrow`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace VCInequality

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {m : ℕ}

theorem measurable_swap (σ : Fin m → Bool) : Measurable (swap (X := X) σ) := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  unfold swap
  by_cases h : σ i <;> simp only [h, if_true, if_false, Bool.false_eq_true]
  · exact _root_.measurable_swap.comp (measurable_pi_apply i)
  · exact measurable_pi_apply i

theorem measurePreserving_swap (σ : Fin m → Bool) :
    MeasurePreserving (swap σ) (doubleMeasure μ m) (doubleMeasure μ m) := by
  have h : ∀ i : Fin m, MeasurePreserving (if σ i then (Prod.swap : X × X → X × X) else id)
      (μ.prod μ) (μ.prod μ) := by
    intro i
    by_cases hi : σ i <;> simp only [hi, if_true, if_false, Bool.false_eq_true]
    · exact Measure.measurePreserving_swap
    · exact MeasurePreserving.id _
  have hpi := MeasureTheory.measurePreserving_pi (fun _ : Fin m ↦ μ.prod μ)
      (fun _ : Fin m ↦ μ.prod μ) h
  convert hpi using 1
  funext z i
  simp only [swap]
  by_cases hi : σ i <;> simp [hi]

/-- The double-sample measure is the pushforward of the product of two sample measures under
`z ↦ (fstSample z, sndSample z)`, and conversely. -/
theorem prod_sampleMeasure_eq_map :
    (sampleMeasure μ m).prod (sampleMeasure μ m)
      = (doubleMeasure μ m).map (fun z ↦ (fstSample z, sndSample z)) := by
  have h := MeasureTheory.measurePreserving_arrowProdEquivProdArrow X X (Fin m)
      (fun _ ↦ μ) (fun _ ↦ μ)
  rw [← h.map_eq]
  rfl

/-- Averaging over swaps: if the average over all `σ` of the indicator of `E` at `swap σ z` is
at most `K` for every `z`, then `E` has measure at most `K`. -/
theorem doubleMeasure_real_le_of_swap_avg {E : Set (Fin m → X × X)} (hE : MeasurableSet E)
    {K : ℝ}
    (h : ∀ z, (∑ σ : Fin m → Bool, E.indicator (fun _ ↦ (1 : ℝ)) (swap σ z)) / 2 ^ m ≤ K) :
    (doubleMeasure μ m).real E ≤ K := by
  set π := doubleMeasure μ m with hπ
  have hmeas : ∀ σ : Fin m → Bool, MeasurableSet (swap (X := X) σ ⁻¹' E) :=
    fun σ ↦ measurable_swap σ hE
  -- the indicator of `E` composed with `swap σ` is the indicator of the preimage
  have hind : ∀ σ : Fin m → Bool, (fun z ↦ E.indicator (fun _ ↦ (1 : ℝ)) (swap σ z))
      = (swap (X := X) σ ⁻¹' E).indicator (fun _ ↦ (1 : ℝ)) := by
    intro σ
    funext z
    rfl
  have hintegrable : ∀ σ : Fin m → Bool,
      Integrable (fun z ↦ E.indicator (fun _ ↦ (1 : ℝ)) (swap σ z)) π := by
    intro σ
    rw [hind σ]
    exact (integrable_const (1 : ℝ)).indicator (hmeas σ)
  -- each swap has the same measure, since `swap σ` is measure preserving
  have hint : ∀ σ : Fin m → Bool,
      ∫ z, E.indicator (fun _ ↦ (1 : ℝ)) (swap σ z) ∂π = π.real E := by
    intro σ
    rw [hind σ, integral_indicator_const (1 : ℝ) (hmeas σ), smul_eq_mul, mul_one,
      (measurePreserving_swap μ σ).measureReal_preimage hE.nullMeasurableSet]
  -- hence the average over the `2 ^ m` swaps integrates to the measure of `E`
  have hsum : ∫ z, (∑ σ : Fin m → Bool, E.indicator (fun _ ↦ (1 : ℝ)) (swap σ z)) / 2 ^ m ∂π
      = π.real E := by
    rw [integral_div, integral_finsetSum _ (fun σ _ ↦ hintegrable σ)]
    simp only [hint, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    field_simp
  have hIntLHS : Integrable
      (fun z ↦ (∑ σ : Fin m → Bool, E.indicator (fun _ ↦ (1 : ℝ)) (swap σ z)) / 2 ^ m) π :=
    (integrable_finsetSum _ fun σ _ ↦ hintegrable σ).div_const _
  calc π.real E = ∫ z, (∑ σ : Fin m → Bool, E.indicator (fun _ ↦ (1 : ℝ)) (swap σ z)) / 2 ^ m ∂π :=
        hsum.symm
    _ ≤ ∫ _, K ∂π := integral_mono hIntLHS (integrable_const K) h
    _ = K := by simp

end VCInequality
