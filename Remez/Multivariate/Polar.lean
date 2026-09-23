/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Remez.Multivariate.Defs

/-!
# Polar coordinates about a point of `ℝᵐ`

For a measurable set `S ⊆ ℝᵐ = (Fin m → ℝ)` and a base point `x`, the Lebesgue measure of `S`
is recovered by integrating the `r^{m-1}`-weighted lengths `rayWeight m S x θ` of the ray fibers
of `S` emanating from `x` over the unit sphere, with respect to the measure
`MeasureTheory.Measure.toSphere` attached to `volume`.

The proof reduces to Mathlib's generalized polar coordinate change
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`, after translating `S` by `x`
and discarding the (null) origin.

## Main results

* `Remez.measurable_rayWeight`: `θ ↦ rayWeight m S x θ` is measurable on the unit sphere.
* `Remez.volume_eq_lintegral_rayWeight`: the polar coordinate formula about `x`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Remez

variable {m : ℕ}

/-- The set of pairs `(θ, r)` on `sphere 0 1 × (0, ∞)` with `x + r • θ ∈ S`; the image of `S`
under polar coordinates centred at `x`. -/
def polarSet (S : Set (Fin m → ℝ)) (x : Fin m → ℝ) :
    Set (Metric.sphere (0 : Fin m → ℝ) 1 × Ioi (0 : ℝ)) :=
  {p | x + (p.2 : ℝ) • (p.1 : Fin m → ℝ) ∈ S}

lemma measurable_polarMap (x : Fin m → ℝ) :
    Measurable fun p : Metric.sphere (0 : Fin m → ℝ) 1 × Ioi (0 : ℝ) =>
      x + (p.2 : ℝ) • (p.1 : Fin m → ℝ) := by
  fun_prop

lemma measurableSet_polarSet {S : Set (Fin m → ℝ)} (hS : MeasurableSet S) (x : Fin m → ℝ) :
    MeasurableSet (polarSet S x) :=
  hS.preimage (measurable_polarMap x)

lemma measurableSet_polarSection {S : Set (Fin m → ℝ)} (hS : MeasurableSet S)
    (x θ : Fin m → ℝ) : MeasurableSet {r : Ioi (0 : ℝ) | x + (r : ℝ) • θ ∈ S} :=
  hS.preimage (by fun_prop)

lemma image_subtype_val_polarSection (S : Set (Fin m → ℝ)) (x θ : Fin m → ℝ) :
    ((↑) : Ioi (0 : ℝ) → ℝ) '' {r : Ioi (0 : ℝ) | x + (r : ℝ) • θ ∈ S} = rayFiber S x θ := by
  ext r
  constructor
  · rintro ⟨⟨s, hs⟩, hmem, rfl⟩
    exact ⟨hs, hmem⟩
  · rintro ⟨hr, hmem⟩
    exact ⟨⟨r, hr⟩, hmem, rfl⟩

/-- The weighted ray length `rayWeight m S x θ` is the `volumeIoiPow (m - 1)`-measure of the
section `{r > 0 | x + r • θ ∈ S}`. -/
lemma rayWeight_eq_volumeIoiPow {S : Set (Fin m → ℝ)} (hS : MeasurableSet S) (x θ : Fin m → ℝ) :
    rayWeight m S x θ =
      Measure.volumeIoiPow (m - 1) {r : Ioi (0 : ℝ) | x + (r : ℝ) • θ ∈ S} := by
  rw [Measure.volumeIoiPow, withDensity_apply _ (measurableSet_polarSection hS x θ),
    setLIntegral_subtype measurableSet_Ioi _ fun a : ℝ ↦ ENNReal.ofReal (a ^ (m - 1)),
    image_subtype_val_polarSection]
  rfl

/-- `θ ↦ rayWeight m S x θ` is measurable on the unit sphere. -/
theorem measurable_rayWeight {S : Set (Fin m → ℝ)} (hS : MeasurableSet S) (x : Fin m → ℝ) :
    Measurable fun θ : Metric.sphere (0 : Fin m → ℝ) 1 => rayWeight m S x θ := by
  have h : (fun θ : Metric.sphere (0 : Fin m → ℝ) 1 => rayWeight m S x θ) =
      fun θ => Measure.volumeIoiPow (m - 1) (Prod.mk θ ⁻¹' polarSet S x) := by
    funext θ
    exact rayWeight_eq_volumeIoiPow hS x _
  rw [h]
  exact measurable_measure_prodMk_left (measurableSet_polarSet hS x)

/-- **Polar coordinates about `x`.** The Lebesgue measure of a measurable set `S ⊆ ℝᵐ` is the
integral over the unit sphere (with respect to `volume.toSphere`) of the `r^{m-1}`-weighted
length of the ray fibers of `S` from `x`. -/
theorem volume_eq_lintegral_rayWeight (hm : 0 < m) {S : Set (Fin m → ℝ)} (hS : MeasurableSet S)
    (x : Fin m → ℝ) :
    volume S = ∫⁻ θ : Metric.sphere (0 : Fin m → ℝ) 1, rayWeight m S x θ ∂(volume.toSphere) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nontrivial (Fin m → ℝ) := Function.nontrivial
  -- The translate of `S` by `-x`.
  set S' : Set (Fin m → ℝ) := (fun y => x + y) ⁻¹' S with hS'def
  have hS'meas : MeasurableSet S' := hS.preimage (by fun_prop)
  have hc : MeasurableSet ({0}ᶜ : Set (Fin m → ℝ)) := (measurableSet_singleton 0).compl
  -- Step 1: translation invariance.
  have e1 : volume S = volume S' := (measure_preimage_add volume x S).symm
  -- Step 2: pass to the punctured space.
  have e2 : (volume.comap ((↑) : ({0}ᶜ : Set (Fin m → ℝ)) → Fin m → ℝ))
      (((↑) : ({0}ᶜ : Set (Fin m → ℝ)) → Fin m → ℝ) ⁻¹' S') = volume S' := by
    rw [comap_subtype_coe_apply hc, Subtype.image_preimage_coe, inter_comm, ← diff_eq,
      measure_diff_null (measure_singleton 0)]
  -- Step 3: apply the polar coordinate change.
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (Fin m → ℝ))
  have hpre : (homeomorphUnitSphereProd (Fin m → ℝ)) ⁻¹' (polarSet S x) =
      ((↑) : ({0}ᶜ : Set (Fin m → ℝ)) → Fin m → ℝ) ⁻¹' S' := by
    ext y
    have hy0 : (y : Fin m → ℝ) ≠ 0 := y.2
    have hy : ‖(y : Fin m → ℝ)‖ ≠ 0 := norm_ne_zero_iff.2 hy0
    simp only [polarSet, mem_preimage, mem_setOf_eq, hS'def,
      homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe,
      smul_smul, mul_inv_cancel₀ hy, one_smul]
  have e3 := hmp.measure_preimage (measurableSet_polarSet hS x).nullMeasurableSet
  rw [hpre, e2] at e3
  -- Step 4: unfold the product measure.
  have hdim : Module.finrank ℝ (Fin m → ℝ) - 1 = m - 1 := by
    rw [Module.finrank_fin_fun]
  rw [hdim, Measure.prod_apply (measurableSet_polarSet hS x)] at e3
  rw [e1, e3]
  exact (lintegral_congr fun θ => rayWeight_eq_volumeIoiPow hS x _).symm

end Remez
