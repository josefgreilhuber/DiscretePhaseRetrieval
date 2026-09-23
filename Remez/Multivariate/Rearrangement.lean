/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Remez.Multivariate.Defs

/-!
# Rearrangement estimates for ray fibers

This file collects the one-dimensional estimates that drive the Brudnyi–Ganzburg approach to
the multivariate Remez inequality.  Everything happens on a single ray: we fix a base point
`x ∈ ℝᵐ` and a direction `θ ≠ 0` and study the fiber `rayFiber V x θ = {r > 0 | x + r • θ ∈ V}`.

The main results are:

* `Remez.volume_rayFiber_ne_top`: a bounded set has ray fibers of finite length;
* `Remez.rayFiber_subset_Ioc` and `Remez.Ioo_subset_rayFiber`: for a convex `V` containing the
  base point `x`, the fiber is an interval starting at `0`, squeezed between `Ioo 0 ρ` and
  `Ioc 0 ρ` where `ρ` is its length;
* `Remez.lintegral_pow_Ioc`: the elementary computation `∫_s^ρ r^{m-1} dr = (ρ^m - s^m)/m`;
* `Remez.lintegral_pow_le_of_subset_Ioc`: *pushing to the right* — among measurable subsets of
  `(0, ρ]` of a given length, the weighted length `∫ r^{m-1} dr` is maximal for the terminal
  interval;
* `Remez.rayWeight_eq` and `Remez.rayWeight_le`: the two consequences for `rayWeight`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Remez

variable {m : ℕ}

/-! ### Boundedness and the interval structure of ray fibers -/

/-- If `V` is contained in the closed ball of radius `R` around `x`, then every ray fiber of `V`
based at `x` is contained in `(0, R / ‖θ‖]`. -/
theorem rayFiber_subset_Ioc_div {V : Set (Fin m → ℝ)} {x : Fin m → ℝ} {R : ℝ}
    (hVR : V ⊆ Metric.closedBall x R) {θ : Fin m → ℝ} (hθ : θ ≠ 0) :
    rayFiber V x θ ⊆ Ioc 0 (R / ‖θ‖) := by
  intro r hr
  obtain ⟨hr0, hrV⟩ := hr
  have hθ0 : 0 < ‖θ‖ := norm_pos_iff.mpr hθ
  have hball := hVR hrV
  rw [Metric.mem_closedBall, dist_eq_norm] at hball
  have hnorm : ‖x + r • θ - x‖ = r * ‖θ‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  rw [hnorm] at hball
  exact ⟨hr0, (le_div_iff₀ hθ0).mpr hball⟩

/-- Ray fibers of a bounded set in a nonzero direction have finite length. -/
theorem volume_rayFiber_ne_top {V : Set (Fin m → ℝ)} (hV : Bornology.IsBounded V)
    (x : Fin m → ℝ) {θ : Fin m → ℝ} (hθ : θ ≠ 0) : volume (rayFiber V x θ) ≠ ⊤ := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).mp hV
  refine ne_top_of_le_ne_top ?_ (measure_mono (rayFiber_subset_Ioc_div hR hθ))
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

/-- Ray fibers of a bounded set in a nonzero direction are bounded above. -/
theorem bddAbove_rayFiber {V : Set (Fin m → ℝ)} (hV : Bornology.IsBounded V)
    (x : Fin m → ℝ) {θ : Fin m → ℝ} (hθ : θ ≠ 0) : BddAbove (rayFiber V x θ) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).mp hV
  exact ⟨R / ‖θ‖, fun _ hr => (rayFiber_subset_Ioc_div hR hθ hr).2⟩

/-- For a convex `V` containing the base point `x`, the ray fiber is downward closed inside
`(0, ∞)`: if `r` belongs to it and `0 < r' ≤ r`, then so does `r'`. -/
theorem mem_rayFiber_of_le {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V) {x : Fin m → ℝ} (hx : x ∈ V)
    {θ : Fin m → ℝ} {r r' : ℝ} (hr : r ∈ rayFiber V x θ) (hr'0 : 0 < r') (hr' : r' ≤ r) :
    r' ∈ rayFiber V x θ := by
  obtain ⟨hr0, hrV⟩ := hr
  refine ⟨hr'0, ?_⟩
  have hmem := hVc.add_smul_mem hx hrV (t := r' / r)
    ⟨by positivity, (div_le_one hr0).mpr hr'⟩
  have hsmul : (r' / r) • (r • θ) = r' • θ := by
    rw [smul_smul]
    congr 1
    field_simp
  rwa [hsmul] at hmem

/-- A ray fiber of a bounded set is contained in `(0, sSup]`. -/
theorem rayFiber_subset_Ioc_sSup {V : Set (Fin m → ℝ)} (hVb : Bornology.IsBounded V)
    {x : Fin m → ℝ} {θ : Fin m → ℝ} (hθ : θ ≠ 0) :
    rayFiber V x θ ⊆ Ioc 0 (sSup (rayFiber V x θ)) :=
  fun _ hr => ⟨hr.1, le_csSup (bddAbove_rayFiber hVb x hθ) hr⟩

/-- A ray fiber of a convex set containing the base point contains `(0, sSup)`. -/
theorem Ioo_sSup_subset_rayFiber {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V) {x : Fin m → ℝ}
    (hx : x ∈ V) {θ : Fin m → ℝ} : Ioo 0 (sSup (rayFiber V x θ)) ⊆ rayFiber V x θ := by
  rintro r ⟨hr0, hrlt⟩
  rcases (rayFiber V x θ).eq_empty_or_nonempty with h | h
  · rw [h, Real.sSup_empty] at hrlt
    exact absurd (hr0.trans hrlt) (lt_irrefl 0)
  · obtain ⟨r₀, hr₀mem, hr₀⟩ := exists_lt_of_lt_csSup h hrlt
    exact mem_rayFiber_of_le hVc hx hr₀mem hr0 hr₀.le

/-- The supremum of a ray fiber of a bounded set is nonnegative. -/
theorem sSup_rayFiber_nonneg {V : Set (Fin m → ℝ)} (hVb : Bornology.IsBounded V)
    (x : Fin m → ℝ) {θ : Fin m → ℝ} (hθ : θ ≠ 0) : 0 ≤ sSup (rayFiber V x θ) := by
  rcases (rayFiber V x θ).eq_empty_or_nonempty with h | h
  · rw [h, Real.sSup_empty]
  · obtain ⟨r₀, hr₀⟩ := h
    exact hr₀.1.le.trans (le_csSup (bddAbove_rayFiber hVb x hθ) hr₀)

/-- For a bounded convex `V` containing the base point, the length of the ray fiber is its
supremum. -/
theorem toReal_volume_rayFiber {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V)
    (hVb : Bornology.IsBounded V) {x : Fin m → ℝ} (hx : x ∈ V) {θ : Fin m → ℝ} (hθ : θ ≠ 0) :
    (volume (rayFiber V x θ)).toReal = sSup (rayFiber V x θ) := by
  have hle : volume (rayFiber V x θ) ≤ ENNReal.ofReal (sSup (rayFiber V x θ)) := by
    have h := measure_mono (μ := volume) (rayFiber_subset_Ioc_sSup (x := x) hVb hθ)
    rwa [Real.volume_Ioc, sub_zero] at h
  have hge : ENNReal.ofReal (sSup (rayFiber V x θ)) ≤ volume (rayFiber V x θ) := by
    have h := measure_mono (μ := volume) (Ioo_sSup_subset_rayFiber hVc hx (θ := θ))
    rwa [Real.volume_Ioo, sub_zero] at h
  rw [le_antisymm hle hge, ENNReal.toReal_ofReal (sSup_rayFiber_nonneg hVb x hθ)]

/-- For `V` convex and `x ∈ V`, the ray fiber is an interval starting at `0`: it is contained in
`(0, ρ]` where `ρ` is its length. -/
theorem rayFiber_subset_Ioc {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V) (hVb : Bornology.IsBounded V)
    {x : Fin m → ℝ} (hx : x ∈ V) {θ : Fin m → ℝ} (hθ : θ ≠ 0) :
    rayFiber V x θ ⊆ Ioc 0 (volume (rayFiber V x θ)).toReal := by
  rw [toReal_volume_rayFiber hVc hVb hx hθ]
  exact rayFiber_subset_Ioc_sSup hVb hθ

/-- For `V` convex and `x ∈ V`, the ray fiber contains `(0, ρ)` where `ρ` is its length. -/
theorem Ioo_subset_rayFiber {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V) (hVb : Bornology.IsBounded V)
    {x : Fin m → ℝ} (hx : x ∈ V) {θ : Fin m → ℝ} (hθ : θ ≠ 0) :
    Ioo 0 (volume (rayFiber V x θ)).toReal ⊆ rayFiber V x θ := by
  rw [toReal_volume_rayFiber hVc hVb hx hθ]
  exact Ioo_sSup_subset_rayFiber hVc hx

/-! ### The weighted length of an interval -/

/-- `∫_s^ρ r^{m-1} dr = (ρ^m - s^m)/m`. -/
theorem lintegral_pow_Ioc (hm : 0 < m) {s ρ : ℝ} (hs : 0 ≤ s) (hsρ : s ≤ ρ) :
    ∫⁻ r in Ioc s ρ, ENNReal.ofReal (r ^ (m - 1)) = ENNReal.ofReal ((ρ ^ m - s ^ m) / m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  simp only [Nat.add_sub_cancel]
  have hint : IntegrableOn (fun r : ℝ => r ^ k) (Ioc s ρ) volume :=
    (intervalIntegral.intervalIntegrable_pow (μ := volume) (n := k) (a := s) (b := ρ)).1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc s ρ)] fun r : ℝ => r ^ k := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc s ρ))] with r hr
    change (0 : ℝ) ≤ r ^ k
    exact pow_nonneg (hs.trans hr.1.le) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le hsρ, integral_pow]
  push_cast
  ring_nf

/-! ### Pushing mass to the right -/

/-- **Pushing to the right.** Since `r ↦ r^{m-1}` is increasing on `(0, ∞)`, among all
measurable `A ⊆ (0, ρ]` of given length the weighted length `∫_A r^{m-1} dr` is largest when
`A` is the terminal interval `(ρ - |A|, ρ]`. -/
theorem lintegral_pow_le_of_subset_Ioc (hm : 0 < m) {ρ : ℝ} {A : Set ℝ} (hA : MeasurableSet A)
    (hAρ : A ⊆ Ioc 0 ρ) :
    ∫⁻ r in A, ENNReal.ofReal (r ^ (m - 1)) ≤
      ∫⁻ r in Ioc (ρ - (volume A).toReal) ρ, ENNReal.ofReal (r ^ (m - 1)) := by
  have _hm := hm
  rcases le_or_gt ρ 0 with hρ | hρ
  · have hAe : A = ∅ := by
      refine eq_empty_of_forall_notMem fun r hr => ?_
      have h := hAρ hr
      linarith [h.1, h.2]
    simp [hAe]
  · set a := (volume A).toReal with ha
    have hAtop : volume A ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono hAρ)
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have haρ : a ≤ ρ := by
      have h := measure_mono (μ := volume) hAρ
      rw [Real.volume_Ioc, sub_zero] at h
      calc a ≤ (ENNReal.ofReal ρ).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
        _ = ρ := ENNReal.toReal_ofReal hρ.le
    have hc0 : 0 ≤ ρ - a := by linarith
    have hIoc : MeasurableSet (Ioc (ρ - a) ρ) := measurableSet_Ioc
    have hvolIoc : volume (Ioc (ρ - a) ρ) = volume A := by
      rw [Real.volume_Ioc, sub_sub_cancel, ha, ENNReal.ofReal_toReal hAtop]
    have key1 : volume (A ∩ Ioc (ρ - a) ρ) + volume (A \ Ioc (ρ - a) ρ) = volume A :=
      measure_inter_add_diff (μ := volume) A hIoc
    have key2 : volume (A ∩ Ioc (ρ - a) ρ) + volume (Ioc (ρ - a) ρ \ A) = volume A := by
      have h := measure_inter_add_diff (μ := volume) (Ioc (ρ - a) ρ) hA
      rwa [hvolIoc, Set.inter_comm] at h
    have hfin : volume (A ∩ Ioc (ρ - a) ρ) ≠ ⊤ :=
      ne_top_of_le_ne_top hAtop (measure_mono Set.inter_subset_left)
    have hmeq : volume (A \ Ioc (ρ - a) ρ) = volume (Ioc (ρ - a) ρ \ A) :=
      (ENNReal.add_right_inj hfin).mp (key1.trans key2.symm)
    -- the part of `A` to the left of `ρ - a` sits inside `(0, ρ - a]`
    have hsub1 : A \ Ioc (ρ - a) ρ ⊆ Ioc 0 (ρ - a) := by
      rintro r ⟨hrA, hrn⟩
      obtain ⟨hr0, hrρ⟩ := hAρ hrA
      exact ⟨hr0, by by_contra h; exact hrn ⟨not_le.mp h, hrρ⟩⟩
    have hmeasf : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (m - 1)) :=
      (measurable_id.pow_const _).ennreal_ofReal
    have hb1 : ∫⁻ r in A \ Ioc (ρ - a) ρ, ENNReal.ofReal (r ^ (m - 1)) ≤
        ENNReal.ofReal ((ρ - a) ^ (m - 1)) * volume (A \ Ioc (ρ - a) ρ) := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono measurable_const fun r hr => ?_
      obtain ⟨hr0, hrc⟩ := hsub1 hr
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr0.le hrc _)
    have hb2 : ENNReal.ofReal ((ρ - a) ^ (m - 1)) * volume (Ioc (ρ - a) ρ \ A) ≤
        ∫⁻ r in Ioc (ρ - a) ρ \ A, ENNReal.ofReal (r ^ (m - 1)) := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono hmeasf fun r hr => ?_
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc0 hr.1.1.le _)
    have hfinal : ∫⁻ r in A \ Ioc (ρ - a) ρ, ENNReal.ofReal (r ^ (m - 1)) ≤
        ∫⁻ r in Ioc (ρ - a) ρ \ A, ENNReal.ofReal (r ^ (m - 1)) := by
      refine hb1.trans ?_
      rw [hmeq]
      exact hb2
    have hsplitA : ∫⁻ r in A, ENNReal.ofReal (r ^ (m - 1)) =
        (∫⁻ r in A \ Ioc (ρ - a) ρ, ENNReal.ofReal (r ^ (m - 1))) +
          ∫⁻ r in A ∩ Ioc (ρ - a) ρ, ENNReal.ofReal (r ^ (m - 1)) := by
      conv_lhs => rw [← Set.diff_union_inter A (Ioc (ρ - a) ρ)]
      exact lintegral_union (hA.inter hIoc) disjoint_sdiff_inter
    have hsplitI : ∫⁻ r in Ioc (ρ - a) ρ, ENNReal.ofReal (r ^ (m - 1)) =
        (∫⁻ r in A ∩ Ioc (ρ - a) ρ, ENNReal.ofReal (r ^ (m - 1))) +
          ∫⁻ r in Ioc (ρ - a) ρ \ A, ENNReal.ofReal (r ^ (m - 1)) := by
      rw [Set.inter_comm A (Ioc (ρ - a) ρ)]
      conv_lhs => rw [← Set.inter_union_diff (Ioc (ρ - a) ρ) A]
      exact lintegral_union (hIoc.diff hA) disjoint_inf_sdiff
    rw [hsplitA, hsplitI, add_comm]
    exact add_le_add le_rfl hfinal

/-! ### Consequences for `rayWeight` -/

/-- The weighted length of the ray fiber of a bounded convex set is `ρ^m / m`. -/
theorem rayWeight_eq (hm : 0 < m) {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V)
    (hVb : Bornology.IsBounded V) {x : Fin m → ℝ} (hx : x ∈ V) {θ : Fin m → ℝ} (hθ : θ ≠ 0) :
    rayWeight m V x θ = ENNReal.ofReal ((volume (rayFiber V x θ)).toReal ^ m / m) := by
  have hae : rayFiber V x θ =ᵐ[volume] Ioc 0 (volume (rayFiber V x θ)).toReal := by
    have h0 : Ioo (0 : ℝ) (volume (rayFiber V x θ)).toReal
        =ᵐ[volume] Ioc (0 : ℝ) (volume (rayFiber V x θ)).toReal := Ioo_ae_eq_Ioc
    rw [Filter.eventuallyEq_set] at h0 ⊢
    filter_upwards [h0] with r hr
    exact ⟨fun h => rayFiber_subset_Ioc hVc hVb hx hθ h,
      fun h => Ioo_subset_rayFiber hVc hVb hx hθ (hr.mpr h)⟩
  rw [rayWeight, setLIntegral_congr hae,
    lintegral_pow_Ioc hm le_rfl ENNReal.toReal_nonneg, zero_pow hm.ne', sub_zero]

/-- The weighted length of the ray fiber of a measurable `M ⊆ V` is at most that of the
terminal interval of `(0, ρ]` of the same length. -/
theorem rayWeight_le (hm : 0 < m) {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V)
    (hVb : Bornology.IsBounded V) {x : Fin m → ℝ} (hx : x ∈ V) {θ : Fin m → ℝ} (hθ : θ ≠ 0)
    {M : Set (Fin m → ℝ)} (hM : MeasurableSet M) (hMV : M ⊆ V) :
    rayWeight m M x θ ≤ ∫⁻ r in Ioc ((volume (rayFiber V x θ)).toReal -
      (volume (rayFiber M x θ)).toReal) (volume (rayFiber V x θ)).toReal,
        ENNReal.ofReal (r ^ (m - 1)) := by
  rw [rayWeight]
  exact lintegral_pow_le_of_subset_Ioc hm (measurableSet_rayFiber hM x θ)
    ((rayFiber_mono hMV x θ).trans (rayFiber_subset_Ioc hVc hVb hx hθ))

end Remez
