/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Remez.Remez
import Remez.Multivariate.Defs
import Remez.Multivariate.Line
import Remez.Multivariate.Polar
import Remez.Multivariate.Rearrangement

/-!
# The Brudnyi–Ganzburg multivariate Remez inequality

This file proves inequality (4.1) of M. I. Ganzburg, *Polynomial inequalities on measurable
sets and their applications*, Constr. Approx. 17 (2001), due to Brudnyi and Ganzburg: for a
convex body `V ⊆ ℝᵐ`, a set `E ⊆ V` of positive Lebesgue measure and a real polynomial `P` in
`m` variables of total degree at most `n`,

  `max_{x ∈ V} |P(x)| ≤ Tₙ((1 + βₘ(|E|/|V|)) / (1 − βₘ(|E|/|V|))) · sup_{y ∈ E} |P(y)|`,

where `βₘ(t) = (1 − t)^{1/m}` and `Tₙ` is the Chebyshev polynomial.  The main statements are
`Remez.brudnyi_ganzburg` (with an explicit bound `K` for `|P|` on `E`) and
`Remez.brudnyi_ganzburg_sSup`.  `E` needs no measurability.

## Proof (scanning along rays)

Fix `x ∈ V` and the closed set `M = V ∩ {|P| ≤ K} ⊇ E`.  For a direction `θ` let
`V_θ, M_θ ⊆ (0, ∞)` be the ray fibers of `V` and `M` from `x`, of lengths `ρ(θ) ≥ a(θ)`.

1. Polar coordinates about `x` (`volume_eq_lintegral_rayWeight`) express `|M|` and `|V|` as
   integrals over the unit sphere of `∫_{M_θ} r^{m-1} dr` and `∫_{V_θ} r^{m-1} dr = ρ^m/m`
   (`V_θ` is an interval since `V` is convex, `rayWeight_eq`).
2. `exists_good_ray`: some ray with `ρ(θ) > 0` has `a(θ) ≥ (1 − β)ρ(θ)`, `β = βₘ(|M|/|V|)`.
   Otherwise, pushing `M_θ` to the far end of `V_θ` (`rayWeight_le`) gives
   `∫_{M_θ} r^{m-1} < ∫_{βρ}^{ρ} r^{m-1} = (|M|/|V|) ∫_{V_θ} r^{m-1}` on the set `{ρ > 0}`,
   which has positive measure; integrating over the sphere yields `|M| < |M|`.
3. On that ray, `r ↦ P(x + rθ)` is a univariate polynomial of degree `≤ n`
   (`lineRestrict`), bounded by `K` on `M_θ ⊆ [0, ρ]`, and `|M_θ| ≥ (1 − β)ρ`; the
   one-dimensional Remez inequality at the endpoint `r = 0` gives exactly
   `|P(x)| ≤ Tₙ((1 + β)/(1 − β)) K`.
4. Since `|M| ≥ |E|` and `Tₙ` is monotone on `[1, ∞)`, the constant for `E` is larger.
-/

open MeasureTheory Set Polynomial.Chebyshev
open scoped ENNReal

namespace Remez

variable {m : ℕ}

/-! ### Elementary facts on `βₘ` -/

lemma beta_nonneg (m : ℕ) {t : ℝ} (ht : t ≤ 1) : 0 ≤ beta m t :=
  Real.rpow_nonneg (by linarith) _

lemma beta_pow (hm : 0 < m) {t : ℝ} (ht : t ≤ 1) : beta m t ^ m = 1 - t := by
  unfold beta
  rw [one_div, Real.rpow_inv_natCast_pow (by linarith) hm.ne']

lemma beta_lt_one (hm : 0 < m) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : beta m t < 1 :=
  Real.rpow_lt_one (by linarith) (by linarith) (by positivity)

lemma beta_anti (hm : 0 < m) {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 1) : beta m t ≤ beta m s :=
  Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)

lemma ne_zero_of_mem_sphere (θ : Metric.sphere (0 : Fin m → ℝ) 1) : (θ : Fin m → ℝ) ≠ 0 := by
  intro h
  have := θ.2
  rw [mem_sphere_zero_iff_norm, h, norm_zero] at this
  exact zero_ne_one this

/-! ### A ray catching enough of the measure -/

/-- **A good ray exists.**  For a compact convex `V`, a measurable `M ⊆ V` of positive measure
and `x ∈ V`, there is a direction `θ` whose ray fiber `V_θ` has positive length `ρ` and whose
fiber `M_θ` has length at least `(1 − βₘ(|M|/|V|)) ρ`. -/
theorem exists_good_ray (hm : 0 < m) {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V)
    (hVcpt : IsCompact V) {M : Set (Fin m → ℝ)} (hM : MeasurableSet M) (hMV : M ⊆ V)
    (hvol : 0 < volume M) {x : Fin m → ℝ} (hx : x ∈ V) :
    ∃ θ : Fin m → ℝ, θ ≠ 0 ∧ 0 < (volume (rayFiber V x θ)).toReal ∧
      ENNReal.ofReal ((1 - beta m ((volume M).toReal / (volume V).toReal)) *
        (volume (rayFiber V x θ)).toReal) ≤ volume (rayFiber M x θ) := by
  set σ := (volume : Measure (Fin m → ℝ)).toSphere with hσ_def
  have hVb : Bornology.IsBounded V := hVcpt.isBounded
  have hVm : MeasurableSet V := hVcpt.isClosed.measurableSet
  have hVfin : volume V ≠ ⊤ := hVb.measure_lt_top.ne
  have hMfin : volume M ≠ ⊤ := ne_top_of_le_ne_top hVfin (measure_mono hMV)
  have hVpos : 0 < volume V := hvol.trans_le (measure_mono hMV)
  set t := (volume M).toReal / (volume V).toReal with ht_def
  set β := beta m t with hβ_def
  have hVr : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVfin
  have hMr : 0 < (volume M).toReal := ENNReal.toReal_pos hvol.ne' hMfin
  have ht0 : 0 < t := div_pos hMr hVr
  have ht1 : t ≤ 1 := (div_le_one hVr).2 (ENNReal.toReal_mono hVfin (measure_mono hMV))
  have hβm : β ^ m = 1 - t := beta_pow hm ht1
  have hβ0 : 0 ≤ β := beta_nonneg m ht1
  have hβ1 : β < 1 := beta_lt_one hm ht0 ht1
  have hc : ENNReal.ofReal t * volume V = volume M := by
    rw [ht_def, ENNReal.ofReal_div_of_pos hVr, ENNReal.ofReal_toReal hMfin,
      ENNReal.ofReal_toReal hVfin, ENNReal.div_mul_cancel hVpos.ne' hVfin]
  by_contra hcon
  push Not at hcon
  -- pointwise comparison of the ray weights
  have hle : ∀ θ : Metric.sphere (0 : Fin m → ℝ) 1,
      rayWeight m M x θ ≤ ENNReal.ofReal t * rayWeight m V x θ ∧
      (0 < (volume (rayFiber V x θ)).toReal →
        rayWeight m M x θ < ENNReal.ofReal t * rayWeight m V x θ) := by
    intro θ
    have hθ := ne_zero_of_mem_sphere θ
    have hfinV := volume_rayFiber_ne_top hVb x hθ
    have hfinM : volume (rayFiber M x θ) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinV (measure_mono (rayFiber_mono hMV x θ))
    set ρ := (volume (rayFiber V x θ)).toReal with hρ_def
    set a := (volume (rayFiber M x θ)).toReal with ha_def
    have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have haρ : a ≤ ρ := ENNReal.toReal_mono hfinV (measure_mono (rayFiber_mono hMV x θ))
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 hm
    rw [rayWeight_eq hm hVc hVb hx hθ, ← ENNReal.ofReal_mul ht0.le]
    have key := rayWeight_le hm hVc hVb hx hθ hM hMV
    rw [lintegral_pow_Ioc hm (by linarith) (by linarith)] at key
    rw [← hρ_def, ← ha_def] at key
    rcases hρ0.eq_or_lt with hρ | hρ
    · have ha : a = 0 := le_antisymm (hρ ▸ haρ) ha0
      refine ⟨key.trans ?_, fun h => absurd h (by rw [← hρ]; exact lt_irrefl 0)⟩
      rw [← hρ, ha]
      simp
    · have hstrict := hcon θ hθ hρ
      have ha' : a < (1 - β) * ρ := by
        have := (ENNReal.toReal_lt_toReal hfinM ENNReal.ofReal_ne_top).2 hstrict
        rwa [ENNReal.toReal_ofReal (by nlinarith)] at this
      have hlt : (ρ ^ m - (ρ - a) ^ m) / m < t * (ρ ^ m / m) := by
        have h1 : β * ρ < ρ - a := by nlinarith
        have h2 : (β * ρ) ^ m < (ρ - a) ^ m := pow_lt_pow_left₀ h1 (by positivity) hm.ne'
        rw [mul_pow, hβm] at h2
        rw [div_lt_iff₀ hmpos, show t * (ρ ^ m / m) * m = t * ρ ^ m by field_simp]
        linarith
      exact ⟨key.trans (ENNReal.ofReal_le_ofReal hlt.le),
        fun _ => key.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt)⟩
  -- integrate over the sphere
  have hint_M := volume_eq_lintegral_rayWeight hm hM x
  have hint_V := volume_eq_lintegral_rayWeight hm hVm x
  have hmeasV := measurable_rayWeight hVm x
  have hs : σ {θ : Metric.sphere (0 : Fin m → ℝ) 1 |
      0 < (volume (rayFiber V x θ)).toReal} ≠ 0 := by
    intro hs0
    have hzero : ∫⁻ θ, rayWeight m V x θ ∂σ = 0 := by
      rw [lintegral_eq_zero_iff hmeasV]
      refine (measure_eq_zero_iff_ae_notMem.1 hs0).mono fun θ hθ => ?_
      change rayWeight m V x θ = 0
      rw [rayWeight_eq hm hVc hVb hx (ne_zero_of_mem_sphere θ)]
      have h0 : (volume (rayFiber V x θ)).toReal = 0 :=
        le_antisymm (not_lt.1 hθ) ENNReal.toReal_nonneg
      simp [h0, hm.ne']
    rw [← hint_V] at hzero
    exact hVpos.ne' hzero
  have hlt := lintegral_strict_mono_of_ae_le_of_ae_lt_on (μ := σ)
    (hmeasV.const_mul _).aemeasurable (hint_M ▸ hMfin)
    (Filter.Eventually.of_forall fun θ => (hle θ).1) hs
    (Filter.Eventually.of_forall fun θ hθ => (hle θ).2 hθ)
  rw [← hint_M, lintegral_const_mul _ hmeasV, ← hint_V, hc] at hlt
  exact lt_irrefl _ hlt

/-! ### The multivariate Remez inequality -/

/-- The Brudnyi–Ganzburg inequality for a measurable set `M ⊆ V`. -/
theorem brudnyi_ganzburg_of_measurable (hm : 0 < m) {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V)
    (hVcpt : IsCompact V) {M : Set (Fin m → ℝ)} (hM : MeasurableSet M) (hMV : M ⊆ V)
    (hvol : 0 < volume M) {P : MvPolynomial (Fin m) ℝ} {n : ℕ} (hP : P.totalDegree ≤ n)
    {K : ℝ} (hPM : ∀ y ∈ M, |MvPolynomial.eval y P| ≤ K) {x : Fin m → ℝ} (hx : x ∈ V) :
    |MvPolynomial.eval x P| ≤
      (T ℝ n).eval ((1 + beta m ((volume M).toReal / (volume V).toReal)) /
        (1 - beta m ((volume M).toReal / (volume V).toReal))) * K := by
  obtain ⟨θ, hθ, hρ, hgood⟩ := exists_good_ray hm hVc hVcpt hM hMV hvol hx
  set t := (volume M).toReal / (volume V).toReal with ht_def
  set β := beta m t with hβ_def
  have hVfin : volume V ≠ ⊤ := hVcpt.isBounded.measure_lt_top.ne
  have hMfin : volume M ≠ ⊤ := ne_top_of_le_ne_top hVfin (measure_mono hMV)
  have hVpos : 0 < volume V := hvol.trans_le (measure_mono hMV)
  have hVr : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVfin
  have hMr : 0 < (volume M).toReal := ENNReal.toReal_pos hvol.ne' hMfin
  have ht0 : 0 < t := div_pos hMr hVr
  have ht1 : t ≤ 1 := (div_le_one hVr).2 (ENNReal.toReal_mono hVfin (measure_mono hMV))
  have hβ0 : 0 ≤ β := beta_nonneg m ht1
  have hβ1 : β < 1 := beta_lt_one hm ht0 ht1
  set ρ := (volume (rayFiber V x θ)).toReal with hρ_def
  set q := lineRestrict P x θ with hq_def
  have hq : q.natDegree ≤ n := (natDegree_lineRestrict_le P x θ).trans hP
  have hE : rayFiber M x θ ⊆ Icc 0 ρ := fun r hr =>
    ⟨hr.1.le, (rayFiber_subset_Ioc hVc hVcpt.isBounded hx hθ (rayFiber_mono hMV x θ hr)).2⟩
  have hqE : ∀ r ∈ rayFiber M x θ, |q.eval r| ≤ K := fun r hr => by
    rw [hq_def, eval_lineRestrict]
    exact hPM _ hr.2
  have hm0 : 0 < (1 - β) * ρ := mul_pos (by linarith) hρ
  have key := remez_of_abs_le hq hρ hE hqE hm0 hgood (x := 0) ⟨le_rfl, hρ.le⟩
  rw [hq_def, eval_lineRestrict, zero_smul, add_zero] at key
  convert key using 3
  have hρne : ρ ≠ 0 := hρ.ne'
  have hβne : 1 - β ≠ 0 := by linarith
  field_simp
  ring

/-- **The Brudnyi–Ganzburg multivariate Remez inequality** (Ganzburg, (4.1)).  Let `V ⊆ ℝᵐ`
be a compact convex set, `E ⊆ V` a set of positive Lebesgue measure, and `P` a real
polynomial in `m` variables of total degree at most `n` with `|P| ≤ K` on `E`.  Then for every
`x ∈ V`, with `β = βₘ(|E|/|V|) = (1 − |E|/|V|)^{1/m}`,
`|P(x)| ≤ Tₙ((1 + β)/(1 − β)) · K`. -/
theorem brudnyi_ganzburg (hm : 0 < m) {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V)
    (hVcpt : IsCompact V) {E : Set (Fin m → ℝ)} (hE : E ⊆ V) (hvol : 0 < volume E)
    {P : MvPolynomial (Fin m) ℝ} {n : ℕ} (hP : P.totalDegree ≤ n)
    {K : ℝ} (hPE : ∀ y ∈ E, |MvPolynomial.eval y P| ≤ K) {x : Fin m → ℝ} (hx : x ∈ V) :
    |MvPolynomial.eval x P| ≤
      (T ℝ n).eval ((1 + beta m ((volume E).toReal / (volume V).toReal)) /
        (1 - beta m ((volume E).toReal / (volume V).toReal))) * K := by
  set M := V ∩ {y | |MvPolynomial.eval y P| ≤ K} with hM_def
  have hMc : IsClosed M :=
    hVcpt.isClosed.inter (isClosed_le (MvPolynomial.continuous_eval P).abs continuous_const)
  have hEM : E ⊆ M := fun y hy => ⟨hE hy, hPE y hy⟩
  have hvolM : 0 < volume M := hvol.trans_le (measure_mono hEM)
  have key := brudnyi_ganzburg_of_measurable hm hVc hVcpt hMc.measurableSet inter_subset_left
    hvolM hP (fun y hy => hy.2) hx
  have hK0 : 0 ≤ K :=
    (abs_nonneg _).trans (hPE _ (nonempty_of_measure_ne_zero hvol.ne').some_mem)
  refine key.trans (mul_le_mul_of_nonneg_right ?_ hK0)
  -- compare the constants
  have hVfin : volume V ≠ ⊤ := hVcpt.isBounded.measure_lt_top.ne
  have hMfin : volume M ≠ ⊤ := ne_top_of_le_ne_top hVfin (measure_mono inter_subset_left)
  have hVpos : 0 < volume V := hvolM.trans_le (measure_mono inter_subset_left)
  have hVr : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVfin
  have hEr : 0 < (volume E).toReal :=
    ENNReal.toReal_pos hvol.ne' (ne_top_of_le_ne_top hMfin (measure_mono hEM))
  set tM := (volume M).toReal / (volume V).toReal with htM_def
  set tE := (volume E).toReal / (volume V).toReal with htE_def
  have htE0 : 0 < tE := div_pos hEr hVr
  have htEM : tE ≤ tM :=
    div_le_div_of_nonneg_right (ENNReal.toReal_mono hMfin (measure_mono hEM)) hVr.le
  have htM1 : tM ≤ 1 :=
    (div_le_one hVr).2 (ENNReal.toReal_mono hVfin (measure_mono inter_subset_left))
  have hβM0 : 0 ≤ beta m tM := beta_nonneg m htM1
  have hβME : beta m tM ≤ beta m tE := beta_anti hm htEM htM1
  have hβE1 : beta m tE < 1 := beta_lt_one hm htE0 (htEM.trans htM1)
  have hβM1 : beta m tM < 1 := hβME.trans_lt hβE1
  refine monotoneOn_eval_T n ?_ ?_ ?_
  · rw [mem_Ici, le_div_iff₀ (by linarith)]
    linarith
  · rw [mem_Ici, le_div_iff₀ (by linarith)]
    linarith
  · exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

/-- **The Brudnyi–Ganzburg inequality**, supremum form:
`|P(x)| ≤ Tₙ((1 + β)/(1 − β)) · sup_{y ∈ E} |P(y)|` for all `x ∈ V`. -/
theorem brudnyi_ganzburg_sSup (hm : 0 < m) {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V)
    (hVcpt : IsCompact V) {E : Set (Fin m → ℝ)} (hE : E ⊆ V) (hvol : 0 < volume E)
    {P : MvPolynomial (Fin m) ℝ} {n : ℕ} (hP : P.totalDegree ≤ n) {x : Fin m → ℝ} (hx : x ∈ V) :
    |MvPolynomial.eval x P| ≤
      (T ℝ n).eval ((1 + beta m ((volume E).toReal / (volume V).toReal)) /
        (1 - beta m ((volume E).toReal / (volume V).toReal))) *
        sSup ((fun y => |MvPolynomial.eval y P|) '' E) := by
  have hbdd : BddAbove ((fun y => |MvPolynomial.eval y P|) '' E) :=
    (hVcpt.bddAbove_image (MvPolynomial.continuous_eval P).abs.continuousOn).mono
      (Set.image_mono hE)
  exact brudnyi_ganzburg hm hVc hVcpt hE hvol hP
    (fun y hy => le_csSup hbdd (mem_image_of_mem _ hy)) hx

end Remez
