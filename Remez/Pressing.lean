/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-!
# The distribution function of a closed set and the "pressing" lemma

For a set `M ⊆ ℝ` we consider its *distribution function*
`cdf M t = |M ∩ (-∞, t]|` (Lebesgue measure, as a real number).  For `M ⊆ [a, b]` this
function is monotone and `1`-Lipschitz.

The main result, `Remez.exists_cdf_eq`, is the measure-theoretic heart of Bojanov's proof of
the Remez inequality: if `M ⊆ [a, b]` is closed and `c ∈ [0, |M|]`, then there is a point
`x ∈ M` with `|M ∩ (-∞, x]| = c`.  Bojanov phrases this as "press `M` to the left": the point
`x` is the point of `M` which lands at `a + c` after all the gaps of `M` are removed.
-/

open MeasureTheory Set

namespace Remez

/-- The distribution function `t ↦ |M ∩ (-∞, t]|` of a set `M ⊆ ℝ`. -/
noncomputable def cdf (M : Set ℝ) (t : ℝ) : ℝ := (volume (M ∩ Iic t)).toReal

variable {M : Set ℝ} {a b : ℝ}

lemma volume_ne_top_of_subset_Icc (hM : M ⊆ Icc a b) : volume M ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono hM)

lemma volume_inter_ne_top (hM : M ⊆ Icc a b) (S : Set ℝ) : volume (M ∩ S) ≠ ⊤ :=
  volume_ne_top_of_subset_Icc (inter_subset_left.trans hM)

lemma cdf_mono (hM : M ⊆ Icc a b) : Monotone (cdf M) := fun _ _ hst =>
  ENNReal.toReal_mono (volume_inter_ne_top hM _)
    (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hst)))

lemma cdf_sub (hM : M ⊆ Icc a b) (hMm : MeasurableSet M) {s t : ℝ} (hst : s ≤ t) :
    cdf M t - cdf M s = (volume (M ∩ Ioc s t)).toReal := by
  have h : M ∩ Iic t = (M ∩ Iic s) ∪ (M ∩ Ioc s t) := by
    rw [← inter_union_distrib_left, Iic_union_Ioc_eq_Iic hst]
  have hd : Disjoint (M ∩ Iic s) (M ∩ Ioc s t) :=
    Disjoint.mono inter_subset_right inter_subset_right (Iic_disjoint_Ioc le_rfl)
  unfold cdf
  rw [h, measure_union hd (hMm.inter measurableSet_Ioc),
    ENNReal.toReal_add (volume_inter_ne_top hM _) (volume_inter_ne_top hM _)]
  ring

lemma cdf_le_add (hM : M ⊆ Icc a b) (hMm : MeasurableSet M) (s t : ℝ) :
    cdf M t ≤ cdf M s + |t - s| := by
  rcases le_total s t with hst | hts
  · have h1 := cdf_sub hM hMm hst
    have h2 : (volume (M ∩ Ioc s t)).toReal ≤ t - s := by
      have := ENNReal.toReal_mono (b := volume (Ioc s t)) (by simp [Real.volume_Ioc])
        (measure_mono (inter_subset_right : M ∩ Ioc s t ⊆ Ioc s t))
      rwa [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at this
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have := cdf_mono hM hts
    linarith [abs_nonneg (t - s)]

lemma lipschitzWith_cdf (hM : M ⊆ Icc a b) (hMm : MeasurableSet M) :
    LipschitzWith 1 (cdf M) :=
  LipschitzWith.of_le_add fun s t => by rw [Real.dist_eq]; exact cdf_le_add hM hMm t s

lemma abs_cdf_sub_le (hM : M ⊆ Icc a b) (hMm : MeasurableSet M) (s t : ℝ) :
    |cdf M s - cdf M t| ≤ |s - t| := by
  have := (lipschitzWith_cdf hM hMm).dist_le_mul s t
  simpa [Real.dist_eq] using this

lemma cdf_eq_of_inter_Ioc_eq_empty (hM : M ⊆ Icc a b) (hMm : MeasurableSet M) {s t : ℝ}
    (hst : s ≤ t) (h : M ∩ Ioc s t = ∅) : cdf M t = cdf M s := by
  have := cdf_sub hM hMm hst
  rw [h, measure_empty, ENNReal.toReal_zero] at this
  linarith

lemma cdf_of_lt (hM : M ⊆ Icc a b) {t : ℝ} (ht : t < a) : cdf M t = 0 := by
  have : M ∩ Iic t = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hx
    exact lt_of_lt_of_le ht (hM hx).1
  simp [cdf, this]

lemma cdf_sInf (hM : M ⊆ Icc a b) : cdf M (sInf M) = 0 := by
  have hbdd : BddBelow M := ⟨a, fun x hx => (hM hx).1⟩
  have : M ∩ Iic (sInf M) ⊆ {sInf M} := fun x hx =>
    mem_singleton_iff.2 (le_antisymm hx.2 (csInf_le hbdd hx.1))
  simp [cdf, measure_mono_null this Real.volume_singleton]

lemma cdf_le_sub (hM : M ⊆ Icc a b) {t : ℝ} (ht : a ≤ t) : cdf M t ≤ t - a := by
  have : M ∩ Iic t ⊆ Icc a t := fun x hx => ⟨(hM hx.1).1, hx.2⟩
  have := ENNReal.toReal_mono (b := volume (Icc a t)) (by simp [Real.volume_Icc])
    (measure_mono this)
  rwa [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at this

lemma cdf_of_ge (hM : M ⊆ Icc a b) {t : ℝ} (ht : b ≤ t) : cdf M t = (volume M).toReal := by
  have : M ∩ Iic t = M := inter_eq_left.2 fun x hx => le_trans (hM hx).2 ht
  simp [cdf, this]

/-- **Pressing lemma.**  If `M ⊆ [a, b]` is closed and nonempty and `0 ≤ c ≤ |M|`, then there is
a point `x ∈ M` with `|M ∩ (-∞, x]| = c`. -/
theorem exists_cdf_eq (hMc : IsClosed M) (hM : M ⊆ Icc a b) (hne : M.Nonempty) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ENNReal.ofReal c ≤ volume M) : ∃ x ∈ M, cdf M x = c := by
  have hMm : MeasurableSet M := hMc.measurableSet
  rcases hc0.eq_or_lt with rfl | hpos
  · exact ⟨sInf M, hMc.csInf_mem hne ⟨a, fun x hx => (hM hx).1⟩, cdf_sInf hM⟩
  set S := {t : ℝ | c ≤ cdf M t} with hS_def
  have hS : IsClosed S :=
    isClosed_le continuous_const (lipschitzWith_cdf hM hMm).continuous
  have hSne : S.Nonempty := by
    refine ⟨b, ?_⟩
    simp only [hS_def, mem_setOf_eq, cdf_of_ge hM le_rfl]
    exact (ENNReal.ofReal_le_iff_le_toReal (volume_ne_top_of_subset_Icc hM)).1 hc
  have hSbdd : BddBelow S := by
    refine ⟨a, fun t ht => ?_⟩
    by_contra h
    have := cdf_of_lt hM (not_le.1 h)
    simp only [hS_def, mem_setOf_eq] at ht
    linarith
  set x := sInf S with hx_def
  have hxS : x ∈ S := hS.csInf_mem hSne hSbdd
  have hx_lt : ∀ t, t < x → cdf M t < c := by
    intro t ht
    by_contra h
    exact absurd (csInf_le hSbdd (not_lt.1 h)) (not_le.2 ht)
  have hxM : x ∈ M := by
    by_contra hxM
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hMc.isOpen_compl x hxM
    have hempty : M ∩ Ioc (x - ε / 2) x = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro htM h1 h2
      refine hball ?_ htM
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    have h1 := cdf_eq_of_inter_Ioc_eq_empty hM hMm (by linarith) hempty
    have h2 := hx_lt (x - ε / 2) (by linarith)
    simp only [hS_def, mem_setOf_eq] at hxS
    linarith
  refine ⟨x, hxM, le_antisymm ?_ hxS⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h1 := cdf_le_add hM hMm (x - ε) x
  have h2 := hx_lt (x - ε) (by linarith)
  rw [show x - (x - ε) = ε by ring, abs_of_pos hε] at h1
  linarith

end Remez
