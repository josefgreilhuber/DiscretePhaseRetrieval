import VCInequality.Defs
import VCInequality.Sauer
import VCInequality.Swap
import VCInequality.Rademacher
import VCInequality.Dichotomy
import VCInequality.Symmetrization
import VCInequality.Binomial.Main

/-!
# The relative Vapnik–Chervonenkis inequality

Assembly:
* If `m ε² < 1` the bound is trivial: the left side is `≤ 1` and `8 G exp(−mε²/4) ≥ 8 e^{−1/4} G`,
  with `G ≥ 1` when `ι` is nonempty (a nonempty family has at least one trace; `X` is nonempty
  because `μ` is a probability measure) and the left side `0` when `ι` is empty.
* Otherwise `symmetrization` with `c = 1/8` (`binomial_bound`), then
  `doubleMeasure_real_le_of_swap_avg` with the pointwise bound `swap_avg_le`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace VCInequality

variable {X : Type*} [MeasurableSpace X]

/-- **Relative Vapnik–Chervonenkis inequality** (Vapnik–Chervonenkis 1974, Appendix Thm 1). -/
theorem relative_deviation (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Countable ι]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) (m : ℕ) {G : ℝ}
    (hG : IsGrowthBound (Set.range A) (2 * m) G) {ε : ℝ} (hε : 0 < ε) :
    (sampleMeasure μ m).real (badEvent μ A m ε) ≤ 8 * G * Real.exp (-(m * ε ^ 2) / 4) := by
  classical
  -- `X` is nonempty because `μ` is a probability measure, so we may evaluate `hG`.
  have hXne : Nonempty X := Measure.nonempty_of_neZero μ
  have hG0 : 0 ≤ G := by
    refine le_trans ?_ (hG (fun _ ↦ Classical.arbitrary X))
    positivity
  rcases le_or_gt 1 ((m : ℝ) * ε ^ 2) with hmε | hmε
  · -- Main case: symmetrization, then the swap-averaging bound.
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; norm_num at hmε
      · exact h
    have h1 := symmetrization μ A hA m hε hmε (c := 1 / 8) (by norm_num)
      (fun B hB hpB ↦ binomial_bound μ m hm hB hpB)
    have h2 := doubleMeasure_real_le_of_swap_avg μ (measurableSet_symEvent hA m ε)
      (K := G * Real.exp (-(m * ε ^ 2) / 4)) (fun z ↦ swap_avg_le A m hG hε z)
    calc (sampleMeasure μ m).real (badEvent μ A m ε)
        ≤ (1 / 8 : ℝ)⁻¹ * (doubleMeasure μ m).real (symEvent A m ε) := h1
      _ ≤ (1 / 8 : ℝ)⁻¹ * (G * Real.exp (-(m * ε ^ 2) / 4)) := by gcongr
      _ = 8 * G * Real.exp (-(m * ε ^ 2) / 4) := by ring
  · -- Trivial case `m ε² < 1`: the right-hand side is at least `6 G ≥ 1`.
    have hexp : (3 : ℝ) / 4 ≤ Real.exp (-(m * ε ^ 2) / 4) := by
      have h1 : (3 : ℝ) / 4 ≤ Real.exp (-(1 : ℝ) / 4) := by
        have := Real.add_one_le_exp (-(1 : ℝ) / 4)
        linarith
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      linarith
    rcases isEmpty_or_nonempty ι with hι | hι
    · -- No sets at all: the bad event is empty.
      have hemp : badEvent μ A m ε = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
        obtain ⟨i, -⟩ := hx
        exact isEmptyElim i
      rw [hemp, measureReal_empty]
      have := Real.exp_pos (-(m * ε ^ 2) / 4)
      nlinarith
    · -- At least one set: its trace witnesses `G ≥ 1`.
      have hG1 : (1 : ℝ) ≤ G := by
        obtain ⟨i₀⟩ := hι
        refine le_trans ?_ (hG (fun _ ↦ Classical.arbitrary X))
        have key : ∀ f : Set X → Set (Fin (2 * m)),
            (1 : ℝ) ≤ (((f '' Set.range A)).ncard : ℝ) := by
          intro f
          have hne : ((f '' Set.range A)).Nonempty := ⟨f (A i₀), ⟨A i₀, ⟨i₀, rfl⟩, rfl⟩⟩
          have hpos : 0 < ((f '' Set.range A)).ncard :=
            (Set.ncard_pos (Set.toFinite _)).mpr hne
          exact_mod_cast hpos
        exact key _
      calc (sampleMeasure μ m).real (badEvent μ A m ε) ≤ 1 := measureReal_le_one
        _ ≤ 8 * G * Real.exp (-(m * ε ^ 2) / 4) := by
            have h6 : (1 : ℝ) * (3 / 4) ≤ G * Real.exp (-(m * ε ^ 2) / 4) :=
              mul_le_mul hG1 hexp (by norm_num) (by linarith)
            linarith

/-- Sauer–Shelah form, for a family of VC dimension `≤ V`, `1 ≤ V ≤ 2m`. -/
theorem relative_deviation_vc (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Countable ι]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) (m V : ℕ) (hV : 1 ≤ V) (hmV : V ≤ 2 * m)
    (hvc : VCDimLE (Set.range A) V) {ε : ℝ} (hε : 0 < ε) :
    (sampleMeasure μ m).real (badEvent μ A m ε)
      ≤ 8 * (Real.exp 1 * (2 * m) / V) ^ V * Real.exp (-(m * ε ^ 2) / 4) := by
  have hG := isGrowthBound_of_vcDimLE hvc hV hmV (𝒢 := Set.range A)
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [hcast] at hG
  exact relative_deviation μ A hA m hG hε

end VCInequality
