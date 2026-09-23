import ContinuousPhaseRetrieval.ModulusRecovery.Hermite1Dimd.ImportedAnalyticInputs
import ContinuousPhaseRetrieval.ModulusRecovery.Hermitek.TrueLevelBasis
import Mathlib.Analysis.Complex.Isometry

set_option linter.style.setOption false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

/-!
# ProductBasisAndAnnuli

Finite several-variable basis infrastructure.
Scaffolding notes: `ScaffoldingNotes/Basis/product_basis_and_annuli.md`.
-/

private lemma integrable_oneDimPhi_cross_gaussian
    (k m n : ℕ) :
    Integrable
      (fun z : CSpace 1 => oneDimPhi k m (z 0) * conj (oneDimPhi k n (z 0)))
      (gaussianMeasure 1) := by
  change
    Integrable
      (fun z : CSpace 1 => HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
      (gaussianMeasure 1)
  rw [gaussianMeasure, ModulusRecovery.gamma_d]
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul']
  · have hcross :
        Integrable
          (fun z : CSpace 1 =>
            HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)) *
              (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
      let e : CSpace 1 ≃ᵐ ℂ := MeasurableEquiv.funUnique (Fin 1) ℂ
      have hcomp :=
        (MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integrable_comp_of_integrable
          (g := fun z : ℂ =>
            HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z) *
              (Real.exp (-‖z‖ ^ 2) : ℂ))
          (HermitekLEAN.integrable_weightedCross k m n)
      simp only [Function.comp_def] at hcomp
      exact hcomp
    have hsmul :
        Integrable
          (fun z : CSpace 1 =>
            Real.exp (-‖z 0‖ ^ 2) •
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      convert hcross using 1
      funext z
      simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    convert hsmul.const_mul (1 / Real.pi) using 1
    · rfl
    funext z
    have hnonneg : 0 ≤ π⁻¹ * rexp (-‖z 0‖ ^ 2) := by
      positivity
    simp [gaussianDensity, ModulusRecovery.gaussianDensity, hnonneg, smul_smul]
    ring
  ·
    change
      Measurable
        (fun z : CSpace 1 =>
          ENNReal.ofReal ((1 / Real.pi ^ 1) * Real.exp (-(∑ q : Fin 1, ‖z q‖ ^ 2))))
    fun_prop
  · simp

private theorem gaussianInner_self
    {d : ℕ} (F : CSpace d → ℂ) :
    gaussianInner F F = ((gaussianL2NormSq F : ℝ) : ℂ) := by
  unfold gaussianInner gaussianL2NormSq
  have hfun :
      (fun z : CSpace d => F z * conj (F z)) =
        fun z : CSpace d => ((‖F z‖ ^ 2 : ℝ) : ℂ) := by
    funext z
    simpa using Complex.mul_conj' (F z)
  rw [hfun, integral_complex_ofReal]

private lemma integrable_productBasis_cross
    {d : ℕ} (κ α β : MultiIndex d) :
    Integrable
      (fun z : CSpace d => PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))
      (gaussianMeasure d) := by
  simpa [PhiKappaAlpha, Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm] using
    (tensorGaussianFactorization d
      (fun q z => oneDimPhi (κ q) (α q) z)
      (fun q z => oneDimPhi (κ q) (β q) z)
      (fun q => by
        simpa [oneDimLift] using
          integrable_oneDimPhi_cross_gaussian (κ q) (α q) (β q))).1

private lemma gaussianInner_finite_sum_basis
    {d : ℕ} (κ β : MultiIndex d)
    (s : Finset (MultiIndex d)) (c : MultiIndex d → ℂ) :
    gaussianInner (fun z => Finset.sum s (fun α => c α * PhiKappaAlpha κ α z)) (PhiKappaAlpha κ β) =
      Finset.sum s (fun α => c α * gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β)) := by
  unfold gaussianInner
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro α hα
    have hconst :
        (∫ z : CSpace d, c α * (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))
            ∂gaussianMeasure d) =
          c α * ∫ z : CSpace d, PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)
            ∂gaussianMeasure d := by
      simpa [mul_assoc] using
        (MeasureTheory.integral_const_mul (c α)
          (fun z : CSpace d => PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)))
    rw [hconst]
  · intro α hα
    simpa [mul_assoc] using (integrable_productBasis_cross κ α β).const_mul (c α)

private lemma gaussianInner_finite_sum
    {d : ℕ} (κ : MultiIndex d)
    (s t : Finset (MultiIndex d)) (a b : MultiIndex d → ℂ) :
    gaussianInner
        (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
        (fun z => Finset.sum t (fun β => b β * PhiKappaAlpha κ β z)) =
      Finset.sum t
        (fun β =>
          conj (b β) *
            gaussianInner
              (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
              (PhiKappaAlpha κ β)) := by
  unfold gaussianInner
  have hfun :
      (fun z : CSpace d =>
        (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
          conj (Finset.sum t (fun β => b β * PhiKappaAlpha κ β z))) =
        fun z : CSpace d =>
          Finset.sum t
            (fun β =>
              conj (b β) *
                ((Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
                  conj (PhiKappaAlpha κ β z))) := by
    funext z
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro β hβ
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hfun, MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro β hβ
    have hconst :
        (∫ z : CSpace d,
            conj (b β) *
              ((Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) * conj (PhiKappaAlpha κ β z))
            ∂gaussianMeasure d) =
          conj (b β) *
            ∫ z : CSpace d,
              (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) * conj (PhiKappaAlpha κ β z)
              ∂gaussianMeasure d := by
      simpa [mul_assoc] using
        (MeasureTheory.integral_const_mul (conj (b β))
          (fun z : CSpace d =>
            (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) * conj (PhiKappaAlpha κ β z)))
    rw [hconst]
  · intro β hβ
    have hsumInt :
        Integrable
          (fun z : CSpace d =>
            (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
              conj (PhiKappaAlpha κ β z))
          (gaussianMeasure d) := by
      rw [show (fun z : CSpace d =>
            (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
              conj (PhiKappaAlpha κ β z)) =
          (fun z : CSpace d =>
            Finset.sum s (fun α => a α * (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)))) by
            funext z
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro α hα
            ring]
      refine MeasureTheory.integrable_finset_sum _ ?_
      intro α hα
      simpa [mul_assoc] using (integrable_productBasis_cross κ α β).const_mul (a α)
    simpa [mul_assoc] using (hsumInt.const_mul (conj (b β)))





/-- Product basis orthonormality at fixed multi-index `κ`. -/
theorem productBasisOrthonormal
    {d : ℕ} (κ α β : MultiIndex d) :
    gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β) =
      if α = β then (1 : ℂ) else 0 := by
  /-
  Key scaffolding step:
  use tensor-product factorization and the imported one-variable orthonormality
  theorem coordinate by coordinate.
  -/
  have hfactor := tensorGaussianFactorization d
    (fun q z => oneDimPhi (κ q) (α q) z)
    (fun q z => oneDimPhi (κ q) (β q) z)
    (fun q => by
      simpa [oneDimLift] using
        integrable_oneDimPhi_cross_gaussian (κ q) (α q) (β q))
  have hprod :
      (∏ q : Fin d,
          gaussianInner (d := 1) (fun z : CSpace 1 => oneDimPhi (κ q) (α q) (z 0))
            (fun z : CSpace 1 => oneDimPhi (κ q) (β q) (z 0))) =
        if α = β then (1 : ℂ) else 0 := by
    by_cases h : α = β
    · subst h
      have hcoord :
          ∀ q : Fin d,
            gaussianInner (d := 1) (fun z : CSpace 1 => oneDimPhi (κ q) (α q) (z 0))
              (fun z : CSpace 1 => oneDimPhi (κ q) (α q) (z 0)) = 1 := by
        intro q
        have h1 := oneVariableBasisOrthonormal (k := κ q) (m := α q) (n := α q)
        rw [if_pos rfl] at h1
        exact h1
      simp [hcoord]
    · obtain ⟨q, hq⟩ : ∃ q : Fin d, α q ≠ β q := by
        simpa [funext_iff] using h
      rw [if_neg h, Finset.prod_eq_zero_iff]
      refine ⟨q, Finset.mem_univ q, ?_⟩
      have h1 := oneVariableBasisOrthonormal (k := κ q) (m := α q) (n := β q)
      rw [if_neg hq] at h1
      exact h1
  exact hfactor.2.trans hprod


/-- Finite Parseval for a finite several-variable Hermite sum. -/
theorem finiteParseval
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteNormSq κ G = Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 := by
  /-
  Scaffolding guidance:
  keep the public statement on literal finite coefficient families.
  This is the version later files regroup by blocks and total degree.
  -/
  classical
  have hinner :
      gaussianInner (evalHermiteSum κ G) (evalHermiteSum κ G) =
        Finset.sum G.support fun α => G.coeff α * conj (G.coeff α) := by
    unfold evalHermiteSum
    rw [gaussianInner_finite_sum (κ := κ) (s := G.support) (t := G.support)
      (a := G.coeff) (b := G.coeff)]
    calc
      ∑ β ∈ G.support,
          conj (G.coeff β) *
            gaussianInner (fun z => ∑ α ∈ G.support, G.coeff α * PhiKappaAlpha κ α z)
              (PhiKappaAlpha κ β)
          = ∑ β ∈ G.support,
              conj (G.coeff β) *
                ∑ α ∈ G.support, G.coeff α * gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β) := by
                  refine Finset.sum_congr rfl ?_
                  intro β hβ
                  rw [gaussianInner_finite_sum_basis (κ := κ) (β := β)
                    (s := G.support) (c := G.coeff)]
      _ = ∑ β ∈ G.support, conj (G.coeff β) * G.coeff β := by
            refine Finset.sum_congr rfl ?_
            intro β hβ
            rw [Finset.sum_eq_single β]
            · simp [productBasisOrthonormal]
            · intro α hα hne
              simp [productBasisOrthonormal, hne]
            · intro hnotin
              exact False.elim (hnotin hβ)
      _ = ∑ α ∈ G.support, G.coeff α * conj (G.coeff α) := by
            refine Finset.sum_congr rfl ?_
            intro α hα
            ring
  unfold hermiteNormSq
  have hsq : gaussianL2NormSq (evalHermiteSum κ G) = Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 := by
    apply Complex.ofReal_injective
    calc
      (((gaussianL2NormSq (evalHermiteSum κ G) : ℝ)) : ℂ)
          = gaussianInner (evalHermiteSum κ G) (evalHermiteSum κ G) := by
              symm
              exact gaussianInner_self (F := evalHermiteSum κ G)
      _ = ∑ α ∈ G.support, G.coeff α * conj (G.coeff α) := hinner
      _ = (((Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 : ℝ)) : ℂ) := by
            simp [Complex.mul_conj']
  simpa using hsq
























end Hermite1DimdLEAN
