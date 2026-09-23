import ContinuousPhaseRetrieval.ModulusRecovery.Hermite1Dimd.Definitions
import Mathlib.MeasureTheory.Integral.Pi
import ContinuousPhaseRetrieval.ModulusRecovery.Hermitek.TrueLevelBasis

set_option linter.style.setOption false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

def oneDimLift (f : ℂ → ℂ) : CSpace 1 → ℂ := fun z => f (z 0)








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
    have hnonneg : 0 ≤ π⁻¹ * rexp (-‖z 0‖ ^ 2) := by positivity
    simp [gaussianDensity, ModulusRecovery.gaussianDensity, hnonneg, smul_smul]
    ring
  ·
    change
      Measurable
        (fun z : CSpace 1 =>
          ENNReal.ofReal ((1 / Real.pi ^ 1) * Real.exp (-(∑ q : Fin 1, ‖z q‖ ^ 2))))
    fun_prop
  · simp

private theorem gaussianInner_oneDimPhi_eq_weightedInner
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      HermitekLEAN.weightedInner (HermitekLEAN.Phi k m) (HermitekLEAN.Phi k n) := by
  change
    gaussianInner (d := 1) (fun z => HermitekLEAN.Phi k m (z 0))
      (fun z => HermitekLEAN.Phi k n (z 0)) =
      HermitekLEAN.weightedInner (HermitekLEAN.Phi k m) (HermitekLEAN.Phi k n)
  unfold gaussianInner HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  rw [gaussianMeasure, ModulusRecovery.gamma_d]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun z : CSpace 1 => ENNReal.ofReal (gaussianDensity 1 z)) by
      unfold gaussianDensity ModulusRecovery.gaussianDensity
      fun_prop)
    (show ∀ᵐ x : CSpace 1, ENNReal.ofReal (gaussianDensity 1 x) < ⊤ by
      filter_upwards with x
      simp)]
  have hEq :
      ∫ (x : CSpace 1),
          HermitekLEAN.Phi k m ((MeasurableEquiv.funUnique (Fin 1) ℂ) x) *
            ((Real.exp (-‖(MeasurableEquiv.funUnique (Fin 1) ℂ) x‖ ^ 2) : ℂ) *
              conj (HermitekLEAN.Phi k n ((MeasurableEquiv.funUnique (Fin 1) ℂ) x)))
            ∂(volume : Measure (CSpace 1)) =
        ∫ z : ℂ,
          HermitekLEAN.Phi k m z *
            ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
            ∂(volume : Measure ℂ) := by
    let e : CSpace 1 ≃ᵐ ℂ := MeasurableEquiv.funUnique (Fin 1) ℂ
    have hEq0 :=
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
        (f := e)
        (fun z : ℂ =>
          HermitekLEAN.Phi k m z *
            ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))))
    convert hEq0 using 1 <;> rfl
  have hcomp :
        ∫ z : CSpace 1,
            HermitekLEAN.Phi k m (z 0) *
              ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0)))
              ∂(volume : Measure (CSpace 1)) =
          ∫ z : ℂ,
            HermitekLEAN.Phi k m z *
              ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
              ∂(volume : Measure ℂ) := by
    convert hEq using 1 <;> rfl
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
          ∂(volume : Measure (CSpace 1))
        =
      ∫ z : CSpace 1,
        ((1 / Real.pi : ℂ) *
          ((HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
            (Real.exp (-‖z 0‖ ^ 2) : ℂ))) ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          have hdens :
              (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
                (1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) := by
            have hnonneg : 0 ≤ Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by
              positivity
            simp [gaussianDensity, ModulusRecovery.gaussianDensity, hnonneg]
          rw [Algebra.smul_def, hdens]
          have hcast :
              (algebraMap ℝ ℂ) ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) =
                ((1 / Real.pi : ℂ) * (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
            simp
          calc
            (algebraMap ℝ ℂ) ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) *
                (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
                =
              ((1 / Real.pi : ℂ) * (Real.exp (-‖z 0‖ ^ 2) : ℂ)) *
                (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) := by
                  rw [hcast]
            _ =
              (1 / Real.pi : ℂ) *
                ((HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                  (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
                    ring
    _ =
      (1 / Real.pi : ℂ) *
        ∫ z : CSpace 1,
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
            (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) := by
            have hconst :
                ∫ z : CSpace 1,
                  (1 / Real.pi : ℂ) *
                    ((HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                      (Real.exp (-‖z 0‖ ^ 2) : ℂ)) =
                (1 / Real.pi : ℂ) *
                  ∫ z : CSpace 1,
                    (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                      (Real.exp (-‖z 0‖ ^ 2) : ℂ) := by
                exact
                  (MeasureTheory.integral_const_mul
                    (μ := (volume : Measure (CSpace 1)))
                    (1 / Real.pi : ℂ)
                    (fun z : CSpace 1 =>
                      (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                        (Real.exp (-‖z 0‖ ^ 2) : ℂ)))
            simpa using hconst
    _ = (1 / Real.pi : ℂ) *
        ∫ z : ℂ,
          (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
            (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := by
          have hcomp' : ∫ z : CSpace 1,
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) =
              ∫ z : ℂ,
                (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
                  (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := by
            have hleft :
                ∫ z : CSpace 1,
                  (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                    (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) =
                  ∫ z : CSpace 1,
                    HermitekLEAN.Phi k m (z 0) *
                      ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0)))
                      ∂(volume : Measure (CSpace 1)) := by
                  apply integral_congr_ae
                  filter_upwards with z
                  ring
            have hright :
                ∫ z : ℂ,
                  (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
                    (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) =
                  ∫ z : ℂ,
                    HermitekLEAN.Phi k m z *
                      ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
                      ∂(volume : Measure ℂ) := by
                  apply integral_congr_ae
                  filter_upwards with z
                  ring
            calc
              ∫ z : CSpace 1,
                  (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                    (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1))
                  =
                ∫ z : CSpace 1,
                  HermitekLEAN.Phi k m (z 0) *
                    ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0)))
                    ∂(volume : Measure (CSpace 1)) := hleft
              _ = ∫ z : ℂ,
                    HermitekLEAN.Phi k m z *
                      ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
                      ∂(volume : Measure ℂ) := hcomp
              _ =
                ∫ z : ℂ,
                  (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
                    (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := hright.symm
          rw [hcomp']


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




/-- Imported one-variable basis orthonormality at fixed true-Hermite level. -/
theorem oneVariableBasisOrthonormal
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      if m = n then (1 : ℂ) else 0 := by
  /-
  Scaffolding guidance:
  re-export the frozen one-dimensional basis theorem under a stable name.
  Downstream files only use orthonormality and finite Parseval consequences.
  -/
  rw [gaussianInner_oneDimPhi_eq_weightedInner]
  simpa using (HermitekLEAN.phi_orthonormal (k := k) (m := m) (n := n))











/-- Gaussian density splits into first-coordinate and tail factors. -/
private lemma gaussianDensity_succ_split
    (d : ℕ) (z : CSpace (d + 1)) :
    gaussianDensity (d + 1) z =
      gaussianDensity 1 (fun _ : Fin 1 => z 0) *
        gaussianDensity d (fun q : Fin d => z (Fin.succ q)) := by
  unfold gaussianDensity ModulusRecovery.gaussianDensity
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one]
  rw [pow_succ, neg_add, Real.exp_add]
  field_simp [Real.pi_pos.ne']

/-- Gaussian density factors pointwise into one-dimensional densities. -/
private lemma gaussianDensity_eq_prod
    (d : ℕ) (z : CSpace d) :
    gaussianDensity d z =
      ∏ q : Fin d, gaussianDensity 1 (fun _ : Fin 1 => z q) := by
  induction d with
  | zero =>
      simp [gaussianDensity, ModulusRecovery.gaussianDensity]
  | succ d ih =>
      rw [gaussianDensity_succ_split]
      rw [ih]
      rw [Fin.prod_univ_succ]

private lemma integrable_weighted_coord_of_integrable_gaussian
    (f g : ℂ → ℂ)
    (hfg :
      Integrable
        (fun z : CSpace 1 => f (z 0) * conj (g (z 0)))
        (gaussianMeasure 1)) :
    Integrable
      (fun z : ℂ =>
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z)))
      (volume : Measure ℂ) := by
  have hsmul :
      Integrable
        (fun z : CSpace 1 =>
          (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
            (f (z 0) * conj (g (z 0))))
        (volume : Measure (CSpace 1)) := by
    rw [gaussianMeasure, ModulusRecovery.gamma_d] at hfg
    exact
      (integrable_withDensity_iff_integrable_smul'
        (show Measurable (fun z : CSpace 1 => ENNReal.ofReal (gaussianDensity 1 z)) by
          unfold gaussianDensity ModulusRecovery.gaussianDensity
          fun_prop)
        (show ∀ᵐ x : CSpace 1, ENNReal.ofReal (gaussianDensity 1 x) < ⊤ by
          filter_upwards with x
          simp)).1 hfg
  let e : ℂ ≃ᵐ CSpace 1 := (MeasurableEquiv.funUnique (Fin 1) ℂ).symm
  have hcomp :
      Integrable
        (fun z : ℂ =>
          (ENNReal.ofReal (gaussianDensity 1 (e z))).toReal •
            (f ((e z) 0) * conj (g ((e z) 0))))
        (volume : Measure ℂ) := by
    simpa [e, Function.comp_def] using
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).symm.integrable_comp_of_integrable
        (g := fun z : CSpace 1 =>
          (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
            (f (z 0) * conj (g (z 0))))
        hsmul)
  convert hcomp using 1
  ext z
  have hdens :
      (ENNReal.ofReal (gaussianDensity 1 (e z))).toReal =
        (1 / Real.pi) * Real.exp (-‖z‖ ^ 2) := by
    have hnonneg' : 0 ≤ π⁻¹ * Real.exp (-‖z‖ ^ 2) := by
      positivity
    simpa [e, gaussianDensity, ModulusRecovery.gaussianDensity] using (ENNReal.toReal_ofReal hnonneg')
  rw [hdens]
  simp [e, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]

private theorem gaussianInner_oneDim_eq_weighted_coord
    (f g : ℂ → ℂ) :
    gaussianInner (d := 1) (fun z : CSpace 1 => f (z 0)) (fun z : CSpace 1 => g (z 0)) =
      ∫ z : ℂ,
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z))
        ∂(volume : Measure ℂ) := by
  unfold gaussianInner
  rw [gaussianMeasure, ModulusRecovery.gamma_d]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun z : CSpace 1 => ENNReal.ofReal (gaussianDensity 1 z)) by
      unfold gaussianDensity ModulusRecovery.gaussianDensity
      fun_prop)
    (show ∀ᵐ x : CSpace 1, ENNReal.ofReal (gaussianDensity 1 x) < ⊤ by
      filter_upwards with x
      simp)]
  let e : CSpace 1 ≃ᵐ ℂ := MeasurableEquiv.funUnique (Fin 1) ℂ
  have hEq :
      ∫ x : CSpace 1,
          (((1 / Real.pi) * Real.exp (-‖x 0‖ ^ 2) : ℝ) : ℂ) *
            (f (x 0) * conj (g (x 0)))
          ∂(volume : Measure (CSpace 1)) =
        ∫ z : ℂ,
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
            (f z * conj (g z))
          ∂(volume : Measure ℂ) := by
    have hEq0 :=
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
        (f := e)
        (fun z : ℂ =>
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
            (f z * conj (g z))))
    convert hEq0 using 1 <;> rfl
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (f (z 0) * conj (g (z 0)))
        ∂(volume : Measure (CSpace 1)) =
      ∫ z : CSpace 1,
        (((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
          (f (z 0) * conj (g (z 0)))
        ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          have hnonneg : 0 ≤ π⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by
            positivity
          have hdens :
              (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
                (1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) := by
            simpa [gaussianDensity, ModulusRecovery.gaussianDensity] using (ENNReal.toReal_ofReal hnonneg)
          rw [hdens]
          simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ z : ℂ,
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z))
        ∂(volume : Measure ℂ) := hEq

private lemma density_prod_identity
    (d : ℕ) (F G : Fin d → ℂ → ℂ) (z : CSpace d) :
    (gaussianDensity d z : ℂ) *
        ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q))) =
      ∏ q : Fin d,
        ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
          (F q (z q) * conj (G q (z q)))) := by
  rw [gaussianDensity_eq_prod]
  simp [gaussianDensity, ModulusRecovery.gaussianDensity, Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]

/-- Tensor-product factorization over the Gaussian product measure. -/
theorem tensorGaussianFactorization
    (d : ℕ) (F G : Fin d → ℂ → ℂ)
    (hFG :
      ∀ q : Fin d,
        Integrable
            (fun z : CSpace 1 => F q (z 0) * conj (G q (z 0)))
            (gaussianMeasure 1)) :
    Integrable
        (fun z : CSpace d => ∏ q : Fin d, F q (z q) * conj (G q (z q)))
        (gaussianMeasure d) ∧
      gaussianInner (d := d) (fun z => ∏ q : Fin d, F q (z q)) (fun z => ∏ q : Fin d, G q (z q)) =
        ∏ q : Fin d,
          gaussianInner (d := 1) (fun z : CSpace 1 => F q (z 0)) (fun z : CSpace 1 => G q (z 0)) := by
  have hcoord :
      ∀ q : Fin d,
        Integrable
          (fun z : ℂ =>
            (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
              (F q z * conj (G q z)))
          (volume : Measure ℂ) := by
    intro q
    exact integrable_weighted_coord_of_integrable_gaussian (F q) (G q) (hFG q)
  have hprod_volume :
      Integrable
        (fun z : CSpace d =>
          ∏ q : Fin d,
            ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
              (F q (z q) * conj (G q (z q)))))
        (volume : Measure (CSpace d)) := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Integrable.fintype_prod hcoord
  have hintegrable :
      Integrable
        (fun z : CSpace d => ∏ q : Fin d, F q (z q) * conj (G q (z q)))
        (gaussianMeasure d) := by
    rw [gaussianMeasure, ModulusRecovery.gamma_d]
    rw [MeasureTheory.integrable_withDensity_iff_integrable_smul']
    · convert hprod_volume using 1
      · rfl
      funext z
      have hnonneg : 0 ≤ gaussianDensity d z := by
        unfold gaussianDensity ModulusRecovery.gaussianDensity
        positivity
      calc
        (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
            ∏ q : Fin d, F q (z q) * conj (G q (z q))) =
          (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
            ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q)))) := by
              simp [Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]
        _ = (gaussianDensity d z : ℂ) *
              ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q))) := by
              rw [show (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ)) =
                  gaussianDensity d z by
                simp [ENNReal.toReal_ofReal hnonneg]]
        _ = ∏ q : Fin d,
              ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
                (F q (z q) * conj (G q (z q)))) := density_prod_identity d F G z
    ·
      change Measurable (fun z : CSpace d => ENNReal.ofReal (gaussianDensity d z))
      unfold gaussianDensity ModulusRecovery.gaussianDensity
      fun_prop
    ·
      filter_upwards with x
      simp
  constructor
  · exact hintegrable
  · unfold gaussianInner
    rw [gaussianMeasure, ModulusRecovery.gamma_d]
    rw [integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun z : CSpace d => ENNReal.ofReal (gaussianDensity d z)) by
        unfold gaussianDensity ModulusRecovery.gaussianDensity
        fun_prop)
      (show ∀ᵐ x : CSpace d, ENNReal.ofReal (gaussianDensity d x) < ⊤ by
        filter_upwards with x
        simp)]
    calc
      ∫ z : CSpace d,
          (ENNReal.ofReal (gaussianDensity d z)).toReal •
            ((fun z => ∏ q : Fin d, F q (z q)) z *
              conj ((fun z => ∏ q : Fin d, G q (z q)) z))
          ∂(volume : Measure (CSpace d)) =
        ∫ z : CSpace d,
          (ENNReal.ofReal (gaussianDensity d z)).toReal •
            (∏ q : Fin d, F q (z q) * conj (G q (z q)))
          ∂(volume : Measure (CSpace d)) := by
            apply integral_congr_ae
            filter_upwards with z
            simp [Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∫ z : CSpace d,
          ∏ q : Fin d,
            ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
              (F q (z q) * conj (G q (z q))))
          ∂(volume : Measure (CSpace d)) := by
            apply integral_congr_ae
            filter_upwards with z
            have hnonneg : 0 ≤ gaussianDensity d z := by
              unfold gaussianDensity ModulusRecovery.gaussianDensity
              positivity
            calc
              (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
                  ∏ q : Fin d, F q (z q) * conj (G q (z q))) =
                (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
                  ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q)))) := by
                    simp [Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]
              _ = (gaussianDensity d z : ℂ) *
                    ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q))) := by
                    rw [show (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ)) =
                        gaussianDensity d z by
                      simp [ENNReal.toReal_ofReal hnonneg]]
              _ = ∏ q : Fin d,
                    ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
                      (F q (z q) * conj (G q (z q)))) := density_prod_identity d F G z
      _ =
        ∫ z : CSpace d,
          ∏ q : Fin d,
            ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
              (F q (z q) * conj (G q (z q))))
          ∂(volume : Measure (CSpace d)) := by
            rfl
      _ = ∫ z : CSpace d,
            ∏ q : Fin d,
              (fun q : Fin d => fun z : ℂ =>
                ((((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
                  (F q z * conj (G q z)))) q (z q)
            ∂(volume : Measure (CSpace d)) := by
              rfl
      _ = ∏ q : Fin d,
            ∫ z : ℂ,
              (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
                (F q z * conj (G q z))
              ∂(volume : Measure ℂ) := by
              rw [MeasureTheory.volume_pi]
              exact
                MeasureTheory.integral_fintype_prod_eq_prod
                  (fun q : Fin d => fun z : ℂ =>
                    ((((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
                      (F q z * conj (G q z))))
      _ = ∏ q : Fin d,
            gaussianInner (d := 1) (fun z : CSpace 1 => F q (z 0))
              (fun z : CSpace 1 => G q (z 0)) := by
            apply Finset.prod_congr rfl
            intro q hq
            symm
            exact gaussianInner_oneDim_eq_weighted_coord (F q) (G q)

end Hermite1DimdLEAN
