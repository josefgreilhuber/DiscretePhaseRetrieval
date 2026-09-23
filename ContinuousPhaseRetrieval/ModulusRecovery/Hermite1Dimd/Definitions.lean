import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ContinuousPhaseRetrieval.ModulusRecovery.Hermite.Definitions
import ContinuousPhaseRetrieval.ModulusRecovery.Hermitek.TrueLevelBasis
import ContinuousPhaseRetrieval.ModulusRecovery.Definitions

open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace Hermite1DimdLEAN

abbrev CSpace := ModulusRecovery.Cd
abbrev MultiIndex := ModulusRecovery.MultiIndex

/-- The Gaussian weight; the same function as `ModulusRecovery.gaussianDensity`
(see `plans/DUPLICATES.md`, item 4.4). -/
abbrev gaussianDensity := ModulusRecovery.gaussianDensity

/-- The Gaussian measure; the same measure as `ModulusRecovery.gamma_d`. -/
abbrev gaussianMeasure := ModulusRecovery.gamma_d

/-- The one-dimensional level-`k` Hermite basis vector; the same function as
`HermitekLEAN.Phi` (see `plans/DUPLICATES.md`, item 4.3). -/
noncomputable def oneDimPhi (k n : ℕ) : ℂ → ℂ := HermitekLEAN.Phi k n

def PhiKappaAlpha {d : ℕ} (κ α : MultiIndex d) : CSpace d → ℂ :=
  fun z => ∏ q : Fin d, oneDimPhi (κ q) (α q) (z q)


def gaussianL2NormSq {d : ℕ} {α : Type*} [Norm α] (F : CSpace d → α) : ℝ :=
  ∫ z, ‖F z‖ ^ 2 ∂ gaussianMeasure d


def gaussianInner {d : ℕ} (F G : CSpace d → ℂ) : ℂ :=
  ∫ z, F z * conj (G z) ∂ gaussianMeasure d



structure FiniteHermiteSum (d : ℕ) where
  coeff : MultiIndex d →₀ ℂ

def FiniteHermiteSum.support {d : ℕ} (G : FiniteHermiteSum d) : Finset (MultiIndex d) :=
  G.coeff.support

def evalHermiteSum {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : CSpace d → ℂ :=
  fun z => Finset.sum G.support fun α => G.coeff α * PhiKappaAlpha κ α z



def hermiteNormSq {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (evalHermiteSum κ G)











































end Hermite1DimdLEAN
