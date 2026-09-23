/-
  # Definitions.lean
  Core shared definitions for the Hermite phase-retrieval scaffold.

  Scaffolding notes:
  - `Basis/first_true_level_basis.md`
  - `Reduction/circle_reduction.md`
  - `BlockDecomposition/block_decomposition.md`

  The goal of this file is only to pin down the common language of the
  development. Proofs come later.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Nat.Dist
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace HermiteLEAN

/-- The weighted inner product on `L²_γ(ℂ)`. -/
def weightedInner (F G : ℂ → ℂ) : ℂ :=
  (1 / Real.pi : ℂ) *
    ∫ z, F z * conj (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ)

/-- The weighted squared norm on `L²_γ(ℂ)`. -/
def weightedNormSq (F : ℂ → ℂ) : ℝ :=
  (1 / Real.pi) * ∫ z, ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)

/-- The weighted norm on `L²_γ(ℂ)`. -/
def weightedNorm (F : ℂ → ℂ) : ℝ := Real.sqrt (weightedNormSq F)














end HermiteLEAN
