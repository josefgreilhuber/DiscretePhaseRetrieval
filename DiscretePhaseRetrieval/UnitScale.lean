import Definitions

/-!
# Unit-scale phase-space objects for the STFT corollary

The formal proofs of `ContinuousPhaseRetrieval/` are carried out with the Hermite functions
`ψ_α(t) ∝ H_α(t) e^{−|t|²/2}`, whose short-time Fourier transforms are functions of the
polyanalytic Fock space (weight `e^{−|z|²}`) in the variable `T(x, ξ) = (x − 2πi ξ)/√2`.  This
file holds the phase-space objects of that *unit scale*: the window `h(t) e^{−|t|²/2}` and the
distance `phaseDistUnit` that makes `T` an isometry.

The public STFT corollary (`STFT.lean`, vocabulary of `Definitions.lean`) is stated, as in the
paper, for the window `h(t) e^{−π|t|²}` and the Euclidean distance of `ℝ^d × ℝ^d`;
`DiscretePhaseRetrieval/Dilation.lean` relates the two by the unitary dilation `t = s/√(2π)` of
`L²(ℝ^d)`, under which `T` becomes `z = √π (x − i ξ)`.
-/

open MeasureTheory

noncomputable section

namespace DiscretePR

variable {d : ℕ}

/-- The distance on phase space `ℝ^d × ℝ^d` under which `(x, ξ) ↦ (x − 2πi ξ)/√2` is an isometry
onto `ℂ^d` with its Euclidean distance `euclideanDist`:
`phaseDistUnit x ξ x' ξ' = ((|x − x'|² + 4π² |ξ − ξ'|²) / 2)^{1/2}`,
i.e. the Euclidean distance in the coordinates `(x/√2, √2 π ξ)`.  This is the map under which the
STFT with a unit-scale Hermite-type window becomes a function of the polyanalytic Fock space. -/
def phaseDistUnit (x ξ x' ξ' : RealVec d) : ℝ :=
  Real.sqrt ((‖x - x'‖ ^ 2 + (2 * Real.pi) ^ 2 * ‖ξ - ξ'‖ ^ 2) / 2)

/-- `ε`-uniformly discrete subsets of phase space for the unit-scale distance `phaseDistUnit`. -/
def UniformlyDiscretePhaseUnit (ε : ℝ) (S : Set (RealVec d × RealVec d)) : Prop :=
  ∀ x ξ, (x, ξ) ∈ S → ∀ x' ξ', (x', ξ') ∈ S → (x, ξ) ≠ (x', ξ') → ε ≤ phaseDistUnit x ξ x' ξ'

/-- The unit-scale window `h(x) e^{−|x|²/2}` of a real polynomial `h` in `d` variables, as an
element of `L²(ℝ^d)`: a finite linear combination of the Hermite functions of
`ContinuousPhaseRetrieval/`.  (The `MemLp` branch is the one taken.) -/
def gaussWindowUnit (h : MvPolynomial (Fin d) ℝ) : L2Real d := by
  classical
  exact if hL2 : MemLp (fun x : RealVec d =>
      ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * Real.exp (-‖x‖ ^ 2 / 2)) 2 volume
    then hL2.toLp _ else 0

end DiscretePR
