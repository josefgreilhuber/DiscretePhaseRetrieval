import Mathlib

/-!
# Comparator challenge: discrete phase retrieval in polyanalytic Fock spaces

This standalone challenge imports only Mathlib.  It presents the Hermite--Fock
result and its short-time Fourier transform counterpart in the notation of
polynomial Gaussian windows.

The comparator deliberately keeps the function space concrete.  Its members
are exactly the functions having an explicit square-summable expansion in the
mixed basis.  This is the coefficient model used by the formal proof.
-/

open MeasureTheory Nat Finset Lp InnerProductSpace FourierTransform
open scoped lp

noncomputable section

namespace DiscretePR_Showcase

variable {d : ℕ}

/-- Complex Euclidean `d`-space. -/
notation "ℂ^[" d "]" => EuclideanSpace ℂ (Fin d)

notation "ℝ^[" d "]" => EuclideanSpace ℝ (Fin d)
notation "ℕ^[" d "]" => Fin d → ℕ
notation "L²(" α ", " E ")" => Lp E 2 (volume : Measure α)
notation:100 R "[" ι "]" => MvPolynomial ι R

/-- A real Euclidean vector regarded coordinatewise as a complex one. -/
instance {d : ℕ} : Coe (ℝ^[d]) (ℂ^[d]) where
  coe x := WithLp.toLp 2 fun i => (x i : ℂ)

end DiscretePR_Showcase

namespace EuclideanSpace

/-- The coordinatewise real part of a complex Euclidean vector. -/
def re {d : ℕ} (z : ℂ^[d]) : ℝ^[d] := WithLp.toLp 2 fun i => (z i).re

/-- The coordinatewise imaginary part of a complex Euclidean vector. -/
def im {d : ℕ} (z : ℂ^[d]) : ℝ^[d] := WithLp.toLp 2 fun i => (z i).im

end EuclideanSpace

namespace DiscretePR_Showcase

/-! ## Basic definitions -/

/-- Distinct points of `S` are separated by at least `ε`. -/
def UniformlyDiscrete {X : Type*} [MetricSpace X] (ε : ℝ) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε ≤ dist x y

/-- Equality of samples in modulus determines functions up to a global complex scalar. -/
def PhaseRetrievalSet {X : Type*} (F : Set (X → ℂ)) (S : Set X) : Prop :=
  ∀ f ∈ F, ∀ g ∈ F,
    (∀ s ∈ S, ‖f s‖ = ‖g s‖) → ∃ θ : ℂ, f = θ • g

/-! ## Weighted polyanalytic spaces -/

/-- The normalized one-variable Hermite--Fock basis polynomial
`φ_{m,n}(z,z̄)`.  The first index is the coefficient index and the second is
the Landau level. -/
def HermitePoly (m n : ℕ) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) : ℂ)⁻¹) *
    ∑ r ∈ range (min m n + 1),
      ((-1 : ℂ) ^ r) * (Nat.factorial r : ℂ) *
        (choose m r : ℂ) * (choose n r : ℂ) *
        z ^ (m - r) * (star z) ^ (n - r)

/-- The `d`-variable tensor-product basis element. -/
def Φ (n q : ℕ^[d]) (z : ℂ^[d]) : ℂ :=
  ∏ i, HermitePoly (n i) (q i) (z i)

/-- The normalized mixed-level basis element associated with `h`. -/
def Ψ (h : ℂ[Fin d]) (n : ℕ^[d]) (z : ℂ^[d]) : ℂ :=
  (((Real.sqrt (∑' q, ‖h.coeff q‖ ^ 2)) : ℂ)⁻¹) *
    ∑' q, h.coeff q * Φ n q z

/-- The functions with a square-summable mixed Hermite--Fock expansion. -/
def PolyFockSpace (h : ℂ[Fin d]) : Set (ℂ^[d] → ℂ) :=
  {f | ∃ w : ℓ^2(ℕ^[d], ℂ), f = fun z => ∑' n, w n * Ψ h n z}

/-! ## Main result -/

/-- Every nonzero polynomial Gaussian window admits a uniformly discrete phase-retrieval set. -/
theorem DiscretePhaseRetrieval
    (d : ℕ) (h : ℂ[Fin d]) (hnonzero : h ≠ 0) :
    ∃ S : Set ℂ^[d],
      UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧
        PhaseRetrievalSet (PolyFockSpace h) S := by
  sorry

/-! ## Short-time Fourier transform -/

/-- The modulation--translation operator on `L²(ℝ^d)`.

This pointwise representative is equivalent to conjugating a frequency-domain translation by
Mathlib's `L²` Fourier transform, but makes the STFT convention explicit and directly usable. -/
def timeFreqShift {d : ℕ} (x ξ : ℝ^[d]) (f : L²(ℝ^[d], ℂ)) : L²(ℝ^[d], ℂ) := by
  classical
  exact if hL2 : MemLp (fun t : ℝ^[d] =>
      Complex.exp ((2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ t : ℝ) : ℂ)) *
        (f : ℝ^[d] → ℂ) (t - x)) 2 volume then
    hL2.toLp _
  else 0

/-- The short-time Fourier transform with window `g`. -/
def STFT {d : ℕ} (g f : L²(ℝ^[d], ℂ)) : ℂ^[d] → ℂ :=
  fun z => ⟪timeFreqShift z.re z.im g, f⟫_ℂ

/-- The polynomial--Gaussian window `h(x)e^{-‖x‖²}`. -/
def window (h : ℂ[Fin d]) : ℝ^[d] → ℂ :=
  fun x => Real.exp (-‖x‖ ^ 2) * h.eval (x : ℂ^[d])

/-- The polynomial--Gaussian window as an `L²` vector.

The fallback branch keeps this definition independent of the subsequent integrability challenge;
`window_MemLp` proves that the first branch is always selected. -/
def windowL2 (h : ℂ[Fin d]) : L²(ℝ^[d], ℂ) := by
  classical
  exact if hL2 : MemLp (window h) 2 volume then hL2.toLp (window h) else 0

/-- A polynomial times the Gaussian belongs to `L²(ℝ^d)`. -/
lemma window_MemLp {d : ℕ} (h : ℂ[Fin d]) :
    MemLp (window h) 2 volume := by
  sorry

/-- The range of the STFT with the polynomial--Gaussian window. -/
def STFTspace (h : ℂ[Fin d]) : Set (ℂ^[d] → ℂ) :=
  Set.range (STFT (windowL2 h))

/-- Discrete phase retrieval for the polynomial-window STFT.

The separation is `√d / 10⁷`: the Fourier convention in `timeFreqShift` and the window
`e^{-‖x‖²}` introduce an anisotropic phase-space scaling, so the Hermite separation constant
`4√d / 10⁷` weakens by the elementary estimate `π ≤ 4`. -/
theorem STFTPhaseRetrieval
    (d : ℕ) (h : ℂ[Fin d]) (hnonzero : h ≠ 0) :
    ∃ S : Set ℂ^[d],
      UniformlyDiscrete (Real.sqrt d / 10 ^ 7) S ∧
        PhaseRetrievalSet (STFTspace h) S := by
  sorry

end DiscretePR_Showcase
