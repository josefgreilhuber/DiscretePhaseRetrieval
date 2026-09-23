import Mathlib
import VCInequality.Defs
import PolyFock.Fock.Basic

/-!
# Proposition 2.1 (discrete norming inequality) — definitions

Points of `ℂ^d` are represented as `Pt d = EuclideanSpace ℝ (Fin (2 * d))`, with complex
coordinates `toC x j = x j + i · x (j + d)`. For `F, G ∈ ℂ[z, z̄]` (`PolyFock.Fock.P d`, evaluated
by `PolyFock.Fock.ev`), `diff F G x = |F(z)|² − |G(z)|²` (real-valued). `hull Ω` is the closed
convex hull. The uniform probability measure on `Ω` is `unif Ω = volume[|Ω]`.

See `PLAN-DiscreteNorming.md` and `CLAIMS.md` for the claim-by-claim map.
-/

open MeasureTheory Metric

namespace DiscreteNorming

/-- The ambient real space `ℝ^{2d}` with the Euclidean metric. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin (2 * d))

/-- Complex coordinates of a real point: `toC x j = x j + i · x (j + d)`. -/
def toC {d : ℕ} (x : Pt d) : Fin d → ℂ :=
  fun j ↦ ⟨x ⟨j, by omega⟩, x ⟨j + d, by omega⟩⟩

/-- `|F(z)|² − |G(z)|²` as a real function of `x ∈ ℝ^{2d}`. -/
noncomputable def diff {d : ℕ} (F G : PolyFock.Fock.P d) (x : Pt d) : ℝ :=
  ‖PolyFock.Fock.ev (toC x) F‖ ^ 2 - ‖PolyFock.Fock.ev (toC x) G‖ ^ 2

/-- Linear combination `∑ a_j φ_j` of polynomials with complex coefficients. -/
noncomputable def comb {d N : ℕ} (φ : Fin N → PolyFock.Fock.P d) (a : Fin N → ℂ) :
    PolyFock.Fock.P d :=
  ∑ j, MvPolynomial.C (a j) * φ j

/-- A Gaussian rational `p + q i`. -/
def gaussRat (a : ℚ × ℚ) : ℂ := (a.1 : ℂ) + (a.2 : ℂ) * Complex.I

/-- Combination with Gaussian-rational coefficients. -/
noncomputable def ratComb {d N : ℕ} (φ : Fin N → PolyFock.Fock.P d) (a : Fin N → ℚ × ℚ) :
    PolyFock.Fock.P d :=
  comb φ (fun j ↦ gaussRat (a j))

/-- The closed convex hull `Ω̂` (compact for bounded `Ω`). -/
def hull {d : ℕ} (Ω : Set (Pt d)) : Set (Pt d) := closure (convexHull ℝ Ω)

/-- Lebesgue measure as a real number (Mathlib's `MeasureTheory.Measure.real`). -/
noncomputable abbrev vol {d : ℕ} (Ω : Set (Pt d)) : ℝ := volume.real Ω

/-- Volume `|B^{2d}|` of the Euclidean unit ball. -/
noncomputable def unitBallVol (d : ℕ) : ℝ := (volume (ball (0 : Pt d) 1)).toReal

/-- The uniform probability measure on `Ω`. -/
noncomputable def unif {d : ℕ} (Ω : Set (Pt d)) : Measure (Pt d) := ProbabilityTheory.cond volume Ω

/-- Lemma 2.2's family: superlevel sets `{z ∈ Ω : ||F(z)|² − |G(z)|²| ≥ τ}`, `F, G ∈ 𝒱`, `τ > 0`. -/
def superlevelFamily {d : ℕ} (Ω : Set (Pt d)) (𝒱 : Submodule ℂ (PolyFock.Fock.P d)) :
    Set (Set (Pt d)) :=
  {A | ∃ F ∈ 𝒱, ∃ G ∈ 𝒱, ∃ τ : ℝ, 0 < τ ∧ A = {x ∈ Ω | τ ≤ |diff F G x|}}

/-- Index set of the countable subfamily: Gaussian-rational coefficient vectors for `F` and `G`
(with respect to a spanning family of `𝒱`) and a positive rational threshold. -/
abbrev RatIndex (N : ℕ) := (Fin N → ℚ × ℚ) × (Fin N → ℚ × ℚ) × {τ : ℚ // 0 < τ}

/-- The countable subfamily of `superlevelFamily`. -/
def ratFamily {d N : ℕ} (Ω : Set (Pt d)) (φ : Fin N → PolyFock.Fock.P d) (i : RatIndex N) :
    Set (Pt d) :=
  {x ∈ Ω | ((i.2.2 : ℚ) : ℝ) ≤ |diff (ratComb φ i.1) (ratComb φ i.2.1) x|}

/-- The Remez parameter `θ = (t|Ω| + |Ω̂ \ Ω|)/|Ω̂|`. -/
noncomputable def theta {d : ℕ} (Ω : Set (Pt d)) (t : ℝ) : ℝ :=
  (t * vol Ω + vol (hull Ω \ Ω)) / vol (hull Ω)

/-- The sample size `M = ⌊(3000 + 1200 |log t|) N / t⌋`. -/
noncomputable def sampleSize (t : ℝ) (N : ℕ) : ℕ := ⌊(3000 + 1200 * |Real.log t|) * N / t⌋₊

/-- The separation radius `δ N^{−1/(2d)} = (t|Ω| / (2M|B^{2d}|))^{1/(2d)}` of the proof. -/
noncomputable def sepRadius (d : ℕ) (Ω : Set (Pt d)) (t : ℝ) (N : ℕ) : ℝ :=
  (t * vol Ω / (2 * sampleSize t N * unitBallVol d)) ^ (1 / (2 * d : ℝ))

/-- The paper's explicit `δ = (1/16) (|Ω|/|B^{2d}| / (3·10⁵(1+d)))^{1/(2d)}`. -/
noncomputable def deltaPaper (d : ℕ) (Ω : Set (Pt d)) : ℝ :=
  (1 / 16) * (vol Ω / unitBallVol d / (3 * 10 ^ 5 * (1 + d))) ^ (1 / (2 * d : ℝ))

/-- Number of `r`-close pairs `i < j` in a sample. -/
noncomputable def closePairs {d M : ℕ} (r : ℝ) (x : Fin M → Pt d) : ℕ := by
  classical exact (Finset.univ.filter fun p : Fin M × Fin M ↦ p.1 < p.2 ∧ dist (x p.1) (x p.2) < r).card

end DiscreteNorming
