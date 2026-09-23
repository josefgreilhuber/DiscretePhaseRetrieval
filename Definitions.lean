import Mathlib

/-!
# Definitions: discrete phase retrieval in mixed-level polyanalytic Fock spaces

This file imports only Mathlib and contains every definition the statements of the main theorem
(`Main.lean`) and of its STFT corollary (`STFT.lean`) use, with the indexing of the paper.  The
comparator `Showcase.lean` states the result in the equivalent vocabulary of polynomial weights
and `EuclideanSpace ℂ (Fin d)`; `Check.lean` proves the transport to that statement.  The last
section (phase space, `L²(ℝ^d)`, the short-time Fourier transform, the polynomial–Gaussian window)
serves only `STFT.lean`.

* a point is a vector `z : Fin d → ℂ`;
* `HermitePoly m n` is the explicit normalized one-variable complex Hermite
  basis polynomial `φ_{m,n}(z, z̄)` of the paper (`m` the coefficient index,
  `n` the Landau level), and `Φ n q` is its `d`-fold tensor product
  `Φ_{n,q}`;
* a family of level weights is a finitely supported `h : (Fin d → ℕ) →₀ ℂ`
  (the paper's finite sequence `h` with `h_q = 0` for `|q| > L`), and
  `Ψ n h` is the normalized mixture `Ψ_{n,h}` of the `Φ_{n,q}` over the
  levels `q` in the support of `h`;
* `γ` is the product Gaussian measure on `Fin d → ℂ`;
* the polyanalytic Fock space `PolyFockSpace h` (the paper's `𝓕_h`)
  is described in function-space language: the classical Gaussian `L²` and
  continuity conditions, together with an explicit `ℓ²` coefficient
  representation witness in the basis `Ψ · h`;
* samples are ordinary pointwise absolute values on a uniformly discrete set.

The final conjunct of `PolyFockSpace` is the
formal bridge to the coefficient model used by the Lean proof.  Mathematically
it is the basis-expansion witness for an element of the closed span of
`{Ψ n h}` in the Gaussian `L²` space: the `Φ_{n,q}` are orthonormal in
`L²(γ)` over all pairs `(n, q)`, so for fixed `h ≠ 0` the `Ψ_{n,h}` are
orthonormal in `n`, and for square-summable coefficients the series converges
absolutely at every point, so pointwise sampling is meaningful.

Uniform discreteness is stated for the Euclidean metric on `ℂ^d`, the one used
in the paper; `euclideanDist` spells it out, so no change of ambient type is
needed.  The separation is quantified: `UniformlyDiscrete ε` takes it as an
explicit argument.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace DiscretePR

/-! ## Explicit Hermite-Fock basis -/

/-- The normalized one-variable Hermite-Fock basis polynomial `φ_{m,n}(z, z̄)`
of the paper,
`φ_{m,n}(z, z̄) = (m! n!)^{-1/2} ∑_{r=0}^{min(m,n)} (-1)^r r! C(m,r) C(n,r) z^{m-r} z̄^{n-r}`.

The first index `m` is the coefficient index (the power of `z`), the second
index `n` is the Hermite (Landau) level (the power of `z̄`).  Lean's
`Finset.range N` is the finite set `{0, ..., N - 1}`, so
`Finset.range (min m n + 1)` indexes exactly `r = 0, ..., min m n`, matching the
inclusive upper limit in the paper formula. -/
def HermitePoly (m n : ℕ) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) : ℂ)⁻¹) *
    ∑ r ∈ Finset.range (min m n + 1),
      ((-1 : ℂ) ^ r) * (Nat.factorial r : ℂ) *
        (Nat.choose m r : ℂ) * (Nat.choose n r : ℂ) *
        z ^ (m - r) * (star z) ^ (n - r)

variable {d : ℕ}

/-- The `d`-variable basis element `Φ_{n,q}(z, z̄) = ∏ᵢ φ_{nᵢ,qᵢ}(zᵢ, z̄ᵢ)` of the
paper: `n` is the coefficient multi-index, `q` the Landau level. -/
def Φ (n q : Fin d → ℕ) (z : Fin d → ℂ) : ℂ :=
  ∏ i : Fin d, HermitePoly (n i) (q i) (z i)

/-! ## Mixed-level basis -/

/-- The normalized mixed-level basis element of the paper,
`Ψ_{n,h}(z, z̄) = (∑_{|q| ≤ L} |h_q|²)^{-1/2} ∑_{|q| ≤ L} h_q Φ_{n,q}(z, z̄)`,
for a finite family of level weights `h`.

`h : (Fin d → ℕ) →₀ ℂ` is a finitely supported function on the multi-indices
(Mathlib's `Finsupp`); this is the paper's finite sequence `h` with `h_q = 0`
for `|q| > L`.  Since `h` vanishes off its support `h.support` (a `Finset`),
both sums over `|q| ≤ L` in the paper formula equal the sums over `h.support`
written here, and no bound `L` needs to be named.  For `h ≠ 0` the
normalization makes `Ψ_{n,h}` a unit vector of `L²(γ)`; for the single-level
weight `h = Finsupp.single q 1` one gets `Ψ_{n,h} = Φ_{n,q}`. -/
def Ψ (n : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) (z : Fin d → ℂ) : ℂ :=
  (((Real.sqrt (∑ q ∈ h.support, ‖h q‖ ^ 2)) : ℂ)⁻¹) *
    ∑ q ∈ h.support, h q * Φ n q z

/-! ## Gaussian measure -/

/-- The real-valued Gaussian density on `Fin d → ℂ`. -/
def gaussianDensity (z : Fin d → ℂ) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-Finset.sum Finset.univ fun i : Fin d => ‖z i‖ ^ 2)

/-- The product Gaussian measure on `Fin d → ℂ`. -/
def γ : MeasureTheory.Measure (Fin d → ℂ) :=
  MeasureTheory.volume.withDensity fun z => ENNReal.ofReal (gaussianDensity z)

/-! ## Coefficient model and pointwise evaluation -/

/-- The coefficient Hilbert space used by the formal proof: square-summable
coefficient families indexed by the multi-indices `Fin d → ℕ`. -/
abbrev PolyFock (d : ℕ) : Type :=
  lp (fun _ : (Fin d → ℕ) => ℂ) 2

/-- Coefficient access. -/
def coeff (F : PolyFock d) (n : Fin d → ℕ) : ℂ :=
  F n

/-- The function represented by a coefficient vector for the level weights
`h`: the pointwise sum of the coefficient series against the basis `Ψ · h`. -/
def polyanalyticEval (h : (Fin d → ℕ) →₀ ℂ) (F : PolyFock d) (z : Fin d → ℂ) : ℂ :=
  ∑' n : Fin d → ℕ, coeff F n * Ψ n h z

/-! ## The function-space polyanalytic Fock space -/

/-- The function-space polyanalytic Fock space `𝓕_h` of the level weights `h`
used by the comparator: the `L²(γ)`-closure of the span of the basis
polynomials `Ψ_{n,h}`, `n ∈ ℕ^d`.

The first two conjuncts are the classical Gaussian `L²` and regularity
conditions.  The third conjunct is the explicit coefficient representation
witness that connects this public function-space statement to the coefficient
model in which the Lean proof is carried out.  For `h = Finsupp.single q 1`
this is the true polyanalytic Fock space `𝓕^d_q` at Landau level `q`. -/
def PolyFockSpace (h : (Fin d → ℕ) →₀ ℂ) : Set ((Fin d → ℂ) → ℂ) :=
  { f | MemLp f 2 γ ∧ Continuous f ∧
      ∃ F : PolyFock d, f = polyanalyticEval h F }

/-! ## Sampling notions -/

/-- The Euclidean distance on `ℂ^d = Fin d → ℂ`, written out explicitly.  This
is the metric in which the paper measures separation; the ambient type keeps
its default (sup-metric) instances, which are not used here. -/
def euclideanDist (x y : Fin d → ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin d, ‖x i - y i‖ ^ 2)

/-- A set is `ε`-uniformly discrete if distinct points are at Euclidean
distance at least `ε` from each other.  The separation `ε` is an explicit
parameter, so a statement using this predicate quantifies how spread out the
set is. -/
def UniformlyDiscrete (ε : ℝ) (S : Set (Fin d → ℂ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε ≤ euclideanDist x y

/--
`S` is a phase-retrieval set for a function class `F` if equality of sampled
absolute values on `S` forces equality up to one global unit complex phase.
-/
def PhaseRetrievalSet {X : Type*} (F : Set (X → ℂ)) (S : Set X) : Prop :=
  ∀ f ∈ F, ∀ g ∈ F,
    (∀ s ∈ S, ‖f s‖ = ‖g s‖) →
      ∃ θ : ℂ, ‖θ‖ = 1 ∧ f = θ • g

/-! ## Phase space and the short-time Fourier transform (for the corollary `STFT.lean`) -/

/-- `ℝ^d` with its Euclidean norm. -/
abbrev RealVec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `L²(ℝ^d)`: complex-valued square-integrable functions on `ℝ^d` modulo equality almost
everywhere (Mathlib's `Lp`). -/
abbrev L2Real (d : ℕ) := Lp ℂ 2 (volume : Measure (RealVec d))

/-- The short-time Fourier transform of `f ∈ L²(ℝ^d)` with window `w ∈ L²(ℝ^d)` at the
phase-space point `(x, ξ) ∈ ℝ^d × ℝ^d` (`x` the position, `ξ` the frequency):
`V_w f(x, ξ) = ∫ f(t) conj(w(t − x)) e^{−2πi ξ·t} dt`. -/
def stft (w f : L2Real d) (x ξ : RealVec d) : ℂ :=
  ∫ t : RealVec d,
    (f : RealVec d → ℂ) t * star ((w : RealVec d → ℂ) (t - x)) *
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ t : ℝ) : ℂ))

/-- A subset of phase space `ℝ^d × ℝ^d` is `ε`-uniformly discrete if distinct points `(x, ξ)`,
`(x', ξ')` are at Euclidean distance `(|x − x'|² + |ξ − ξ'|²)^{1/2}` at least `ε` from each other
(the analogue of `UniformlyDiscrete`, which is stated for subsets of `ℂ^d`). -/
def UniformlyDiscretePhase (ε : ℝ) (S : Set (RealVec d × RealVec d)) : Prop :=
  ∀ x ξ, (x, ξ) ∈ S → ∀ x' ξ', (x', ξ') ∈ S → (x, ξ) ≠ (x', ξ') →
    ε ≤ Real.sqrt (‖x - x'‖ ^ 2 + ‖ξ - ξ'‖ ^ 2)

/-- The window `h(x) e^{−π|x|²}` of a real polynomial `h` in `d` variables, as an element of
`L²(ℝ^d)`: the Gaussian normalisation of time-frequency analysis, matching the kernel
`e^{−2πi ξ·t}` of `stft`.  With it, `z = √π (x − i ξ)` carries the STFT to the polyanalytic Fock
space of the main theorem (weight `e^{−|z|²}`), so separations in phase space are those of `ℂ^d`
divided by `√π`.  (A polynomial times a Gaussian is square-integrable, so the `MemLp` branch is
the one taken; the `if` only keeps this file free of proofs.) -/
def gaussWindow (h : MvPolynomial (Fin d) ℝ) : L2Real d := by
  classical
  exact if hL2 : MemLp (fun x : RealVec d =>
      ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * Real.exp (-Real.pi * ‖x‖ ^ 2)) 2 volume
    then hL2.toLp _ else 0

end DiscretePR
