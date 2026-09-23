import Mathlib

/-!
# Relative Vapnik–Chervonenkis inequality — definitions

Target (Vapnik–Chervonenkis 1974, Appendix Theorem 1; Cortes–Greenberg–Mohri 2019, Thm 5 with
`α = 2`): for a probability measure `μ`, a countable family `A i` of measurable sets whose
growth function on `2m` points is at most `G`, and `ε > 0`,

    μ^{⊗m} { x | ∃ i, ε < (μ (A i) − ν_x (A i)) / √(μ (A i)) } ≤ 8 · G · exp (−m ε² / 4),

where `ν_x A = #{j | x j ∈ A} / m` is the empirical frequency.

Conventions: Lean's `x / 0 = 0` and `√0 = 0` make the relative deviation `0` when `μ (A i) = 0`,
which is the right convention (such a set never violates the bound), so no regularising `τ` is
needed.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace VCInequality

variable {X : Type*} [MeasurableSpace X]

/-- Number of sample points of `x` lying in `A`. -/
noncomputable def count {m : ℕ} (x : Fin m → X) (A : Set X) : ℕ := by
  classical exact (univ.filter fun i ↦ x i ∈ A).card

/-- Empirical frequency `count x A / m`. -/
noncomputable def empFreq {m : ℕ} (x : Fin m → X) (A : Set X) : ℝ := (count x A : ℝ) / m

/-- The sample measure `μ^{⊗ m}` on `Fin m → X`. -/
noncomputable abbrev sampleMeasure (μ : Measure X) (m : ℕ) : Measure (Fin m → X) :=
  Measure.pi fun _ ↦ μ

/-- The double-sample measure `(μ ⊗ μ)^{⊗ m}` on `Fin m → X × X`. -/
noncomputable abbrev doubleMeasure (μ : Measure X) (m : ℕ) : Measure (Fin m → X × X) :=
  Measure.pi fun _ ↦ μ.prod μ

/-- First half of a double sample. -/
def fstSample {m : ℕ} (z : Fin m → X × X) : Fin m → X := fun i ↦ (z i).1

/-- Second half of a double sample. -/
def sndSample {m : ℕ} (z : Fin m → X × X) : Fin m → X := fun i ↦ (z i).2

/-- Relative deviation `(μ A − ν_x A) / √(μ A)` of the empirical frequency from the probability. -/
noncomputable def relDev (μ : Measure X) {m : ℕ} (x : Fin m → X) (A : Set X) : ℝ :=
  (μ.real A - empFreq x A) / Real.sqrt (μ.real A)

/-- Symmetrized relative deviation `(ν₂ − ν₁) / √((ν₁ + ν₂)/2)` between the two halves. -/
noncomputable def symDev {m : ℕ} (z : Fin m → X × X) (A : Set X) : ℝ :=
  (empFreq (sndSample z) A - empFreq (fstSample z) A)
    / Real.sqrt ((empFreq (fstSample z) A + empFreq (sndSample z) A) / 2)

/-- Swap the two halves at the coordinates where `σ` is `true`. -/
def swap {m : ℕ} (σ : Fin m → Bool) (z : Fin m → X × X) : Fin m → X × X :=
  fun i ↦ if σ i then (z i).swap else z i

/-- The bad event for the sample: some set of the family has relative deviation `> ε`. -/
def badEvent (μ : Measure X) {ι : Type*} (A : ι → Set X) (m : ℕ) (ε : ℝ) :
    Set (Fin m → X) :=
  {x | ∃ i, ε < relDev μ x (A i)}

/-- The symmetrized bad event for the double sample. -/
def symEvent {ι : Type*} (A : ι → Set X) (m : ℕ) (ε : ℝ) : Set (Fin m → X × X) :=
  {z | ∃ i, ε < symDev z (A i)}

/-- `G` bounds the number of traces of `𝒢` on every `n`-point sample (growth function). -/
def IsGrowthBound (𝒢 : Set (Set X)) (n : ℕ) (G : ℝ) : Prop :=
  ∀ x : Fin n → X, (((fun A ↦ {i | x i ∈ A}) '' 𝒢).ncard : ℝ) ≤ G

/-- VC dimension at most `V`: no finset of more than `V` points is shattered by `𝒢`. -/
def VCDimLE (𝒢 : Set (Set X)) (V : ℕ) : Prop :=
  ∀ s : Finset X, (∀ t ⊆ s, ∃ A ∈ 𝒢, ∀ y ∈ s, y ∈ A ↔ y ∈ t) → s.card ≤ V

/-- The binomial pmf term `C(m,j) p^j (1−p)^{m−j}`, i.e. the summand of `binTail`. -/
noncomputable def binPmf (m : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)

lemma binPmf_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m j : ℕ) :
    0 ≤ binPmf m p j :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _)) (pow_nonneg (by linarith) _)

/-- Tail of the binomial distribution: `P[Bin(m,p) ≥ k]`. -/
noncomputable def binTail (m k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Icc k m, binPmf m p j

/-- Uniform random signs on `Fin m → Bool`. -/
noncomputable abbrev signMeasure (m : ℕ) : Measure (Fin m → Bool) := uniformOn Set.univ

end VCInequality
