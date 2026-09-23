/-
  # TrueLevelBasis.lean
  WIP merged implementation for the true Hermite level `k` basis.

  Scaffolding notes:
  - `Basis/true_level_basis.md`

  This file now carries the previously split circle and bridge API directly.
-/
import ContinuousPhaseRetrieval.ModulusRecovery.Hermite.Definitions
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open Complex MeasureTheory Real Finset
open scoped BigOperators Topology

noncomputable section

namespace HermitekLEAN

-- This merged basis proof file carries a large amount of mechanically stable proof script.
-- Suppress repetitive local lint classes here rather than bloating the file with one-off rewrites.
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedDecidableInType false
set_option linter.flexible false
set_option linter.style.longLine false


abbrev weightedInner := HermiteLEAN.weightedInner
abbrev weightedNormSq := HermiteLEAN.weightedNormSq
abbrev weightedNorm := HermiteLEAN.weightedNorm


/--
The true Hermite basis vector at level `k`, written directly as the explicit
finite `z`/`conj z` expansion used downstream.

The raising/lowering-operator derivation is only bookkeeping motivation; the
public API stays explicit and finitary.
-/
noncomputable def Phi : ℕ → ℕ → ℂ → ℂ := fun k n z =>
  ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
    Finset.sum (Finset.range (min k n + 1)) (fun j =>
      ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
        z ^ (n - j) * (star z) ^ (k - j))

/-- The closed span of the true Hermite level-`k` basis.

  An element `G` belongs to `Hk k` when its canonical Hermite-coefficient
  expansion converges pointwise to `G` and its weighted square norm is
  integrable. Equivalently, `Hk k` is the weighted-`L²` closure of
  `span {Φₖ,ₙ}` together with the pointwise Hermite expansion data. -/
def Hk (k : ℕ) : Set (ℂ → ℂ) :=
  {G | Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ∧
      ∀ z, HasSum (fun n => weightedInner G (Phi k n) * Phi k n z) (G z)}

/-- A finite Hermite sum `sum_{n < D} a_n Phi_{k,n}`. -/
def finiteHermiteSum (k : ℕ) {D : ℕ} (a : Fin D → ℂ) : ℂ → ℂ :=
  fun z => ∑ n : Fin D, a n * Phi k n.1 z


/-- The canonical coefficient extractor for the true level basis. -/
def hermiteCoeff (k : ℕ) (G : ℂ → ℂ) (n : ℕ) : ℂ :=
  weightedInner G (Phi k n)

/-- The partial Hermite sum with the first `J + 1` canonical coefficients of `G`. -/
def truncate (k J : ℕ) (G : ℂ → ℂ) : ℂ → ℂ :=
  finiteHermiteSum k (fun n : Fin (J + 1) => hermiteCoeff k G n.1)











/-- Radial integral: ∫_ℂ ‖z‖^{2a} exp(-‖z‖²) = π a!. -/
private lemma integral_norm_pow_exp_gaussian (a : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2) = π * (Nat.factorial a : ℝ) := by
  have h_rpow : ∀ z : ℂ, (‖z‖ : ℝ) ^ (2 * a) = ‖z‖ ^ ((2 * a : ℕ) : ℝ) := by
    intro z; exact (rpow_natCast ‖z‖ (2 * a)).symm
  have h_exp : ∀ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.exp (-‖z‖ ^ (2 : ℝ)) := by
    intro z; norm_num
  simp_rw [h_rpow, h_exp]
  rw [show ((2 * a : ℕ) : ℝ) = ((2 * a : ℕ) : ℝ) from rfl]
  rw [Complex.integral_rpow_mul_exp_neg_rpow (show (1 : ℝ) ≤ 2 from by linarith)
    (show (-2 : ℝ) < ((2 * a : ℕ) : ℝ) from by
      have : (0 : ℝ) ≤ ((2 * a : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)]
  rw [show ((2 * a : ℕ) : ℝ) + 2 = 2 * ((a : ℝ) + 1) from by push_cast; ring]
  rw [show 2 * ((a : ℝ) + 1) / 2 = (a : ℝ) + 1 from by ring]
  rw [show 2 * π / 2 = π from by ring]
  rw [Real.Gamma_nat_eq_factorial]


/-- Explicit finite expansion for the true Hermite basis vector `Phi k n`. -/
theorem phi_explicit :
    ∀ {k n : ℕ} {z : ℂ},
      Phi k n z =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
          Finset.sum (Finset.range (min k n + 1)) (fun j =>
            ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
              ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              z ^ (n - j) * (star z) ^ (k - j)) := by
  intro k n z
  rfl

















/-- Unit circle power factorization: ω^{p-j} * conj(ω)^{k-j} = ω^p * conj(ω)^k when |ω|=1. -/
private lemma circle_pow_factor (ω : _root_.Circle) {j k p : ℕ} (hjk : j ≤ k) (hjp : j ≤ p) :
    (ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j) =
      (ω : ℂ) ^ p * star (ω : ℂ) ^ k := by
  have hωconj : (ω : ℂ) * star (ω : ℂ) = 1 := by
    rw [star_def]
    rw [show (starRingEnd ℂ) (ω : ℂ) = ↑(ω⁻¹ : _root_.Circle) from
      (_root_.Circle.coe_inv_eq_conj ω).symm]
    rw [← _root_.Circle.coe_mul, mul_inv_cancel, _root_.Circle.coe_one]
  have key : ((ω : ℂ) * star (ω : ℂ)) ^ j = 1 := by rw [hωconj]; simp
  rw [mul_pow] at key
  conv_rhs => rw [← Nat.sub_add_cancel hjp, ← Nat.sub_add_cancel hjk, pow_add, pow_add]
  rw [show (ω : ℂ) ^ (p - j) * (ω : ℂ) ^ j * (star (ω : ℂ) ^ (k - j) * star (ω : ℂ) ^ j) =
    (ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j) * ((ω : ℂ) ^ j * star (ω : ℂ) ^ j) from by ring]
  rw [key, mul_one]

/-- Equivariance of Phi under rotation: Phi k p (ω*z) = ω^p * conj(ω)^k * Phi k p z
for any unit complex number ω. -/
private lemma Phi_rotation_equivariant (ω : _root_.Circle) (z : ℂ) (k p : ℕ) :
    Phi k p ((ω : ℂ) * z) = (ω : ℂ) ^ p * star (ω : ℂ) ^ k * Phi k p z := by
  simp only [Phi, mul_pow, star_mul, map_pow]
  -- Both sides have the same structure. We convert to a termwise equality.
  -- Reduce to termwise equality: for each j, the j-th LHS summand = j-th RHS summand
  -- after pulling ω^p * star(ω)^k through the normalization constant and sum.
  -- Strategy: multiply both sides by √(k!p!) to cancel the denominator, then compare termwise.
  -- Actually, just show the two sides are equal directly:
  suffices h : ∀ j ∈ Finset.range (min k p + 1),
      (-1 : ℂ) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
        ((ω : ℂ) ^ (p - j) * z ^ (p - j)) * (star z ^ (k - j) * star (ω : ℂ) ^ (k - j)) =
      (ω : ℂ) ^ p * star (ω : ℂ) ^ k *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) by
    have hsum := Finset.sum_congr rfl h
    rw [← Finset.mul_sum] at hsum
    -- hsum: ∑ LHS_terms = ω^p * star(ω)^k * ∑ RHS_terms
    -- Goal: C * ∑ LHS = ω^p * star(ω)^k * (C * ∑ RHS)
    linear_combination (1 / ↑(Real.sqrt (↑k.factorial * ↑p.factorial))) * hsum
  intro j hj
  have hjk : j ≤ k := by simp [Finset.mem_range] at hj; omega
  have hjp : j ≤ p := by simp [Finset.mem_range] at hj; omega
  have key := circle_pow_factor ω hjk hjp
  -- Replace ω^{p-j} * star(ω)^{k-j} by ω^p * star(ω)^k, then ring
  calc (-1 : ℂ) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
        ((ω : ℂ) ^ (p - j) * z ^ (p - j)) * (star z ^ (k - j) * star (ω : ℂ) ^ (k - j))
      = ((ω : ℂ) ^ (p - j) * star (ω : ℂ) ^ (k - j)) *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) := by ring
    _ = ((ω : ℂ) ^ p * star (ω : ℂ) ^ k) *
        ((-1) ^ j * ↑(k.choose j) * (↑p.factorial / ↑(p - j).factorial) *
          z ^ (p - j) * star z ^ (k - j)) := by rw [key]

/-! ## Helpers for the diagonal case of phi_orthonormal -/


private lemma alternating_vandermonde_coeff_poly (k s N : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      ((((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s * Polynomial.X ^ k).coeff N) := by
  let A : Polynomial ℤ := (Polynomial.C (1 : ℤ)) + Polynomial.X
  have hinner :
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) =
        Polynomial.X ^ k := by
    let f : ℕ → Polynomial ℤ := fun j =>
      A ^ j * (-1 : Polynomial ℤ) ^ (k - j) * Polynomial.C (k.choose j : ℤ)
    calc
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) =
          ∑ j ∈ Finset.range (k + 1), f ((k + 1) - 1 - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjk : j ≤ k := by simpa [Finset.mem_range] using hj
            have hsub : k - (k - j) = j := by omega
            simp [f, A, hsub, smul_eq_mul, Nat.choose_symm hjk, mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ j ∈ Finset.range (k + 1), f j := Finset.sum_range_reflect f (k + 1)
      _ = (A + (-1 : Polynomial ℤ)) ^ k := by
            symm
            simpa [f, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
              (add_pow A (-1 : Polynomial ℤ) k)
      _ = Polynomial.X ^ k := by
            simp [A, add_assoc, add_left_comm, add_comm]
  have hpoly :
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k + s - j))) =
        A ^ s * Polynomial.X ^ k := by
    calc
      ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k + s - j))) =
          ∑ j ∈ Finset.range (k + 1),
            A ^ s * ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k - j))) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : j ≤ k := by simpa [Finset.mem_range] using hj
              have hsub : k + s - j = s + (k - j) := by omega
              calc
                ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k + s - j))) =
                    ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (s + (k - j)))) := by
                      simp [hsub]
                _ = ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ s * A ^ (k - j))) := by
                      simp [pow_add]
                _ = A ^ s * ((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k - j))) := by
                      simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = A ^ s * ∑ j ∈ Finset.range (k + 1), (((-1 : ℤ) ^ j * ↑(k.choose j)) • (A ^ (k - j))) := by
            rw [Finset.mul_sum]
      _ = A ^ s * Polynomial.X ^ k := by rw [hinner]
  have hpolycoeff :
      ∑ j ∈ Finset.range (k + 1),
          (((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k + s - j))).coeff N) =
        (A ^ s * Polynomial.X ^ k).coeff N := by
    simpa using congrArg (fun p : Polynomial ℤ => p.coeff N) hpoly
  have hsum :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      (A ^ s * Polynomial.X ^ k).coeff N := by
    refine Eq.trans ?_ hpolycoeff
    apply Finset.sum_congr rfl
    intro j hj
    have hcs : (((((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) • (A ^ (k + s - j))).coeff N)
        = (((-1 : ℤ) ^ j * ↑(k.choose j)) : ℤ) * ((A ^ (k + s - j)).coeff N) :=
      (Polynomial.coeff_smul _ _ _).trans (smul_eq_mul _ _)
    rw [hcs]
    simp [A, Polynomial.coeff_one_add_X_pow, mul_assoc, mul_left_comm, mul_comm]
  simpa [A] using hsum

private lemma alternating_vandermonde_coeff (k s N : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
      if k ≤ N then ↑(s.choose (N - k)) else 0 := by
  calc
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) * ↑((k + s - j).choose N) =
        ((((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s * Polynomial.X ^ k).coeff N) :=
      alternating_vandermonde_coeff_poly k s N
    _ = if k ≤ N then (((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s).coeff (N - k) else 0 := by
          simpa using
            (Polynomial.coeff_mul_X_pow' (((Polynomial.C (1 : ℤ)) + Polynomial.X) ^ s) k N)
    _ = if k ≤ N then ↑(s.choose (N - k)) else 0 := by
          by_cases h : k ≤ N <;> simp [h, Polynomial.coeff_one_add_X_pow]


private theorem alternating_vandermonde_zero (k s : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑((k + s - j).choose k) = 1 := by
  simpa [if_pos (Nat.le_refl k)] using alternating_vandermonde_coeff k s k

private theorem alternating_vandermonde_vanish (k s r : ℕ) (hr : r < k) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑((k + s - j).choose r) = 0 := by
  simpa [if_neg (Nat.not_le_of_lt hr)] using alternating_vandermonde_coeff k s r

/-! ## Double-sum identity for phi_orthonormal diagonal case -/

-- Factoring: descFact(m, j) * (m+k-i-j)! = m! * C(m+k-i-j, k-i) * (k-i)!
private lemma desc_fact_mul_fact (k m i j : ℕ) (hi : i ≤ k) (hj : j ≤ m) :
    Nat.descFactorial m j * Nat.factorial (m + k - i - j) =
    Nat.factorial m * Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i) := by
  have hki : k - i ≤ m + k - i - j := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hki
  have hsubt : m + k - i - j - (k - i) = m - j := by omega
  rw [hsubt] at h1
  have h2 := Nat.factorial_mul_descFactorial hj
  calc Nat.descFactorial m j * Nat.factorial (m + k - i - j)
      = Nat.descFactorial m j * (Nat.choose (m + k - i - j) (k - i) *
          Nat.factorial (k - i) * Nat.factorial (m - j)) := by rw [h1]
    _ = (Nat.factorial (m - j) * Nat.descFactorial m j) *
          (Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i)) := by ring
    _ = Nat.factorial m *
          (Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i)) := by rw [h2]
    _ = Nat.factorial m * Nat.choose (m + k - i - j) (k - i) * Nat.factorial (k - i) := by ring

-- Inner sum factoring for fixed i
-- Note: we prove the SUM equality, not per-term equality (which fails when j > m and i = k)
-- The proof repeatedly refactors the inner binomial sum across two disjoint index ranges.
private lemma inner_sum_factor (k m i : ℕ) (hi : i ≤ k) (him : i ≤ m) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j)) =
    ↑(Nat.factorial m) * ↑(Nat.factorial (k - i)) *
      ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
        ↑(Nat.choose (m + k - i - j) (k - i)) := by
  -- Split into j ≤ m and j > m
  -- For j > m: descFact(m,j) = 0 so LHS term = 0.
  --            Also C(m+k-i-j, k-i) = 0 when i < k (since m+k-i-j < k-i).
  --            When i = k, k-i = 0, C(anything, 0) = 1, but j > m and j ≤ k = i ≤ m, contradiction!
  -- So actually j > m can't happen when i ≤ m and j ≤ k (since j ≤ k ≤ ... wait, j can be > m if k > m).
  -- But i ≤ m, so this is fine. When j > m: descFact = 0 makes LHS terms 0.
  -- For RHS: when j > m and i < k: C(m+k-i-j, k-i) = 0, so RHS term = 0. ✓
  -- When j > m and i = k: j > m ≥ i = k, but j ∈ range(k+1) means j ≤ k, contradicting j > m ≥ k. So impossible.
  -- So for j > m with j ≤ k: need i < k. Since i ≤ m < j ≤ k, we get i ≤ m < k, so i < k. ✓
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simp [Finset.mem_range] at hj; omega
  by_cases hjm : j ≤ m
  · have h := desc_fact_mul_fact k m i j hi hjm
    have hcast : (↑(Nat.descFactorial m j) : ℤ) * ↑(Nat.factorial (m + k - i - j)) =
        ↑(Nat.factorial m) * ↑(Nat.choose (m + k - i - j) (k - i)) *
        ↑(Nat.factorial (k - i)) := by exact_mod_cast h
    calc (-1 : ℤ) ^ j * ↑(k.choose j) * ↑(Nat.descFactorial m j) *
          ↑(Nat.factorial (m + k - i - j))
        = (-1 : ℤ) ^ j * ↑(k.choose j) *
          (↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j))) := by ring
      _ = (-1 : ℤ) ^ j * ↑(k.choose j) *
          (↑(Nat.factorial m) * ↑(Nat.choose (m + k - i - j) (k - i)) *
          ↑(Nat.factorial (k - i))) := by rw [hcast]
      _ = ↑(Nat.factorial m) * ↑(Nat.factorial (k - i)) *
          ((-1 : ℤ) ^ j * ↑(k.choose j) *
          ↑(Nat.choose (m + k - i - j) (k - i))) := by ring
  · push_neg at hjm
    -- j > m and j ≤ k, so i ≤ m < j ≤ k, hence i < k
    have hik : i < k := by omega
    have hdesc : Nat.descFactorial m j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hjm
    have hchoose : Nat.choose (m + k - i - j) (k - i) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hdesc, hchoose]

-- Inner sum at i = 0: equals m! * k!
private lemma inner_sum_at_zero (k m : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - j)) =
    ↑(Nat.factorial m) * ↑(Nat.factorial k) := by
  have hrw : ∀ j, Nat.factorial (m + k - j) = Nat.factorial (m + k - 0 - j) := by
    intro j; simp
  simp_rw [hrw]
  rw [inner_sum_factor k m 0 (Nat.zero_le k) (Nat.zero_le m)]
  simp only [Nat.sub_zero]
  have hrw2 : ∀ j, Nat.choose (m + k - j) k = Nat.choose (k + m - j) k := by
    intro j; congr 1; omega
  simp_rw [hrw2]
  rw [alternating_vandermonde_zero k m]; ring

-- Inner sum at i ≥ 1: vanishes
private lemma inner_sum_vanish_pos (k m i : ℕ)
    (hi_pos : 1 ≤ i) (hi : i ≤ k) (him : i ≤ m) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
      ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j)) = 0 := by
  rw [inner_sum_factor k m i hi him]
  have hrw : ∀ j, Nat.choose (m + k - i - j) (k - i) =
      Nat.choose (k + (m - i) - j) (k - i) := by intro j; congr 1; omega
  simp_rw [hrw]
  rw [alternating_vandermonde_vanish k (m - i) (k - i) (by omega)]
  ring

-- The double sum identity
-- This is the heaviest combinatorial normalization in the file: expand, swap, factor, then collapse.
private theorem double_sum_vandermonde (k m : ℕ) :
    ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℤ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
      ↑(Nat.descFactorial m i) * ↑(Nat.descFactorial m j) *
      ↑(Nat.factorial (m + k - i - j)) =
    ↑(Nat.factorial k) * ↑(Nat.factorial m) := by
  have hfactor : ∀ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℤ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        ↑(Nat.descFactorial m i) * ↑(Nat.descFactorial m j) *
        ↑(Nat.factorial (m + k - i - j)) =
      (-1 : ℤ) ^ i * ↑(k.choose i) * ↑(Nat.descFactorial m i) *
        (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ↑(k.choose j) *
          ↑(Nat.descFactorial m j) * ↑(Nat.factorial (m + k - i - j))) := by
    intro i _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; rw [pow_add]; ring
  rw [Finset.sum_congr rfl hfactor]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one,
      Nat.descFactorial_zero, Nat.sub_zero, mul_one]
    rw [inner_sum_at_zero k m]; ring
  · intro i hi hi_ne
    have hik : i ≤ k := by simp [Finset.mem_range] at hi; omega
    by_cases him : i ≤ m
    · rw [inner_sum_vanish_pos k m i (by omega) hik him]; ring
    · push_neg at him
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr him]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (Nat.zero_lt_succ k))

-- Helper: each monomial term ‖z‖^{2a} * exp(-‖z‖²) is integrable
private lemma integrable_norm_pow_exp (a : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ (2 * a) * Real.exp (-‖z‖ ^ 2)) := by
  by_contra h
  have hint := integral_norm_pow_exp_gaussian a
  rw [MeasureTheory.integral_undef h] at hint
  linarith [show (0 : ℝ) < π * (Nat.factorial a : ℝ) from by positivity]

-- The main diagonal integral computation
-- The integral proof unfolds the diagonal formula and runs the full double-sum normalization.
-- double-sum expansion, cross-term simplification, and Vandermonde application
private theorem norm_sq_phi_integral (k m : ℕ) :
    ∫ z : ℂ, ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) = Real.pi := by
  -- Step 1: Express ‖Phi‖² * exp as a double sum * exp pointwise
  -- ‖Phi k m z‖² = (1/(k!*m!)) * Σ_{i,j} (-1)^{i+j} C(k,i) C(k,j)
  --   * descFact(m,i) descFact(m,j) ‖z‖^{2(m+k-i-j)}
  have hnsq : ∀ z : ℂ, ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      (1 / ((Nat.factorial k : ℝ) * (Nat.factorial m : ℝ))) *
      ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (min k m + 1),
        (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
        (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
        (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) := by
    intro z
    suffices h : ‖Phi k m z‖ ^ 2 =
        (1 / ((↑k.factorial : ℝ) * ↑m.factorial)) *
        ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (min k m + 1),
          (-1 : ℝ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
          ↑(m.descFactorial i) * ↑(m.descFactorial j) *
          ‖z‖ ^ (2 * (m + k - i - j)) by
      rw [h, mul_assoc, Finset.sum_mul]
      congr 1; apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    simp only [Phi]
    rw [norm_mul, mul_pow]
    have hpre : ‖(1 : ℂ) / ↑√(↑k.factorial * ↑m.factorial)‖ ^ 2 =
        1 / ((↑k.factorial : ℝ) * ↑m.factorial) := by
      rw [norm_div, norm_one, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
      rw [one_div, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _), one_div]
    rw [hpre]; congr 1
    set S := Finset.range (min k m + 1)
    set g : ℕ → ℂ := fun j =>
        (-1 : ℂ) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        z ^ (m - j) * star z ^ (k - j)
    change ‖∑ j ∈ S, g j‖ ^ 2 = _
    have hnorm_re : ‖∑ j ∈ S, g j‖ ^ 2 =
        ((∑ i ∈ S, g i) * (starRingEnd ℂ) (∑ j ∈ S, g j)).re := by
      rw [mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hnorm_re, map_sum, Finset.sum_mul_sum]
    simp_rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    have him : i ≤ m := by rw [Finset.mem_range] at hi; omega
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega
    have hjk : j ≤ k := by rw [Finset.mem_range] at hj; omega
    -- Cross-term: (g i * conj(g j)).re = coeff * ‖z‖^{2(m+k-i-j)}
    -- Step 1: Expand conj(g j) - coefficients are real, conj swaps z and star z
    have hconj_g : (starRingEnd ℂ) (g j) =
        (-1 : ℂ) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        star z ^ (m - j) * z ^ (k - j) := by
      simp only [g, map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀]
      congr 1; congr 1; exact star_star z
    rw [hconj_g]; simp only [g]
    -- Step 2: Rearrange z-power product
    have hzpow : z ^ (m - i) * star z ^ (k - i) * (star z ^ (m - j) * z ^ (k - j)) =
        ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by
      have h1 : z ^ (m - i) * z ^ (k - j) = z ^ (m + k - i - j) := by
        rw [← pow_add]; congr 1; omega
      have h2 : star z ^ (k - i) * star z ^ (m - j) = star z ^ (m + k - i - j) := by
        rw [← pow_add]; congr 1; omega
      calc z ^ (m - i) * star z ^ (k - i) * (star z ^ (m - j) * z ^ (k - j))
        = (z ^ (m - i) * z ^ (k - j)) * (star z ^ (k - i) * star z ^ (m - j)) := by ring
        _ = z ^ (m + k - i - j) * star z ^ (m + k - i - j) := by rw [h1, h2]
        _ = ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by
            rw [← mul_pow, show z * star z = ↑(‖z‖ ^ 2 : ℝ) from by
              rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj']
              push_cast; rfl]
            push_cast; rw [← pow_mul]
    -- Step 3: Rearrange the full product into coeff * ↑(‖z‖^{2a})
    have hprod : (-1 : ℂ) ^ i * ↑(k.choose i) * (↑m.factorial / ↑(m - i).factorial) *
        z ^ (m - i) * star z ^ (k - i) *
        ((-1) ^ j * ↑(k.choose j) * (↑m.factorial / ↑(m - j).factorial) *
        star z ^ (m - j) * z ^ (k - j)) =
        ((-1 : ℂ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        (↑m.factorial / ↑(m - i).factorial) * (↑m.factorial / ↑(m - j).factorial)) *
        ↑(‖z‖ ^ (2 * (m + k - i - j)) : ℝ) := by
      rw [← hzpow, pow_add]; ring
    rw [hprod]
    -- Step 4: Replace m!/(m-j)! with descFactorial
    have hfact_desc_i : (↑m.factorial : ℂ) / ↑(m - i).factorial = ↑(m.descFactorial i : ℕ) := by
      have hdvd : (m - i).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (Nat.sub_le m i)
      rw [Nat.descFactorial_eq_div him]
      rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    have hfact_desc_j : (↑m.factorial : ℂ) / ↑(m - j).factorial = ↑(m.descFactorial j : ℕ) := by
      have hdvd : (m - j).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (Nat.sub_le m j)
      rw [Nat.descFactorial_eq_div hjm]
      rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    rw [hfact_desc_i, hfact_desc_j]
    -- Step 5: Everything is now ↑(real), so .re = the real value
    rw [show (-1 : ℂ) ^ (i + j) * ↑↑(k.choose i) * ↑↑(k.choose j) *
        ↑↑(m.descFactorial i) * ↑↑(m.descFactorial j) =
        ↑((-1 : ℝ) ^ (i + j) * ↑(k.choose i) * ↑(k.choose j) *
        ↑(m.descFactorial i) * ↑(m.descFactorial j)) from by push_cast; ring]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hnsq]
  rw [integral_const_mul]
  -- Step 2: Swap sum and integral (finite sums, each term is integrable)
  have hint_each : ∀ (i j : ℕ),
      Integrable (fun z : ℂ =>
        (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
        (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
        (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2))) := by
    intro i j
    exact (integrable_norm_pow_exp (m + k - i - j)).const_mul _
  have hswap_outer : ∀ i ∈ Finset.range (min k m + 1),
      Integrable (fun z : ℂ =>
        ∑ j ∈ Finset.range (min k m + 1),
          (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
          (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
          (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2))) := by
    intro i _; exact integrable_finset_sum _ (fun j _ => hint_each i j)
  rw [integral_finset_sum _ hswap_outer]
  have hswap_inner : ∀ i, ∫ z : ℂ, ∑ j ∈ Finset.range (min k m + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) =
      ∑ j ∈ Finset.range (min k m + 1), ∫ z : ℂ,
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) := by
    intro i; exact integral_finset_sum _ (fun j _ => hint_each i j)
  simp_rw [hswap_inner]
  -- Step 3: Compute each monomial integral
  have hcompute : ∀ (i j : ℕ),
      ∫ z : ℂ, (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (‖z‖ ^ (2 * (m + k - i - j)) * Real.exp (-‖z‖ ^ 2)) =
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (π * (Nat.factorial (m + k - i - j) : ℝ)) := by
    intro i j
    rw [integral_const_mul, integral_norm_pow_exp_gaussian]
  simp_rw [hcompute]
  -- Step 4: Extend sum range from (min k m + 1) to (k + 1)
  -- Extra terms have descFactorial m j = 0 (when j > m and k > m) or choose k j = 0 (when j > k)
  -- Actually, we can fold everything into the double_sum_vandermonde directly.
  -- First, factor out π and get the double sum matching double_sum_vandermonde
  have hfold : ∀ (i j : ℕ),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (π * (Nat.factorial (m + k - i - j) : ℝ)) =
      π * ((-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ)) := by
    intro i j; ring
  simp_rw [hfold]
  -- Pull π out of sums: Σ (π * g(i,j)) = π * Σ g(i,j)
  simp_rw [← Finset.mul_sum]
  -- Now goal: (1/(k!*m!)) * (π * Σ_i (π * Σ_j (...))) = π
  -- After pulling π out of both sums: (1/(k!*m!)) * π * Σ_{i,j} (...) = π
  -- But actually after simp_rw [← Finset.mul_sum], the inner sum already pulled π out.
  -- Let me check what the goal looks like and adjust.
  -- Goal should be: (1/(k!*m!)) * π * (Σ_i Σ_j coeff) = π
  -- Extend sum from range(min k m + 1) to range(k + 1)
  -- Extra terms have descFactorial m i = 0 (when i > m and k > m)
  -- or choose k i = 0 (when i > k, which doesn't happen since range stops at min k m ≤ k)
  -- When k ≤ m: min k m = k, so range(min k m + 1) = range(k + 1), no extension needed
  -- When k > m: min k m = m, extra terms for m < i ≤ k have descFactorial m i = 0
  have hext_j : ∀ i, ∑ j ∈ Finset.range (min k m + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) := by
    intro i
    apply Finset.sum_subset (Finset.range_mono (by omega : min k m + 1 ≤ k + 1))
    intro j hj hj'
    rw [Finset.mem_range] at hj hj'
    push_neg at hj'
    -- j ≥ min k m + 1 and j < k + 1, so j > min k m
    have hjm : m < j := by omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hjm]
  simp_rw [hext_j]
  have hext_i : ∑ i ∈ Finset.range (min k m + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega : min k m + 1 ≤ k + 1))
    intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    push_neg at hi'
    have him : m < i := by omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr him]
  rw [hext_i]
  -- Now apply double_sum_vandermonde (cast from ℤ to ℝ)
  have hvand := double_sum_vandermonde k m
  -- Cast hvand from ℤ to ℝ
  have hvand_real : ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ) ^ (i + j) * (Nat.choose k i : ℝ) * (Nat.choose k j : ℝ) *
      (Nat.descFactorial m i : ℝ) * (Nat.descFactorial m j : ℝ) *
      (Nat.factorial (m + k - i - j) : ℝ) =
      (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ) := by
    have := congr_arg (fun x : ℤ => (x : ℝ)) hvand
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast] at this
    convert this using 1
  rw [hvand_real]
  -- Now: (1/(k!*m!)) * π * (k! * m!) = π
  have hpos : (0 : ℝ) < (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ) := by positivity
  field_simp

/-- The level-`k` basis is orthonormal for the weighted inner product. -/
theorem phi_orthonormal :
    ∀ {k m n : ℕ},
      weightedInner (Phi k m) (Phi k n) = if m = n then 1 else 0 := by
  intro k m n
  by_cases hmn : m = n
  · -- Diagonal case: m = n
    subst hmn
    rw [if_pos rfl]
    unfold weightedInner HermiteLEAN.weightedInner
    have hint : ∫ (z : ℂ), Phi k m z * (starRingEnd ℂ) (Phi k m z) *
        ↑(rexp (-‖z‖ ^ 2)) = ↑Real.pi := by
      have hreal : ∀ z : ℂ, Phi k m z * (starRingEnd ℂ) (Phi k m z) *
          ↑(rexp (-‖z‖ ^ 2)) = ↑(‖Phi k m z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
        intro z; rw [mul_conj]; push_cast; rw [Complex.normSq_eq_norm_sq]
        ring_nf; simp [mul_comm]
      simp_rw [hreal, integral_complex_ofReal]
      congr 1
      exact norm_sq_phi_integral k m
    rw [hint]; field_simp [Real.pi_ne_zero]
  · -- Off-diagonal case: m ≠ n. Use rotation trick on ℂ-valued integrand.
    rw [if_neg hmn]
    -- The ℂ-valued integrand
    set f : ℂ → ℂ := fun z =>
      Phi k m z * star (Phi k n z) * (↑(Real.exp (-‖z‖ ^ 2)) : ℂ) with hf_def
    -- Pick ω on the unit circle with ω^{m-n} = -1
    set d : ℤ := (m : ℤ) - (n : ℤ)
    have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (by exact_mod_cast hmn)
    set ω : _root_.Circle := _root_.Circle.exp (Real.pi / (d : ℝ))
    set rot : ℂ ≃ₗᵢ[ℝ] ℂ := rotation ω
    -- f(ω z) = -f(z) because each monomial z^{p-j} conj(z)^{k-j} picks up
    -- ω^{p-j} conj(ω)^{k-j} = ω^{p-k} (independent of j, since |ω|=1),
    -- so Phi k p (ωz) = ω^{p-k} Phi k p z, and the inner product factor is ω^{m-n} = -1.
    -- ω^m * star(ω)^n = -1 (same proof as gaussian_monomial_moments_off_diag)
    have hωmn : (ω : ℂ) ^ m * star (ω : ℂ) ^ n = -1 := by
      rw [star_def, ← _root_.Circle.coe_inv_eq_conj]
      rw [← _root_.Circle.coe_pow, ← _root_.Circle.coe_pow, ← _root_.Circle.coe_mul]
      rw [show ω ^ m * ω⁻¹ ^ n = ω ^ d from by
        rw [show ω ^ m * ω⁻¹ ^ n = ω ^ m * (ω ^ n)⁻¹ from by rw [inv_pow],
          ← zpow_natCast ω m, ← zpow_natCast ω n, ← zpow_sub]]
      rw [show ω = _root_.Circle.exp (Real.pi / (d : ℝ)) from rfl,
        ← _root_.Circle.exp_intCast_mul (Real.pi / (d : ℝ)) d,
        show (d : ℝ) * (Real.pi / (d : ℝ)) = Real.pi from by field_simp]
      simp only [_root_.Circle.coe_exp, Complex.exp_pi_mul_I, Complex.ofReal_neg,
        Complex.ofReal_one]
    -- |ω|^{2k} = 1
    have hωmod : (ω : ℂ) ^ k * star (ω : ℂ) ^ k = 1 := by
      rw [← mul_pow]
      rw [show (ω : ℂ) * star (ω : ℂ) = 1 from by
        rw [star_def, ← _root_.Circle.coe_inv_eq_conj, ← _root_.Circle.coe_mul,
          mul_inv_cancel, _root_.Circle.coe_one]]
      simp
    have hrot_f : ∀ z, f (rot z) = -f z := by
      intro z
      simp only [hf_def, rot, rotation_apply, norm_mul, _root_.Circle.norm_coe, one_mul]
      rw [Phi_rotation_equivariant ω z k m, Phi_rotation_equivariant ω z k n]
      simp only [star_mul, map_pow, map_mul, star_star, star_pow]
      -- After simplification: star(star ↑ω ^ k) becomes ↑ω ^ k (via star_pow + star_star)
      -- star(↑ω ^ n) becomes star(↑ω) ^ n (via star_pow)
      calc (ω : ℂ) ^ m * star (ω : ℂ) ^ k * Phi k m z *
            (star (Phi k n z) * ((ω : ℂ) ^ k * star (ω : ℂ) ^ n)) *
            ↑(rexp (-‖z‖ ^ 2))
          = ((ω : ℂ) ^ m * star (ω : ℂ) ^ n) * ((ω : ℂ) ^ k * star (ω : ℂ) ^ k) *
            (Phi k m z * star (Phi k n z) * ↑(rexp (-‖z‖ ^ 2))) := by ring
        _ = -1 * 1 * (Phi k m z * star (Phi k n z) * ↑(rexp (-‖z‖ ^ 2))) := by
            rw [hωmn, hωmod]
        _ = _ := by ring
    -- From ∫ f(rot z) = ∫ f(z) and f(rot z) = -f(z), get ∫ f = 0
    have hmp := rot.measurePreserving
    have hemb := rot.toHomeomorph.measurableEmbedding
    have hint_eq : ∫ z, f (rot z) = ∫ z, f z := hmp.integral_comp hemb f
    simp_rw [hrot_f, integral_neg] at hint_eq
    -- hint_eq : -(∫ f) = ∫ f, so ∫ f = 0
    have hfzero : ∫ z, f z = 0 := by
      set I := ∫ z, f z
      have h : -I = I := hint_eq
      have h2 : I + I = 0 := by nth_rw 1 [← neg_neg I, h]; exact neg_add_cancel I
      have h3 : 2 • I = 0 := by rw [two_nsmul]; exact h2
      exact_mod_cast (smul_eq_zero.mp h3).resolve_left (by norm_num : (2 : ℕ) ≠ 0)
    -- Connect to weightedInner
    unfold weightedInner HermiteLEAN.weightedInner
    rw [show (∫ z : ℂ, Phi k m z * (starRingEnd ℂ) (Phi k n z) *
        ↑(Real.exp (-‖z‖ ^ 2))) = ∫ z, f z from by rfl]
    rw [hfzero, mul_zero]

-- Phi_mem_Hk is proved below, after finiteHermiteSum_normSq

theorem continuous_Phi (k n : ℕ) : Continuous (Phi k n) := by
  unfold Phi
  refine continuous_const.mul ?_
  refine continuous_finset_sum _ ?_
  intro j hj
  have hpow : Continuous (fun z : ℂ => z ^ (n - j) * (star z) ^ (k - j)) := by
    exact (continuous_id.pow (n - j)).mul (continuous_star.pow (k - j))
  have hterm : Continuous (fun z : ℂ =>
      (((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ))) *
        (z ^ (n - j) * (star z) ^ (k - j))) := by
    exact continuous_const.mul hpow
  simpa [mul_assoc] using hterm

theorem integrable_weightedDiag (k n : ℕ) :
    Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
  let f : ℂ → ℝ := fun z => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  by_contra hf
  have hfC : ¬ Integrable (fun z : ℂ => (f z : ℂ)) := by
    intro hC
    apply hf
    convert hC.re using 1
    funext z
    exact (RCLike.ofReal_re (K := ℂ) (f z)).symm
  have hzero : weightedInner (Phi k n) (Phi k n) = 0 := by
    unfold weightedInner HermiteLEAN.weightedInner
    calc
      (1 / Real.pi : ℂ) *
          ∫ z : ℂ, Phi k n z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
        = (1 / Real.pi : ℂ) * ∫ z : ℂ, (f z : ℂ) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with z
            rw [mul_conj]
            simp [f, Complex.normSq_eq_norm_sq]
      _ = (1 / Real.pi : ℂ) * 0 := by
            rw [MeasureTheory.integral_undef hfC]
      _ = 0 := by ring
  have hone : weightedInner (Phi k n) (Phi k n) = 1 := by
    simpa using (phi_orthonormal (k := k) (m := n) (n := n))
  have h01 : (0 : ℂ) = 1 := by
    calc
      (0 : ℂ) = weightedInner (Phi k n) (Phi k n) := hzero.symm
      _ = 1 := hone
  norm_num at h01

theorem integrable_weightedCross (k m n : ℕ) :
    Integrable (fun z : ℂ =>
      Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  let f : ℂ → ℂ := fun z =>
    Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let g : ℂ → ℝ := fun z =>
    ((‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2) * Real.exp (-‖z‖ ^ 2)
  have hg : Integrable g := by
    have hm : Integrable (fun z : ℂ => ‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
      integrable_weightedDiag k m
    have hn : Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
      integrable_weightedDiag k n
    have hs : Integrable (fun z : ℂ =>
      (‖Phi k m z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) +
        (‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) := hm.add hn
    convert hs.const_mul (1 / 2) using 1
    funext z
    ring
  have hf_meas : AEStronglyMeasurable f volume := by
    have hcontExp : Continuous (fun z : ℂ => (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
      exact
        Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_neg.comp (continuous_norm.pow 2)))
    exact ((continuous_Phi k m).mul (continuous_star.comp (continuous_Phi k n))).mul hcontExp
      |>.aestronglyMeasurable
  have hbound : ∀ z : ℂ, ‖f z‖ ≤ g z := by
    intro z
    calc
      ‖f z‖ = (‖Phi k m z‖ * ‖Phi k n z‖) * Real.exp (-‖z‖ ^ 2) := by
        have hexp_nonneg : 0 ≤ Real.exp (-‖z‖ ^ 2) := by positivity
        calc
          ‖Phi k m z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖
            = ‖Phi k m z * (starRingEnd ℂ) (Phi k n z)‖ *
                ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ := by
                  rw [norm_mul]
          _ = (‖Phi k m z‖ * ‖Phi k n z‖) * ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ := by
                rw [norm_mul]
                rw [show ‖(starRingEnd ℂ) (Phi k n z)‖ = ‖Phi k n z‖ by simp]
          _ = (‖Phi k m z‖ * ‖Phi k n z‖) * Real.exp (-‖z‖ ^ 2) := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
      _ ≤ (((‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2) * Real.exp (-‖z‖ ^ 2)) := by
            have hsq :
                2 * (‖Phi k m z‖ * ‖Phi k n z‖) ≤ ‖Phi k m z‖ ^ 2 + ‖Phi k n z‖ ^ 2 := by
              nlinarith [sq_nonneg (‖Phi k m z‖ - ‖Phi k n z‖)]
            have hexp_nonneg : 0 ≤ Real.exp (-‖z‖ ^ 2) := by positivity
            nlinarith
      _ = g z := by simp [g]
  exact MeasureTheory.Integrable.mono' hg hf_meas (Filter.Eventually.of_forall hbound)

private lemma weightedNormSq_eq_re_weightedInner (F : ℂ → ℂ) :
    weightedNormSq F = Complex.re (weightedInner F F) := by
  unfold HermitekLEAN.weightedNormSq HermiteLEAN.weightedNormSq
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  have hfun :
      (fun z : ℂ => F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ))
        = fun z : ℂ => ((‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
    funext z
    rw [show F z * (starRingEnd ℂ) (F z) = ((‖F z‖ ^ 2 : ℝ) : ℂ) by
      simpa using Complex.mul_conj' (F z)]
    simp
  rw [hfun, integral_complex_ofReal]
  simp

private lemma weightedInner_conj_symm (F G : ℂ → ℂ) :
    weightedInner F G = star (weightedInner G F) := by
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  change _ = (starRingEnd ℂ) _
  rw [map_mul]
  have hpi : (starRingEnd ℂ) ((1 : ℂ) / ↑Real.pi) = (1 : ℂ) / ↑Real.pi := by
    rw [map_div₀, map_one, Complex.conj_ofReal]
  rw [hpi]
  congr 1
  rw [show (starRingEnd ℂ)
    (∫ z : ℂ, G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2))) =
    ∫ z : ℂ, (starRingEnd ℂ)
      (G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2)))
    from (integral_conj (f := fun z =>
      G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2)))).symm]
  congr 1
  ext z
  simp only [map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
  ring

private lemma integrable_finiteHermiteSum_weightedCross
    (k : ℕ) {D n : ℕ} (a : Fin D → ℂ) :
    Integrable (fun z : ℂ =>
      finiteHermiteSum k a z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  unfold finiteHermiteSum
  have hEq :
      (fun z : ℂ =>
        (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ))
        =
      fun z : ℂ =>
        ∑ m : Fin D, a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    funext z
    calc
      (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)
        = ∑ m : Fin D,
            (a m * Phi k m.1 z) *
              ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              rw [mul_assoc, ← Finset.sum_mul]
      _ = ∑ m : Fin D,
          a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            ring
  rw [hEq]
  refine MeasureTheory.integrable_finset_sum (Finset.univ : Finset (Fin D)) ?_
  intro m hm
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (integrable_weightedCross k m.1 n).const_mul (a m)


private theorem weightedInner_add_left_of_integrable
    (F G H : ℂ → ℂ)
    (hF : Integrable
      (fun z : ℂ => F z * (starRingEnd ℂ) (H z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
    (hG : Integrable
      (fun z : ℂ => G z * (starRingEnd ℂ) (H z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :
    weightedInner (F + G) H = weightedInner F H + weightedInner G H := by
  have hsum := congrArg (fun t : ℂ => (1 / Real.pi : ℂ) * t) (integral_add hF hG)
  simpa [weightedInner, HermiteLEAN.weightedInner, Pi.add_apply, add_mul, mul_add, mul_assoc,
    mul_left_comm, mul_comm] using hsum

private theorem weightedInner_finset_sum_left
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (f : α → ℂ → ℂ)
    (g : ℂ → ℂ)
    (hf : ∀ a ∈ s,
      Integrable
        (fun z : ℂ => f a z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :
    weightedInner (fun z => Finset.sum s (fun a => f a z)) g =
      Finset.sum s (fun a => weightedInner (f a) g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [weightedInner, HermiteLEAN.weightedInner]
  | @insert a s ha ih =>
      have hf' :
          ∀ b ∈ s,
            Integrable
              (fun z : ℂ => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)
      have hfa :
          Integrable
            (fun z : ℂ => f a z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        exact hf a (Finset.mem_insert_self a s)
      simp_rw [Finset.sum_insert ha]
      have hsumInt :
          Integrable
            (fun z : ℂ =>
              (Finset.sum s (fun b => f b z)) * (starRingEnd ℂ) (g z) *
                (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        have hsumInt' :
            Integrable
              (fun z : ℂ =>
                Finset.sum s
                  (fun b => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
          exact MeasureTheory.integrable_finset_sum s (fun b hb => hf' b hb)
        have hEq :
            (fun z : ℂ =>
              (Finset.sum s (fun b => f b z)) * (starRingEnd ℂ) (g z) *
                (Real.exp (-‖z‖ ^ 2) : ℂ)) =
              fun z : ℂ =>
                Finset.sum s
                  (fun b => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
          funext z
          rw [mul_assoc]
          rw [Finset.sum_mul]
          simp [mul_assoc, mul_left_comm, mul_comm]
        exact hEq.symm ▸ hsumInt'
      change weightedInner ((fun z : ℂ => f a z) + fun z => Finset.sum s (fun b => f b z)) g =
        weightedInner (f a) g + Finset.sum s (fun a => weightedInner (f a) g)
      rw [weightedInner_add_left_of_integrable (F := fun z => f a z)
        (G := fun z => Finset.sum s (fun b => f b z)) (H := g) hfa hsumInt]
      rw [ih hf']

private lemma weightedInner_finiteHermiteSum_basis
    (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (n : ℕ) :
    weightedInner (finiteHermiteSum k a) (Phi k n) =
      ∑ m : Fin D, a m * weightedInner (Phi k m.1) (Phi k n) := by
  unfold weightedInner HermiteLEAN.weightedInner
  simp_rw [finiteHermiteSum, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finset_sum]
  · change
      (1 / Real.pi : ℂ) *
          ∑ m : Fin D,
            ∫ z : ℂ,
              a m *
                (Phi k m.1 z *
                  ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
        =
        ∑ m : Fin D,
          a m *
            ((1 / Real.pi : ℂ) *
              ∫ z : ℂ,
                Phi k m.1 z *
                  ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
    calc
        (1 / Real.pi : ℂ) *
            ∑ m : Fin D,
              ∫ z : ℂ,
                a m *
                  (Phi k m.1 z *
                    ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
          =
            ∑ m : Fin D,
              (1 / Real.pi : ℂ) *
                ∫ z : ℂ,
                  a m *
                    (Phi k m.1 z *
                      ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              simp [Finset.mul_sum]
        _ =
            ∑ m : Fin D,
              a m *
                ((1 / Real.pi : ℂ) *
                  ∫ z : ℂ,
                    Phi k m.1 z *
                      ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hconst :
                  (∫ z : ℂ,
                    a m *
                      (Phi k m.1 z *
                        ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
                    =
                      a m *
                        ∫ z : ℂ,
                          Phi k m.1 z *
                            ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
                exact
                  MeasureTheory.integral_const_mul (a m)
                    (fun z : ℂ =>
                      Phi k m.1 z *
                        ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
              rw [hconst]
              ring_nf
  · intro m hm
    simpa [mul_assoc] using (integrable_weightedCross k m.1 n).const_mul (a m)

private lemma weightedInner_finiteHermiteSum
    (k : ℕ) {D : ℕ} (a b : Fin D → ℂ) :
    weightedInner (finiteHermiteSum k a) (finiteHermiteSum k b) =
      ∑ m : Fin D, (starRingEnd ℂ) (b m) *
        weightedInner (finiteHermiteSum k a) (Phi k m.1) := by
  unfold weightedInner HermiteLEAN.weightedInner
  have hfun :
      (fun z : ℂ =>
        finiteHermiteSum k a z *
          (starRingEnd ℂ) (finiteHermiteSum k b z) *
            (Real.exp (-‖z‖ ^ 2) : ℂ))
        =
      fun z : ℂ =>
        ∑ m : Fin D,
          (starRingEnd ℂ) (b m) *
            (finiteHermiteSum k a z *
              ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
    funext z
    rw [finiteHermiteSum, finiteHermiteSum, map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hfun, MeasureTheory.integral_finset_sum]
  · calc
      (1 / Real.pi : ℂ) *
          ∑ m : Fin D,
            ∫ z : ℂ,
              (starRingEnd ℂ) (b m) *
                (finiteHermiteSum k a z *
                  ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
        =
          (1 / Real.pi : ℂ) *
            ∑ m : Fin D,
              (starRingEnd ℂ) (b m) *
                ∫ z : ℂ,
                  finiteHermiteSum k a z *
                    ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              congr 1
              refine Finset.sum_congr rfl (fun m _ => ?_)
              exact
                MeasureTheory.integral_const_mul ((starRingEnd ℂ) (b m))
                  (fun z : ℂ =>
                    finiteHermiteSum k a z *
                      ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
      _ =
          ∑ m : Fin D,
            (starRingEnd ℂ) (b m) *
              ((1 / Real.pi : ℂ) *
                ∫ z : ℂ,
                  (fun z => finiteHermiteSum k a z) z *
                    (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun m _ => ?_)
              have hintegral :
                  ∫ z : ℂ,
                    finiteHermiteSum k a z *
                      ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))
                    =
                      ∫ z : ℂ,
                        (fun z => finiteHermiteSum k a z) z *
                          (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ) := by
                apply integral_congr_ae
                filter_upwards with z
                ring
              exact
                calc
                  (1 / Real.pi : ℂ) *
                      ((starRingEnd ℂ) (b m) *
                        ∫ z : ℂ,
                          finiteHermiteSum k a z *
                            ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
                    =
                      (starRingEnd ℂ) (b m) *
                        ((1 / Real.pi : ℂ) *
                          ∫ z : ℂ,
                            finiteHermiteSum k a z *
                              ((starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
                        ring
                  _ =
                      (starRingEnd ℂ) (b m) *
                        ((1 / Real.pi : ℂ) *
                          ∫ z : ℂ,
                            (fun z => finiteHermiteSum k a z) z *
                              (starRingEnd ℂ) (Phi k m.1 z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
                        rw [hintegral]
      _ = ∑ m : Fin D, (starRingEnd ℂ) (b m) * weightedInner (finiteHermiteSum k a) (Phi k m.1) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rfl
  · intro m hm
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrable_finiteHermiteSum_weightedCross (k := k) (a := a) (n := m.1)).const_mul
        ((starRingEnd ℂ) (b m))

/-- Inner products of finite Hermite sums are finite coefficient inner products. -/
theorem finiteHermiteSum_inner :
    ∀ {k D : ℕ} (a b : Fin D → ℂ),
      weightedInner (finiteHermiteSum k a) (finiteHermiteSum k b) =
        ∑ n : Fin D, a n * star (b n) := by
  intro k D a b
  rw [weightedInner_finiteHermiteSum]
  calc
    ∑ m : Fin D, (starRingEnd ℂ) (b m) * weightedInner (finiteHermiteSum k a) (Phi k m.1)
      = ∑ m : Fin D, a m * star (b m) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [weightedInner_finiteHermiteSum_basis]
          have horth :
              ∀ x : Fin D, weightedInner (Phi k x.1) (Phi k m.1) = if x = m then 1 else 0 := by
            intro x
            rw [phi_orthonormal]
            by_cases hxm : x = m
            · subst hxm
              simp
            · have hxval : x.1 ≠ m.1 := by
                intro hEq
                exact hxm (Fin.ext hEq)
              simp [hxm, hxval]
          calc
            star (b m) * ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k m.1)
              = star (b m) * ∑ x : Fin D, a x * (if x = m then (1 : ℂ) else 0) := by
                  congr 1
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  rw [horth x]
            _ = star (b m) * a m := by simp
            _ = a m * star (b m) := by ring
    _ = ∑ n : Fin D, a n * star (b n) := by rfl

/-- The weighted norm square of a finite Hermite sum is the coefficient `ℓ²` norm square. -/
theorem finiteHermiteSum_normSq :
    ∀ {k D : ℕ} (a : Fin D → ℂ),
      weightedNormSq (finiteHermiteSum k a) = ∑ n : Fin D, ‖a n‖ ^ 2 := by
  intro k D a
  rw [weightedNormSq_eq_re_weightedInner, finiteHermiteSum_inner]
  simp [Complex.normSq, Complex.sq_norm]




/-- Helper: Hermite coefficients of a finite sum. -/
private lemma weightedInner_finiteHermiteSum_coeff (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (n : ℕ) :
    weightedInner (finiteHermiteSum k a) (Phi k n) =
      if h : n < D then a ⟨n, h⟩ else 0 := by
  rw [weightedInner_finiteHermiteSum_basis]
  by_cases h : n < D
  · let m : Fin D := ⟨n, h⟩
    calc ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n)
        = ∑ x : Fin D, a x * (if x.1 = n then 1 else 0) := by
          refine Finset.sum_congr rfl ?_; intro x _; rw [phi_orthonormal]
      _ = ∑ x : Fin D, (if x = m then a m else 0) := by
          refine Finset.sum_congr rfl ?_; intro x _
          by_cases hx : x = m
          · subst hx; simp [m]
          · have : x.1 ≠ n := fun hEq => hx (Fin.ext (by simpa [m] using hEq))
            simp [this, hx]
      _ = a m := by simp
    simp [m, h]
  · have : ∀ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n) = 0 := by
      intro x; rw [phi_orthonormal]
      simp [show x.1 ≠ n from fun hEq => h (hEq ▸ x.isLt)]
    simp [this, h]

/-- Every finite Hermite sum belongs to the true level space. -/
theorem finiteHermiteSum_mem_Hk :
    ∀ (k : ℕ) {D : ℕ} (a : Fin D → ℂ), finiteHermiteSum k a ∈ Hk k := by
  intro k D a
  refine ⟨?_, ?_⟩
  · change Integrable (fun z : ℂ => ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2))
    by_contra habs
    have hzero :
        (1 / Real.pi) * ∫ z : ℂ, ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2) = 0 := by
      rw [MeasureTheory.integral_undef habs]
      ring
    have hpos : (1 / Real.pi) * ∫ z : ℂ, ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2) =
        ∑ n : Fin D, ‖a n‖ ^ 2 := by
      change weightedNormSq (finiteHermiteSum k a) = _
      exact finiteHermiteSum_normSq (k := k) (a := a)
    rw [hpos] at hzero
    have hall_zero : ∀ n : Fin D, a n = 0 := by
      intro n
      have :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖a i‖)).mp hzero n (Finset.mem_univ n)
      exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖a n‖])
    have hzero_fun : (fun z : ℂ => ‖finiteHermiteSum k a z‖ ^ 2 * rexp (-‖z‖ ^ 2)) = 0 := by
      ext z
      simp [finiteHermiteSum, hall_zero]
    rw [hzero_fun] at habs
    exact habs (integrable_zero ℂ ℝ volume)
  · intro z
    simp_rw [weightedInner_finiteHermiteSum_coeff]
    let f : ℕ → ℂ := fun n => (if h : n < D then a ⟨n, h⟩ else 0) * Phi k n z
    change HasSum f (finiteHermiteSum k a z)
    have hfin : ∀ n, n ∉ Finset.range D → f n = 0 := by
      intro n hn
      simp only [f, Finset.mem_range, not_lt] at hn ⊢
      simp [show ¬(n < D) from not_lt.mpr hn]
    have hval : finiteHermiteSum k a z = ∑ n ∈ Finset.range D, f n := by
      simp only [finiteHermiteSum, f]
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl ?_
      intro ⟨n, hn⟩ _
      simp [show n < D from hn]
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero hfin



/-- The truncation operator is the explicit finite Hermite sum of the first coefficients. -/
theorem truncate_eq_finiteHermiteSum :
    ∀ {k J : ℕ} {G : ℂ → ℂ},
      truncate k J G =
        finiteHermiteSum k (fun n : Fin (J + 1) => hermiteCoeff k G n.1) := by
  intro k J G
  rfl




/-- Every truncation lies in the true level space. -/
theorem truncate_mem_Hk :
    ∀ (k J : ℕ) (G : ℂ → ℂ), truncate k J G ∈ Hk k := by
  intro k J G
  simpa [truncate] using
    (finiteHermiteSum_mem_Hk k (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1))

/-- Exact finite Parseval identity for Hermite truncations. -/
theorem truncate_normSq :
    ∀ (k J : ℕ) (G : ℂ → ℂ),
      weightedNormSq (truncate k J G) =
        ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 := by
  intro k J G
  simpa [truncate_eq_finiteHermiteSum] using
    (finiteHermiteSum_normSq (k := k) (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1))










/-- Summability of polynomial-exponential factorial tails. -/
private lemma summable_nat_pow_mul_pow_div_factorial_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)) := by
  let f : ℕ → ℝ := fun n => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)
  rw [← @summable_nat_add_iff ℝ _ _ _ _ m]
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ))) ?_ ?_ ?_
  · intro n
    positivity
  · intro n
    have hdesc_nat : (n + 1) ^ m ≤ (n + m).descFactorial m := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.pow_sub_le_descFactorial (n + m) m)
    have hpow_real :
        ((n + m + 1 : ℝ) ^ m) ≤
          (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by
      have hdesc : ((n + 1 : ℝ) ^ m) ≤ (((n + m).descFactorial m : ℕ) : ℝ) := by
        exact_mod_cast hdesc_nat
      calc
        ((n + m + 1 : ℝ) ^ m) ≤ (((m + 1 : ℝ) * (n + 1)) ^ m) := by
          gcongr
          nlinarith
        _ = (m + 1 : ℝ) ^ m * (n + 1 : ℝ) ^ m := by rw [mul_pow]
        _ ≤ (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by
          gcongr
    have hfact :
        (Nat.factorial n : ℝ) * (((n + m).descFactorial m : ℕ) : ℝ) =
          (Nat.factorial (n + m) : ℝ) := by
      have hfact_nat : (n.factorial * (n + m).descFactorial m) = (n + m).factorial := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.factorial_mul_descFactorial (show m ≤ n + m by omega))
      exact_mod_cast hfact_nat
    have hcalc :
        (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ)
          = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := by
      rw [pow_add, ← hfact]
      have hnfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hndesc_nat : (n + m).descFactorial m ≠ 0 := by
        exact Nat.ne_of_gt (Nat.descFactorial_pos.mpr (show m ≤ n + m by omega))
      have hndesc : (((n + m).descFactorial m : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast hndesc_nat
      field_simp [hnfact, hndesc]
    calc
      f (n + m)
          = ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) / (Nat.factorial (n + m) : ℝ) := by
              simp [f]
      _ ≤ (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ) := by
              have hpowx :
                  ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                    ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                      x ^ (n + m) := by
                exact mul_le_mul_of_nonneg_right hpow_real (pow_nonneg hx _)
              have hfacpos : 0 < (Nat.factorial (n + m) : ℝ) := by positivity
              rw [div_le_iff₀ hfacpos]
              calc
                ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                    ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                      x ^ (n + m) := hpowx
                _ =
                    ((((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) *
                        x ^ (n + m)) / (Nat.factorial (n + m) : ℝ)) *
                      (Nat.factorial (n + m) : ℝ) := by
                        have hfacne : (Nat.factorial (n + m) : ℝ) ≠ 0 := by positivity
                        field_simp [hfacne]
      _ = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := hcalc
  · simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
      (Real.summable_pow_div_factorial x).mul_left ((m + 1 : ℝ) ^ m * x ^ m)

/-- Descending factorial ratios are controlled by a fixed successor power. -/
private lemma factorial_ratio_le_pow_succ {n k j : ℕ} (hjn : j ≤ n) (hjk : j ≤ k) :
    (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) ≤ (n + 1 : ℝ) ^ k := by
  have hnat : n.descFactorial j ≤ (n + 1) ^ k := by
    calc
      n.descFactorial j ≤ n ^ j := Nat.descFactorial_le_pow _ _
      _ ≤ (n + 1) ^ j := Nat.pow_le_pow_left n.le_succ _
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos _) hjk
  have hdiv_nat : n.descFactorial j = n.factorial / (n - j).factorial := by
    rw [Nat.descFactorial_eq_div hjn]
  have hdiv : (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) = n.descFactorial j := by
    rw [hdiv_nat, Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le n j))]
    positivity
  rw [hdiv]
  exact_mod_cast hnat

/-- Partial binomial sums are bounded by the full `2^k` binomial sum. -/
private lemma choose_partial_sum_le_pow_two (k n : ℕ) :
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ)) ≤ (2 : ℝ) ^ k := by
  calc
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ))
      ≤ Finset.sum (Finset.range (k + 1)) (fun j => (Nat.choose k j : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp at hx ⊢
            omega
          · intro j _ _
            positivity
    _ = (2 : ℝ) ^ k := by
          exact_mod_cast Nat.sum_range_choose k

/-- Uniform disk majorant for the explicit basis vector `Phi k n`. -/
private lemma phi_norm_le_majorant {k n : ℕ} {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Phi k n z‖ ≤ ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
  let S := Finset.range (min k n + 1)
  let term : ℕ → ℂ := fun j =>
    (-1 : ℂ) ^ j * ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
      z ^ (n - j) * star z ^ (k - j)
  let common : ℝ := ((n + 1 : ℝ) ^ k) * R ^ k * R ^ n
  rw [phi_explicit]
  have hsum_norm : ‖Finset.sum S term‖ ≤ Finset.sum S (fun j => ‖term j‖) := norm_sum_le _ _
  have hterm_bound : ∀ j ∈ S, ‖term j‖ ≤ (Nat.choose k j : ℝ) * common := by
    intro j hj
    have hjk : j ≤ k := by
      simp [S] at hj
      omega
    have hjn : j ≤ n := by
      simp [S] at hj
      omega
    have hratio := factorial_ratio_le_pow_succ hjn hjk
    have hz1 : ‖z‖ ^ (n - j) ≤ R ^ n := by
      calc
        ‖z‖ ^ (n - j) ≤ R ^ (n - j) := by
          exact pow_le_pow_left₀ (norm_nonneg _) hz _
        _ ≤ R ^ n := by
          exact pow_le_pow_right₀ hR (Nat.sub_le _ _)
    have hz2 : ‖z‖ ^ (k - j) ≤ R ^ k := by
      calc
        ‖z‖ ^ (k - j) ≤ R ^ (k - j) := by
          exact pow_le_pow_left₀ (norm_nonneg _) hz _
        _ ≤ R ^ k := by
          exact pow_le_pow_right₀ hR (Nat.sub_le _ _)
    calc
      ‖term j‖
        = (Nat.choose k j : ℝ) * ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
            ‖z‖ ^ (n - j) * ‖z‖ ^ (k - j) := by
            dsimp [term]
            simp [norm_mul, norm_pow, norm_star, Real.norm_eq_abs]
      _ ≤ (Nat.choose k j : ℝ) * ((n + 1 : ℝ) ^ k) * R ^ n * R ^ k := by
            gcongr
      _ = (Nat.choose k j : ℝ) * common := by
            dsimp [common]
            ring
  have hsum_bound :
      Finset.sum S (fun j => ‖term j‖) ≤ Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by
    exact Finset.sum_le_sum (fun j hj => hterm_bound j hj)
  have hsum_factor :
      Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) =
        (Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common := by
    rw [Finset.sum_mul]
  have hfront_nonneg :
      0 ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ := norm_nonneg _
  have hfront :
      ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) := by
    rw [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      one_div]
  calc
    ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) * Finset.sum S term‖
      ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
          Finset.sum S (fun j => ‖term j‖) := by
            exact le_trans (norm_mul_le _ _) <|
              mul_le_mul_of_nonneg_left hsum_norm (norm_nonneg _)
    _ ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
          Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by
            exact mul_le_mul_of_nonneg_left hsum_bound hfront_nonneg
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by
            rw [hfront]
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          ((Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common) := by
            rw [hsum_factor]
    _ ≤ ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          (((2 : ℝ) ^ k) * common) := by
            gcongr
            simpa [S] using choose_partial_sum_le_pow_two k n
    _ = ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
            dsimp [common]
            rw [div_eq_mul_inv]
            ring

/-! ## Basis Bridge -/





/-- Truncation converges pointwise to G -/
private lemma truncate_tendsto_pointwise {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (z : ℂ) :
    Filter.Tendsto (fun J => truncate k J G z) Filter.atTop (nhds (G z)) := by
  have hH := hG.2 z
  -- hH : HasSum (fun n => hermiteCoeff k G n * Phi k n z) (G z)
  -- HasSum means Tendsto of partial sums over Finsets
  -- We need the sequential version through range(J+1)
  have hseq : Filter.Tendsto
      (fun J => ∑ n ∈ Finset.range J, hermiteCoeff k G n * Phi k n z)
      Filter.atTop (nhds (G z)) :=
    hH.tendsto_sum_nat
  -- truncate k J G z = ∑ n : Fin (J+1), hermiteCoeff k G n.1 * Phi k n.1 z
  -- = ∑ n ∈ range(J+1), hermiteCoeff k G n * Phi k n z
  change Filter.Tendsto (fun J =>
    ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z) Filter.atTop (nhds (G z))
  have hrw : (fun J => ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z) =
      (fun J => ∑ n ∈ Finset.range (J + 1), hermiteCoeff k G n * Phi k n z) := by
    ext J; rw [Finset.sum_range]
  rw [hrw]
  exact hseq.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))

/-- Integrability of truncation norm squared with Gaussian weight. -/
theorem integrable_truncate_normSq_exp (k J : ℕ) (G : ℂ → ℂ) :
    Integrable (fun z : ℂ => ‖truncate k J G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
  simpa using (truncate_mem_Hk k J G).1

/-- Cross integrability: Phi_n * conj(G) * exp is integrable when ‖G‖² exp is.
    Uses AM-GM: |ab| ≤ (a² + b²)/2 with the Gaussian split. -/
private lemma integrable_Phi_conj_G_exp {k : ℕ} {G : ℂ → ℂ} (n : ℕ)
    (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    Integrable (fun z : ℂ =>
      Phi k n z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  -- Bound: ‖Phi_n * conj G * exp‖ ≤ (‖Phi_n‖² + ‖G‖²) * exp
  -- Both ‖Phi_n‖² exp and ‖G‖² exp are integrable.
  have hDiag := integrable_weightedDiag k n
  have hBound : Integrable (fun z : ℂ =>
      (‖Phi k n z‖ ^ 2 + ‖G z‖ ^ 2) * rexp (-‖z‖ ^ 2)) := by
    have : (fun z : ℂ => (‖Phi k n z‖ ^ 2 + ‖G z‖ ^ 2) * rexp (-‖z‖ ^ 2)) =
        (fun z => ‖Phi k n z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
      ext z; ring
    rw [this]; exact hDiag.add hInt
  apply MeasureTheory.Integrable.mono' hBound
  · -- G is AEStronglyMeasurable: truncate_J G → G pointwise, each truncation
    -- is continuous (hence AEStronglyMeasurable).
    have hG_aesm : AEStronglyMeasurable G volume := by
      apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := fun J => truncate k J G)
      · intro J; unfold truncate finiteHermiteSum
        exact (continuous_finset_sum _ (fun m _ =>
          continuous_const.mul (continuous_Phi k m.1))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun z => truncate_tendsto_pointwise hG z)
    exact (((continuous_Phi k n).aestronglyMeasurable.mul
      (hG_aesm.star)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_neg.comp ((continuous_pow 2).comp
          continuous_norm)))).aestronglyMeasurable)
  · filter_upwards with z
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
      abs_of_nonneg (exp_nonneg _), Real.norm_of_nonneg (exp_nonneg _)]
    nlinarith [sq_nonneg (‖Phi k n z‖ - ‖G z‖), exp_nonneg (-‖z‖ ^ 2 : ℝ),
      sq_abs ‖Phi k n z‖, sq_abs ‖G z‖]

private lemma bessel_truncate_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) (J : ℕ) :
    weightedNormSq (truncate k J G) ≤ weightedNormSq G := by
  -- Step 1: ⟨trunc, G⟩ expanded via finite sum in first argument
  set a := fun n : Fin (J + 1) => hermiteCoeff k G n.1
  -- Each cross integral is integrable:
  have hCross : ∀ m : Fin (J + 1),
      Integrable (fun z : ℂ => (a m * Phi k m.1 z) * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    intro m
    have h1 := integrable_Phi_conj_G_exp (k := k) m.1 hG hInt
    have heq : (fun z : ℂ => (a m * Phi k m.1 z) * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ)) =
      (fun z : ℂ => a m * (Phi k m.1 z * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ))) := by ext z; ring
    rw [heq]; exact h1.const_mul _
  -- ⟨truncate_J G, G⟩ via finite sum expansion
  have hInnerTG : weightedInner (truncate k J G) G =
      ∑ n : Fin (J + 1), a n * (starRingEnd ℂ) (hermiteCoeff k G n.1) := by
    change weightedInner (finiteHermiteSum k a) G = _
    unfold finiteHermiteSum
    rw [weightedInner_finset_sum_left Finset.univ (fun m => fun z => a m * Phi k m.1 z) G
        (fun m _ => hCross m)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    -- ⟨c * Phi_n, G⟩ = c * conj(⟨G, Phi_n⟩)
    have h1 : weightedInner (fun z => a n * Phi k n.1 z) G =
        a n * weightedInner (Phi k n.1) G := by
      unfold weightedInner HermiteLEAN.weightedInner
      conv_lhs => rw [show (fun z : ℂ => a n * Phi k (↑n) z *
          (starRingEnd ℂ) (G z) * ↑(rexp (-‖z‖ ^ 2))) =
        (fun z => a n * (Phi k (↑n) z * (starRingEnd ℂ) (G z) *
          ↑(rexp (-‖z‖ ^ 2)))) from by ext z; ring]
      rw [show (∫ z : ℂ, a n * (Phi k (↑n) z * (starRingEnd ℂ) (G z) *
          ↑(rexp (-‖z‖ ^ 2)))) = a n * (∫ z : ℂ, (Phi k (↑n) z *
          (starRingEnd ℂ) (G z) * ↑(rexp (-‖z‖ ^ 2)))) from
        MeasureTheory.integral_const_mul _ _]
      ring
    rw [h1]
    have h2 : weightedInner (Phi k n.1) G =
        (starRingEnd ℂ) (weightedInner G (Phi k n.1)) :=
      weightedInner_conj_symm (Phi k n.1) G
    rw [h2]; rfl
  -- Simplify: a n * conj(a n) = ‖a n‖² (as complex)
  have hInnerTG' : weightedInner (truncate k J G) G =
      (∑ n : Fin (J + 1), ‖a n‖ ^ 2 : ℝ) := by
    rw [hInnerTG]; push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [a]
    rw [show hermiteCoeff k G ↑n * (starRingEnd ℂ) (hermiteCoeff k G ↑n) =
        ((‖hermiteCoeff k G ↑n‖ ^ 2 : ℝ) : ℂ) from by
      simpa using Complex.mul_conj' (hermiteCoeff k G ↑n)]; push_cast; ring
  -- Also: ⟨truncate, truncate⟩ = ∑ ‖a_n‖²
  have hInnerTT : weightedInner (truncate k J G) (truncate k J G) =
      (∑ n : Fin (J + 1), ‖a n‖ ^ 2 : ℝ) := by
    change weightedInner (finiteHermiteSum k a) (finiteHermiteSum k a) = _
    rw [finiteHermiteSum_inner]; push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show a n * star (a n) = ((‖a n‖ ^ 2 : ℝ) : ℂ) from by
      simpa using Complex.mul_conj' (a n)]; push_cast; ring
  -- From the equalities: ⟨trunc, G⟩ = ⟨trunc, trunc⟩ (= ∑ ‖a_n‖²)
  have hCrossZero : weightedInner (truncate k J G) G =
      weightedInner (truncate k J G) (truncate k J G) := by
    rw [hInnerTG', hInnerTT]
  -- weightedNormSq T = Re⟨T, T⟩ = Re⟨T, G⟩
  rw [weightedNormSq_eq_re_weightedInner, ← hCrossZero]
  let Tfun : ℂ → ℂ := truncate k J G
  have hTInt : Integrable (fun z : ℂ => ‖Tfun z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
    simpa [Tfun] using integrable_truncate_normSq_exp k J G
  have hAvgInt : Integrable (fun z : ℂ =>
      ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2)) := by
    have hsum : Integrable (fun z : ℂ =>
        ‖Tfun z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := hTInt.add hInt
    have hEq :
        (fun z : ℂ => ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2)) =
          (fun z : ℂ =>
            (1 / 2 : ℝ) *
              (‖Tfun z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
      funext z
      ring
    rw [hEq]
    exact hsum.const_mul (1 / 2 : ℝ)
  have hInnerNormLe :
      ‖weightedInner Tfun G‖ ≤ (weightedNormSq Tfun + weightedNormSq G) / 2 := by
    have hpt :
        ∀ᵐ z : ℂ ∂volume,
          ‖Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖ ≤
            ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) := by
      refine Filter.Eventually.of_forall ?_
      intro z
      calc
        ‖Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖
            = (‖Tfun z‖ * ‖G z‖) * rexp (-‖z‖ ^ 2) := by
                rw [norm_mul, norm_mul]
                rw [show ‖(starRingEnd ℂ) (G z)‖ = ‖G z‖ by simp]
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
        _ ≤ ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) := by
              nlinarith [sq_nonneg (‖Tfun z‖ - ‖G z‖), exp_nonneg (-‖z‖ ^ 2 : ℝ)]
    have hIntLe :
        ‖∫ z : ℂ, Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖ ≤
          ∫ z : ℂ, ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) :=
      MeasureTheory.norm_integral_le_of_norm_le hAvgInt hpt
    have hpi_nonneg : 0 ≤ (1 / Real.pi : ℝ) := by positivity
    have hAvgEq :
        (1 / Real.pi) * ∫ z : ℂ, ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) =
          (weightedNormSq Tfun + weightedNormSq G) / 2 := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      have hEq :
          (fun z : ℂ => ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2)) =
            (fun z : ℂ =>
              (1 / 2 : ℝ) *
                (‖Tfun z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
        funext z
        ring
      rw [hEq, MeasureTheory.integral_const_mul, MeasureTheory.integral_add hTInt hInt]
      ring
    have hpi_norm : ‖(1 / Real.pi : ℂ)‖ = (1 / Real.pi : ℝ) := by
      simpa [one_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ Real.pi by
        positivity)] using (norm_inv (Real.pi : ℂ))
    calc
      ‖weightedInner Tfun G‖
          = ‖(1 / Real.pi : ℂ) *
              ∫ z : ℂ, Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖ := by
                rfl
      _ = (1 / Real.pi : ℝ) *
          ‖∫ z : ℂ, Tfun z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)‖ := by
            rw [norm_mul, hpi_norm]
      _ ≤ (1 / Real.pi : ℝ) *
          ∫ z : ℂ, ((‖Tfun z‖ ^ 2 + ‖G z‖ ^ 2) / 2) * rexp (-‖z‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left hIntLe hpi_nonneg
      _ = (weightedNormSq Tfun + weightedNormSq G) / 2 := hAvgEq
  have hReEq : (weightedInner Tfun G).re = weightedNormSq Tfun := by
    calc
      (weightedInner Tfun G).re = (weightedInner Tfun Tfun).re := by
        simpa [Tfun] using congrArg Complex.re hCrossZero
      _ = weightedNormSq Tfun := (weightedNormSq_eq_re_weightedInner Tfun).symm
  have hTle : weightedNormSq Tfun ≤ weightedNormSq G := by
    have hmid : weightedNormSq Tfun ≤ (weightedNormSq Tfun + weightedNormSq G) / 2 := by
      calc
        weightedNormSq Tfun = (weightedInner Tfun G).re := hReEq.symm
        _ ≤ ‖weightedInner Tfun G‖ := Complex.re_le_norm _
        _ ≤ (weightedNormSq Tfun + weightedNormSq G) / 2 := hInnerNormLe
    linarith
  simpa [Tfun, hReEq] using hTle





private lemma summable_sq_Phi_eval (k : ℕ) (z : ℂ) :
    Summable (fun n => ‖Phi k n z‖ ^ 2) := by
  let R : ℝ := max 1 ‖z‖
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    exact le_max_right _ _
  let C : ℝ := (((2 : ℝ) ^ k) ^ 2 * (R ^ k) ^ 2) / (Nat.factorial k : ℝ)
  have hbase0 :
      Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (2 * k)) * (R ^ 2) ^ n / (Nat.factorial n : ℝ)) := by
    apply summable_nat_pow_mul_pow_div_factorial_nonneg
    positivity
  have hbase :
      Summable (fun n : ℕ => (((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
    refine hbase0.congr ?_
    intro n
    rw [← pow_mul, ← pow_mul]
    simp [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hmajorant :
      Summable (fun n : ℕ => C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ))) := by
    exact hbase.mul_left C
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hmajorant
  intro n
  have hphi := phi_norm_le_majorant (k := k) (n := n) (R := R) hR hzR
  have hrhs_nonneg :
      0 ≤ ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
        Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
    positivity
  have hphi_sq :
      ‖Phi k n z‖ ^ 2 ≤
        (((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hphi 2
  have hsqrt_ne : Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by
    positivity
  calc
    ‖Phi k n z‖ ^ 2
      ≤ (((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) ^ 2 := hphi_sq
    _ = C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
      dsimp [C]
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (by positivity)]


/-- Bessel bound for the partial Hermite coefficient squares. -/
private lemma sum_range_sq_hermiteCoeff_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    ∀ J, ∑ n ∈ Finset.range J, ‖hermiteCoeff k G n‖ ^ 2 ≤ weightedNormSq G := by
  intro J
  by_cases hJ : J = 0
  · simp [hJ]
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    positivity
  · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    rw [show ∑ n ∈ Finset.range (J' + 1), ‖hermiteCoeff k G n‖ ^ 2 =
        ∑ n : Fin (J' + 1), ‖hermiteCoeff k G n.1‖ ^ 2 by
          rw [Finset.sum_range]]
    rw [← truncate_normSq k J' G]
    exact bessel_truncate_le hG hG.1 J'


/-- Point evaluations are bounded on `H_k`. -/
theorem point_eval_bounded :
    ∀ {k : ℕ} (z : ℂ),
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ {G : ℂ → ℂ}, G ∈ Hk k → ‖G z‖ ≤ C * weightedNorm G := by
  intro k z
  let C : ℝ := Real.sqrt (∑' n : ℕ, ‖Phi k n z‖ ^ 2)
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro G hG
  let u : ℕ → ℝ := fun n => ‖hermiteCoeff k G n * Phi k n z‖
  have hsPhi := summable_sq_Phi_eval k z
  have hu_range : ∀ J, ∑ n ∈ Finset.range J, u n ≤ C * weightedNorm G := by
    intro J
    have hcoeffJ := sum_range_sq_hermiteCoeff_le hG J
    have hphiJ :
        ∑ n ∈ Finset.range J, ‖Phi k n z‖ ^ 2 ≤ ∑' n : ℕ, ‖Phi k n z‖ ^ 2 := by
      exact hsPhi.sum_le_tsum (Finset.range J) (fun _ _ => sq_nonneg _)
    have hnormsq_nonneg : 0 ≤ weightedNormSq G := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      positivity
    calc
      ∑ n ∈ Finset.range J, u n
          = ∑ n ∈ Finset.range J, ‖hermiteCoeff k G n‖ * ‖Phi k n z‖ := by
              apply Finset.sum_congr rfl
              intro n hn
              simp [u, norm_mul]
      _ ≤
          Real.sqrt (∑ n ∈ Finset.range J, ‖hermiteCoeff k G n‖ ^ 2) *
            Real.sqrt (∑ n ∈ Finset.range J, ‖Phi k n z‖ ^ 2) := by
              simpa using
                Real.sum_mul_le_sqrt_mul_sqrt (Finset.range J)
                  (fun n => ‖hermiteCoeff k G n‖) (fun n => ‖Phi k n z‖)
      _ ≤ Real.sqrt (weightedNormSq G) * Real.sqrt (∑' n : ℕ, ‖Phi k n z‖ ^ 2) := by
            exact mul_le_mul (Real.sqrt_le_sqrt hcoeffJ) (Real.sqrt_le_sqrt hphiJ)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = C * weightedNorm G := by
            dsimp [C]
            unfold weightedNorm HermiteLEAN.weightedNorm
            rw [mul_comm]
  have hu_summable : Summable u := by
    exact summable_of_sum_range_le (fun n => norm_nonneg _) hu_range
  have hnorm_series : Summable (fun n : ℕ => ‖hermiteCoeff k G n * Phi k n z‖) := by
    simpa [u] using hu_summable
  have htsum : (∑' n : ℕ, hermiteCoeff k G n * Phi k n z) = G z := by
    simpa [hermiteCoeff] using (hG.2 z).tsum_eq
  calc
    ‖G z‖ = ‖∑' n : ℕ, hermiteCoeff k G n * Phi k n z‖ := by
      rw [← htsum]
    _ ≤ ∑' n : ℕ, u n := by
      calc
        ‖∑' n : ℕ, hermiteCoeff k G n * Phi k n z‖
            ≤ ∑' n : ℕ, ‖hermiteCoeff k G n * Phi k n z‖ := norm_tsum_le_tsum_norm hnorm_series
        _ = ∑' n : ℕ, u n := by simp [u]
    _ ≤ C * weightedNorm G := by
      exact Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hu_range








































end HermitekLEAN
