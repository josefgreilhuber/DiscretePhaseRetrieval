/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.PolynomialSard
import Warren.Transversality

/-!
# Bounded components: the perturbed sum of squares

Given polynomials `p₁, …, pₘ` in `n` real variables, let `Σ pᵢ²` be their sum of squares (whose
real zero set is the joint zero set of the `pᵢ`).  This file studies the perturbation

  `pert p ε δ d = Σ pᵢ² − ε + δ · Σⱼ xⱼ^(2d+1)`,

where `d` bounds the degrees of the `pᵢ`.  The odd-degree tail `δ · Σⱼ xⱼ^(2d+1)` dominates the
partial derivatives at infinity: `∂ⱼ pert = ∂ⱼ(Σ pᵢ²) + (2d+1) δ xⱼ^(2d)`, whose leading form
`(2d+1) δ xⱼ^(2d)` has no common complex zero besides the origin.  Consequently the critical set
of `pert p ε δ d` is finite, with at most `(2d)^n` points (`criticalSet_pert_finite`), by
`PolynomialSard.polynomial_sard`.

We also record the size of the perturbation on a ball (`abs_eval_pert_sub_le`) and the bridge
between `fderiv` of the evaluation map and the critical set (`fderiv_eval_eq_zero_iff`).
-/

namespace BoundedComponents

open MvPolynomial

variable {n m : ℕ}

/-! ## Definitions -/

/-- The sum of squares `Σ pᵢ²`, whose real zero set is the joint zero set of the `pᵢ`. -/
noncomputable def sumSq (p : Fin m → MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, (p i) ^ 2

/-- The perturbed polynomial `Σ pᵢ² − ε + δ · Σⱼ xⱼ^(2d+1)`. -/
noncomputable def pert (p : Fin m → MvPolynomial (Fin n) ℝ) (ε δ : ℝ) (d : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  sumSq p - C ε + C δ * ∑ j, X j ^ (2 * d + 1)

/-! ## Evaluation of the sum of squares -/

theorem eval_sumSq (p : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    eval x (sumSq p) = ∑ i, (eval x (p i)) ^ 2 := by
  simp [sumSq]

theorem sumSq_nonneg (p : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    0 ≤ eval x (sumSq p) := by
  rw [eval_sumSq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem eval_sumSq_eq_zero_iff (p : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    eval x (sumSq p) = 0 ↔ ∀ i, eval x (p i) = 0 := by
  rw [eval_sumSq, Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _]
  simp

/-! ## Evaluation of the perturbation -/

theorem eval_pert (p : Fin m → MvPolynomial (Fin n) ℝ) (ε δ : ℝ) (d : ℕ) (x : Fin n → ℝ) :
    eval x (pert p ε δ d) = eval x (sumSq p) - ε + δ * ∑ j, (x j) ^ (2 * d + 1) := by
  simp [pert]

/-- On the ball of radius `R` the perturbation term is at most `|δ| n R^(2d+1)`.  (The
hypothesis `0 ≤ R` is implied by `‖x‖ ≤ R` and is kept only for convenience of callers.) -/
theorem abs_eval_pert_sub_le (p : Fin m → MvPolynomial (Fin n) ℝ) (ε δ : ℝ) (d : ℕ)
    (x : Fin n → ℝ) {R : ℝ} (hx : ‖x‖ ≤ R) (_hR : 0 ≤ R) :
    |eval x (pert p ε δ d) - (eval x (sumSq p) - ε)| ≤ |δ| * n * R ^ (2 * d + 1) := by
  rw [eval_pert, add_sub_cancel_left, abs_mul]
  have hj : ∀ j, |x j ^ (2 * d + 1)| ≤ R ^ (2 * d + 1) := by
    intro j
    rw [abs_pow]
    have hxj : |x j| ≤ R := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm x j).trans hx
    exact pow_le_pow_left₀ (abs_nonneg _) hxj _
  calc |δ| * |∑ j, x j ^ (2 * d + 1)|
      ≤ |δ| * ∑ j, |x j ^ (2 * d + 1)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |δ| * ∑ _j : Fin n, R ^ (2 * d + 1) := by
        gcongr with j
        exact hj j
    _ = |δ| * n * R ^ (2 * d + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-! ## Degrees -/

/-- Taking a partial derivative lowers the total degree by (at least) one. -/
theorem totalDegree_pderiv_le (q : MvPolynomial (Fin n) ℝ) (j : Fin n) (D : ℕ)
    (hq : q.totalDegree ≤ D + 1) : (pderiv j q).totalDegree ≤ D := by
  classical
  have hsum : pderiv j q = ∑ m ∈ q.support, pderiv j (monomial m (coeff m q)) := by
    conv_lhs => rw [q.as_sum]
    rw [map_sum]
  rw [hsum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hmj : m j = 0
  · rw [hmj, Nat.cast_zero, mul_zero, monomial_zero, totalDegree_zero]
    exact Nat.zero_le _
  · have hdeg : (m - Finsupp.single j 1).degree + 1 = m.degree := by
      have h := congrArg Finsupp.degree (Finsupp.sub_add_single_one_cancel hmj)
      rwa [map_add, Finsupp.degree_single] at h
    have h2 : m.degree ≤ D + 1 := (le_totalDegree hm).trans hq
    have h3 : (monomial (m - Finsupp.single j 1) (coeff m q * (m j : ℝ))).totalDegree
        ≤ (m - Finsupp.single j 1).degree := totalDegree_monomial_le _ _
    omega

theorem totalDegree_sumSq_le (p : Fin m → MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hdeg : ∀ i, (p i).totalDegree ≤ d) : (sumSq p).totalDegree ≤ 2 * d :=
  totalDegree_finsetSum_le fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hdeg i))

/-- The partial derivatives of `Σ pᵢ²` have degree `< 2d` (stated without ℕ-subtraction). -/
theorem totalDegree_pderiv_sumSq_add_one_le (p : Fin m → MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hd : 1 ≤ d) (hdeg : ∀ i, (p i).totalDegree ≤ d) (j : Fin n) :
    (pderiv j (sumSq p)).totalDegree + 1 ≤ 2 * d := by
  have h := totalDegree_pderiv_le (sumSq p) j (2 * d - 1)
    (by have := totalDegree_sumSq_le p hdeg; omega)
  omega

/-! ## Partial derivatives of the perturbation -/

theorem pderiv_pert (p : Fin m → MvPolynomial (Fin n) ℝ) (ε δ : ℝ) (d : ℕ) (j : Fin n) :
    pderiv j (pert p ε δ d)
      = pderiv j (sumSq p) + C ((2 * d + 1 : ℕ) * δ) * X j ^ (2 * d) := by
  classical
  simp only [pert, map_sub, map_add, pderiv_C, sub_zero, pderiv_C_mul, map_sum, pderiv_pow,
    pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Nat.add_sub_cancel]
  rw [map_mul, map_natCast]
  ring

theorem totalDegree_pderiv_pert_le (p : Fin m → MvPolynomial (Fin n) ℝ) (ε δ : ℝ) {d : ℕ}
    (hd : 1 ≤ d) (hdeg : ∀ i, (p i).totalDegree ≤ d) (j : Fin n) :
    (pderiv j (pert p ε δ d)).totalDegree ≤ 2 * d := by
  rw [pderiv_pert]
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · have := totalDegree_pderiv_sumSq_add_one_le p hd hdeg j
    omega
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X_pow, zero_add]

/-- The leading form of `∂ⱼ pert` is the monomial `(2d+1) δ xⱼ^(2d)`. -/
theorem homogeneousComponent_pderiv_pert (p : Fin m → MvPolynomial (Fin n) ℝ) (ε δ : ℝ)
    {d : ℕ} (hd : 1 ≤ d) (hdeg : ∀ i, (p i).totalDegree ≤ d) (j : Fin n) :
    homogeneousComponent (2 * d) (pderiv j (pert p ε δ d))
      = C ((2 * d + 1 : ℕ) * δ) * X j ^ (2 * d) := by
  have hlt : (pderiv j (sumSq p)).totalDegree < 2 * d := by
    have := totalDegree_pderiv_sumSq_add_one_le p hd hdeg j
    omega
  rw [pderiv_pert, map_add, homogeneousComponent_eq_zero _ _ hlt, zero_add]
  have hhom : (C ((2 * d + 1 : ℕ) * δ) * X j ^ (2 * d) : MvPolynomial (Fin n) ℝ).IsHomogeneous
      (2 * d) := by
    have := (isHomogeneous_C (Fin n) ((2 * d + 1 : ℕ) * δ)).mul ((isHomogeneous_X ℝ j).pow (2 * d))
    simpa using this
  rw [homogeneousComponent_of_mem hhom, if_pos rfl]

/-- The perturbation is proper at infinity in the sense of `PolynomialSard`. -/
theorem properAtInfinity_pert (p : Fin m → MvPolynomial (Fin n) ℝ) (ε δ : ℝ) {d : ℕ}
    (hd : 1 ≤ d) (hdeg : ∀ i, (p i).totalDegree ≤ d) (hδ : δ ≠ 0) :
    PolynomialSard.ProperAtInfinity (pert p ε δ d) (fun _ => 2 * d) := by
  intro z hz
  funext j
  have h := hz j
  simp only [homogeneousComponent_pderiv_pert p ε δ hd hdeg, PolynomialSard.toC, map_mul, map_C,
    map_pow, map_X, eval_C, eval_X] at h
  have hc : (algebraMap ℝ ℂ) ((2 * d + 1 : ℕ) : ℝ) * (algebraMap ℝ ℂ) δ ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).2 (Nat.cast_ne_zero.2 (by omega))) ((map_ne_zero _).2 hδ)
  have h2d : 2 * d ≠ 0 := by omega
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd h1 hc
  · exact (pow_eq_zero_iff h2d).1 h1

/-! ## Finiteness of the critical set -/

/-- **Main deliverable.** The critical set of the perturbed sum of squares is finite, with at
most `(2d)^n` points. -/
theorem criticalSet_pert_finite (p : Fin m → MvPolynomial (Fin n) ℝ) (ε δ : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hdeg : ∀ i, (p i).totalDegree ≤ d) (hδ : δ ≠ 0) :
    (PolynomialSard.criticalSet (pert p ε δ d)).Finite ∧
    (PolynomialSard.criticalSet (pert p ε δ d)).ncard ≤ (2 * d) ^ n := by
  have h := PolynomialSard.polynomial_sard (pert p ε δ d) (fun _ => 2 * d)
    (fun _ => by omega) (fun j => totalDegree_pderiv_pert_le p ε δ hd hdeg j)
    (properAtInfinity_pert p ε δ hd hdeg hδ)
  simpa using h

/-! ## Bridge to `fderiv` -/

/-- The differential of `x ↦ q(x)` vanishes at `x` exactly when `x` is a critical point. -/
theorem fderiv_eval_eq_zero_iff (q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    fderiv ℝ (fun y => eval y q) x = 0 ↔ x ∈ PolynomialSard.criticalSet q := by
  rw [(AlgebraicTransversality.hasFDerivAt_eval q x).fderiv]
  constructor
  · intro h j
    have hj := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) h
    simp only [AlgebraicTransversality.dualCLM_single, ContinuousLinearMap.zero_apply] at hj
    exact hj
  · intro h
    have hg : AlgebraicTransversality.gradient q x = 0 := funext fun j => h j
    rw [hg]
    ext v
    simp

end BoundedComponents
