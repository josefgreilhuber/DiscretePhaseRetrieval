/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-!
# Two consequences of Lagrange interpolation

* `Remez.abs_eval_le_sum`: for a polynomial `p` of degree `< |s|` and distinct nodes `v i`,
  `|p(y)| ≤ ∑ᵢ |p(vᵢ)| ∏_{j ≠ i} |y - vⱼ| / |vᵢ - vⱼ|`.
* `Remez.eval_T_eq_sum`: for `y ≥ 1` the Chebyshev polynomial satisfies
  `Tₙ(y) = ∑ᵢ ∏_{j ≠ i} |y - ηⱼ| / |ηᵢ - ηⱼ|`, where `η₀ > η₁ > ⋯ > ηₙ` are its extremal
  points `ηᵢ = cos (iπ/n)` in `[-1, 1]` (`Polynomial.Chebyshev.node`).  This is the Lagrange
  interpolation formula for `Tₙ` at its extremal points, where all terms have the same sign.
-/

open Polynomial Finset

namespace Remez

variable {ι : Type*} [DecidableEq ι]

/-- Lagrange interpolation bound. -/
theorem abs_eval_le_sum (s : Finset ι) {v : ι → ℝ} (hv : Set.InjOn v s) {p : ℝ[X]}
    (hp : p.degree < s.card) (y : ℝ) :
    |p.eval y| ≤ ∑ i ∈ s, |p.eval (v i)| * ∏ j ∈ s.erase i, (|y - v j| / |v i - v j|) := by
  conv_lhs => rw [Lagrange.eq_interpolate hv hp]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => le_of_eq ?_)
  rw [eval_mul, eval_C, abs_mul, Lagrange.basis, eval_prod, abs_prod]
  congr 1
  refine prod_congr rfl fun j _ => ?_
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, abs_mul, abs_inv]
  rw [div_eq_inv_mul]

open Polynomial.Chebyshev in
/-- Lagrange interpolation of `Tₙ` at its extremal points, for `y ≥ 1`. -/
theorem eval_T_eq_sum (n : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    (T ℝ n).eval y = ∑ i ∈ range (n + 1),
      ∏ j ∈ (range (n + 1)).erase i, (|y - node n j| / |node n i - node n j|) := by
  have hdeg : (T ℝ n).degree < (range (n + 1)).card := by
    rw [degree_T, card_range, Int.natAbs_natCast]
    exact_mod_cast Nat.lt_succ_self n
  conv_lhs => rw [Lagrange.eq_interpolate (strictAntiOn_node n).injOn hdeg]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  have hin : i ≤ n := Nat.lt_succ_iff.1 hi
  rw [eval_mul, eval_C, eval_T_real_node (Finset.mem_Iic.2 hin), Lagrange.basis, eval_prod]
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  rw [prod_mul_distrib, prod_inv_distrib, prod_div_distrib, ← abs_prod, ← abs_prod]
  set D := ∏ j ∈ (range (n + 1)).erase i, (node n i - node n j) with hD_def
  set N := ∏ j ∈ (range (n + 1)).erase i, (y - node n j) with hN_def
  have hD := zero_lt_prod_node_sub_node hin
  rw [← hD_def] at hD
  have hN : 0 ≤ N :=
    prod_nonneg fun j _ => sub_nonneg.2 ((node_mem_Icc (n := n) (i := j)).2.trans hy)
  have hDabs : |D| = (-1) ^ i * D := by
    rw [← abs_of_pos hD, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_nonneg hN, hDabs]
  have hDne : D ≠ 0 := by
    intro h
    rw [h, mul_zero] at hD
    exact lt_irrefl _ hD
  rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] at hD ⊢ <;> field_simp

open Polynomial.Chebyshev in
/-- `Tₙ` is monotone on `[1, ∞)`: every term of `eval_T_eq_sum` is increasing in `y`. -/
theorem monotoneOn_eval_T (n : ℕ) : MonotoneOn (fun y => (T ℝ n).eval y) (Set.Ici 1) := by
  intro y hy y' hy' hyy'
  simp only
  rw [eval_T_eq_sum n hy, eval_T_eq_sum n hy']
  refine sum_le_sum fun i _ => prod_le_prod (fun j _ => by positivity) fun j _ => ?_
  have hj1 := (node_mem_Icc (n := n) (i := j)).2
  have hy1 := Set.mem_Ici.1 hy
  have hy1' := Set.mem_Ici.1 hy'
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

end Remez
