/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Remez.Multivariate.Defs

/-!
# Restriction of a multivariate polynomial to a line

For `P : MvPolynomial (Fin m) ℝ` and points `x θ : Fin m → ℝ` we define the univariate
polynomial `lineRestrict P x θ`, obtained by substituting the affine parametrisation
`r ↦ x + r • θ` of the line through `x` in direction `θ` into `P`.

The two basic facts proved here are that evaluating `lineRestrict P x θ` at `r` gives
`P (x + r • θ)` (`Remez.eval_lineRestrict`), and that the degree of the restriction is bounded
by the total degree of `P` (`Remez.natDegree_lineRestrict_le`).  Together they let one transfer
univariate results (such as the classical Remez inequality) to lines in `ℝᵐ`.
-/

open Polynomial

namespace Remez

variable {m : ℕ}

/-- The univariate polynomial `r ↦ P (x + r • θ)`, the restriction of `P` to the line through
`x` in direction `θ`. -/
noncomputable def lineRestrict (P : MvPolynomial (Fin m) ℝ) (x θ : Fin m → ℝ) : ℝ[X] :=
  MvPolynomial.aeval (fun i => C (x i) + C (θ i) * X) P

/-- Evaluating the restriction of `P` to a line at the parameter `r` is the same as evaluating
`P` at the corresponding point `x + r • θ` of the line. -/
theorem eval_lineRestrict (P : MvPolynomial (Fin m) ℝ) (x θ : Fin m → ℝ) (r : ℝ) :
    (lineRestrict P x θ).eval r = MvPolynomial.eval (x + r • θ) P := by
  unfold lineRestrict
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, hp, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring

/-- Each linear factor `C (x i) + C (θ i) * X` used in the parametrisation of the line has
degree at most one. -/
private theorem natDegree_lineFactor_le (x θ : Fin m → ℝ) (i : Fin m) :
    (C (x i) + C (θ i) * X : ℝ[X]).natDegree ≤ 1 := by
  rw [add_comm]
  exact natDegree_linear_le

/-- The restriction of `P` to a line has degree at most the total degree of `P`. -/
theorem natDegree_lineRestrict_le (P : MvPolynomial (Fin m) ℝ) (x θ : Fin m → ℝ) :
    (lineRestrict P x θ).natDegree ≤ P.totalDegree := by
  rw [lineRestrict, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Polynomial.algebraMap_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  calc (∏ i, (C (x i) + C (θ i) * X : ℝ[X]) ^ d i).natDegree
      ≤ ∑ i, ((C (x i) + C (θ i) * X : ℝ[X]) ^ d i).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ i, d i := Finset.sum_le_sum fun i _ => natDegree_pow_le.trans <| by
        simpa using Nat.mul_le_mul_left (d i) (natDegree_lineFactor_le x θ i)
    _ ≤ d.sum fun _ e => e := by
        rw [Finsupp.sum_fintype]
        intros
        rfl
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

end Remez
