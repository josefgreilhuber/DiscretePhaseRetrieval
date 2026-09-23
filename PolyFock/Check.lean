/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.TailBound

/-!
# Sanity checks and axiom audit

This file records that the development is `sorry`-free and rests only on Lean's three
standard axioms, and it checks that the objects defined are the intended ones (the comparator's
basis `DiscretePR.HermitePoly` of `Definitions.lean`, which this development uses throughout,
takes the expected values in low degree, and the hypotheses of the tail bound are satisfiable).
-/

namespace PolyFock

open Finset
open DiscretePR (HermitePoly)

/-! ### The basis functions are the intended ones -/

example (z : ℂ) : HermitePoly 0 0 z = 1 := by
  rw [HermitePoly]
  norm_num

example (z : ℂ) : HermitePoly 1 0 z = z := by
  rw [HermitePoly]
  norm_num

example (z : ℂ) : HermitePoly 1 1 z = z * (starRingEnd ℂ) z - 1 := by
  rw [HermitePoly]
  simp only [RCLike.star_def]
  norm_num [Finset.sum_range_succ]
  ring

/-! ### The hypotheses of the tail bound are satisfiable -/

example : ∃ L N : ℕ, 3 * L ≤ N ∧ L + 9 ≤ N ∧ Real.exp 1 * (1 : ℝ) ^ 2 < (N : ℝ) := by
  refine ⟨1, 10, by norm_num, by norm_num, ?_⟩
  have := Real.exp_one_lt_d9
  norm_num
  linarith

/-! ### Axiom audit -/

#print axioms tail_bound
#print axioms tail_bound_sqrt
#print axioms tailKernelDiag_radialPoint_le
#print axioms tailKernelDiag_le_of_radial_bound
#print axioms Fock.layer_kernel_rot
#print axioms Fock.form_Psihat
#print axioms Fock.T_R

end PolyFock
