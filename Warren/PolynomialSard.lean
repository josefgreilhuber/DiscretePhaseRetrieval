/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.WeakBezout.Main
import Warren.Transversality

/-!
# Sard's lemma for polynomials (properness form)

For a polynomial `p` in `n` real variables, the *critical set* is the common zero set of the
partial derivatives `∂p/∂xⱼ`.  This file proves `PolynomialSard.polynomial_sard`: the
critical set is finite, with the sharp bound `∏ dⱼ` where `dⱼ` bounds `deg ∂p/∂xⱼ`, under a
properness hypothesis at infinity: the leading forms of the partial derivatives have no
common **complex** zero except the origin (`ProperAtInfinity`).

The proof is a direct application of `WeakBezout.weak_bezout` to the complexified
partial derivatives: the real critical set embeds into the complex one, which is finite with
at most `∏ dⱼ` points.

The properness hypothesis is genuinely needed: `p = (x₀x₁ - 1)²` has the whole hyperbola
`x₀x₁ = 1` in its critical set.
-/

namespace PolynomialSard

open MvPolynomial

variable {n : ℕ}

/-! ## Definitions -/

/-- The complexification of a real polynomial. -/
noncomputable def toC (q : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.map (algebraMap ℝ ℂ) q

/-- The critical set of `p`: the common zero set of its partial derivatives. -/
def criticalSet (p : MvPolynomial (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ j, MvPolynomial.eval x (MvPolynomial.pderiv j p) = 0}

/-- Properness at infinity: the leading forms of the partial derivatives of `p`, viewed as
complex polynomials, have no common zero except the origin. -/
def ProperAtInfinity (p : MvPolynomial (Fin n) ℝ) (d : Fin n → ℕ) : Prop :=
  ∀ z : Fin n → ℂ,
    (∀ j, MvPolynomial.eval z
        (toC (MvPolynomial.homogeneousComponent (d j) (MvPolynomial.pderiv j p))) = 0)
      → z = 0

/-! ## Complexification toolkit -/

/-- Complexification of a point of `ℝⁿ`. -/
def toCPt (x : Fin n → ℝ) : Fin n → ℂ := Complex.ofReal ∘ x

lemma toCPt_injective : Function.Injective (toCPt (n := n)) :=
  Complex.ofReal_injective.comp_left

/-- Complexification commutes with taking homogeneous components. -/
lemma toC_homogeneousComponent (t : ℕ) (q : MvPolynomial (Fin n) ℝ) :
    toC (homogeneousComponent t q) = homogeneousComponent t (toC q) := by
  ext d
  simp only [toC, coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- Complexification preserves the total degree. -/
lemma totalDegree_toC (q : MvPolynomial (Fin n) ℝ) : (toC q).totalDegree = q.totalDegree := by
  simp only [toC, MvPolynomial.totalDegree,
    MvPolynomial.support_map_of_injective _ (algebraMap ℝ ℂ).injective]

/-- Evaluating a complexified polynomial at a complexified point. -/
lemma eval_toC (q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (toCPt x) (toC q) = ((MvPolynomial.eval x q : ℝ) : ℂ) := by
  have hcomp : ((MvPolynomial.eval (toCPt x)).comp
      (MvPolynomial.map (algebraMap ℝ ℂ) : MvPolynomial (Fin n) ℝ →+* MvPolynomial (Fin n) ℂ))
      = (algebraMap ℝ ℂ).comp (MvPolynomial.eval x) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp [toCPt]
  exact DFunLike.congr_fun hcomp q

/-! ## Finiteness of the critical set -/

/-- Under the properness hypothesis the critical set is finite, with at most `∏ dⱼ`
points. -/
theorem polynomial_sard (p : MvPolynomial (Fin n) ℝ) (d : Fin n → ℕ)
    (hd : ∀ j, 1 ≤ d j) (hdeg : ∀ j, (MvPolynomial.pderiv j p).totalDegree ≤ d j)
    (hproper : ProperAtInfinity p d) :
    (criticalSet p).Finite ∧ (criticalSet p).ncard ≤ ∏ j, d j := by
  classical
  -- the complexified partial derivatives
  have hdegP : ∀ j, (toC (pderiv j p)).totalDegree ≤ d j := by
    intro j; rw [totalDegree_toC]; exact hdeg j
  have hleadP : ∀ z : Fin n → ℂ,
      (∀ j, MvPolynomial.eval z (homogeneousComponent (d j) (toC (pderiv j p))) = 0) → z = 0 := by
    intro z hz
    refine hproper z fun j => ?_
    rw [toC_homogeneousComponent]
    exact hz j
  obtain ⟨hfin, hcard⟩ :=
    WeakBezout.weak_bezout (fun j => toC (pderiv j p)) d hd hdegP hleadP
  -- the real critical set embeds into the complex zero set
  have hsub : toCPt '' criticalSet p ⊆
      {z : Fin n → ℂ | ∀ j, MvPolynomial.eval z (toC (pderiv j p)) = 0} := by
    rintro _ ⟨x, hx, rfl⟩
    intro j
    rw [eval_toC]
    rw [hx j]
    simp
  have himfin := hfin.subset hsub
  refine ⟨Set.Finite.of_finite_image himfin toCPt_injective.injOn, ?_⟩
  calc (criticalSet p).ncard
      = (toCPt '' criticalSet p).ncard :=
        (Set.ncard_image_of_injective _ toCPt_injective).symm
    _ ≤ {z : Fin n → ℂ | ∀ j, MvPolynomial.eval z (toC (pderiv j p)) = 0}.ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ ∏ j, d j := hcard

end PolynomialSard
