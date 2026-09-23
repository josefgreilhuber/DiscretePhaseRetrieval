/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-! # Weak Bezout: Interpolation

Multivariate Lagrange interpolation bound: if `N` distinct points of `kⁿ` all lie in the
vanishing locus of an ideal `I` of `k[X₁, …, Xₙ]` whose quotient is finite-dimensional over
the field `k`, then `N ≤ dim_k (k[X₁, …, Xₙ] ⧸ I)`.

The proof evaluates polynomials at the `N` points, giving a linear map
`k[X₁, …, Xₙ] ⧸ I →ₗ[k] (Fin N → k)`, and shows it is surjective by constructing, for each
point, a polynomial (a product of degree-one separating polynomials) that is nonzero at that
point and zero at all the others.
-/

namespace WeakBezout

open MvPolynomial

/-- For two distinct points of `kⁿ` there is a polynomial vanishing at the first point but not
at the second: take `Xᵢ - C (a i)` for a coordinate `i` where the points differ. -/
theorem exists_separating {n : ℕ} {k : Type*} [Field k] (a b : Fin n → k) (h : a ≠ b) :
    ∃ f : MvPolynomial (Fin n) k, eval a f = 0 ∧ eval b f ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  refine ⟨X i - C (a i), by simp, ?_⟩
  simp only [map_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (Ne.symm hi)

/-- **Multivariate Lagrange interpolation bound.** If `N` distinct points of `kⁿ` are common
zeros of an ideal `I ⊆ k[X₁, …, Xₙ]` with finite-dimensional quotient, then
`N ≤ dim_k (k[X₁, …, Xₙ] ⧸ I)`. -/
theorem card_le_finrank_quotient {n N : ℕ} {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin N → (Fin n → k)) (hinj : Function.Injective x)
    (hzero : ∀ (j : Fin N) (f : MvPolynomial (Fin n) k), f ∈ I → MvPolynomial.eval (x j) f = 0)
    [FiniteDimensional k (MvPolynomial (Fin n) k ⧸ I)] :
    N ≤ Module.finrank k (MvPolynomial (Fin n) k ⧸ I) := by
  classical
  -- The simultaneous-evaluation algebra homomorphism.
  let ev : MvPolynomial (Fin n) k →ₐ[k] (Fin N → k) :=
    Pi.algHom k (fun _ => k) fun j => MvPolynomial.aeval (x j)
  have hIev : ∀ f ∈ I, ev f = 0 := by
    intro f hf
    funext j
    exact hzero j f hf
  -- It kills `I`, hence factors through the quotient.
  let φ : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] (Fin N → k) := Ideal.Quotient.liftₐ I ev hIev
  have hφmk : ∀ (f : MvPolynomial (Fin n) k) (i : Fin N),
      φ (Ideal.Quotient.mk I f) i = eval (x i) f := fun f i => rfl
  -- For each point `x j`, a polynomial nonzero at `x j` and zero at all other points.
  have key : ∀ j : Fin N, ∃ f : MvPolynomial (Fin n) k,
      eval (x j) f ≠ 0 ∧ ∀ i : Fin N, i ≠ j → eval (x i) f = 0 := by
    intro j
    have step : ∀ i : Fin N, ∃ f : MvPolynomial (Fin n) k,
        (i ≠ j → eval (x i) f = 0) ∧ eval (x j) f ≠ 0 := by
      intro i
      by_cases hij : i = j
      · exact ⟨1, fun h => absurd hij h, by simp⟩
      · obtain ⟨f, hf0, hf1⟩ := exists_separating (x i) (x j) (hinj.ne hij)
        exact ⟨f, fun _ => hf0, hf1⟩
    choose f hf0 hf1 using step
    refine ⟨∏ i ∈ Finset.univ.erase j, f i, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hf1 i
    · intro i hij
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) (hf0 i hij)
  -- The factored evaluation map is surjective: its range contains every `Pi.single j 1`.
  have hsurj : Function.Surjective φ.toLinearMap := by
    have hsingle : ∀ j : Fin N,
        (Pi.single j 1 : Fin N → k) ∈ LinearMap.range φ.toLinearMap := by
      intro j
      obtain ⟨g, hg, hg0⟩ := key j
      refine ⟨Ideal.Quotient.mk I (C (eval (x j) g)⁻¹ * g), funext fun i => ?_⟩
      change φ (Ideal.Quotient.mk I (C (eval (x j) g)⁻¹ * g)) i
          = (Pi.single j 1 : Fin N → k) i
      rw [hφmk, map_mul, eval_C]
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same, inv_mul_cancel₀ hg]
      · rw [hg0 i hij, mul_zero, Pi.single_eq_of_ne hij]
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun k (Fin N)).span_eq,
      Submodule.span_le]
    rintro v ⟨j, rfl⟩
    simpa only [Pi.basisFun_apply, SetLike.mem_coe] using hsingle j
  -- Conclude by comparing dimensions.
  have hN : Module.finrank k (Fin N → k) = N := by
    rw [Module.finrank_pi, Fintype.card_fin]
  calc N = Module.finrank k (Fin N → k) := hN.symm
    _ ≤ Module.finrank k (MvPolynomial (Fin n) k ⧸ I) :=
      LinearMap.finrank_le_finrank_of_surjective hsurj

end WeakBezout
