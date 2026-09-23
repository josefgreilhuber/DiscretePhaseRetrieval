/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Fock.Basic

/-!
# Creation and annihilation operators for the Fock form

The integration-by-parts identities of `PolyFock.Fock.Basic` say exactly that the operator

`Aᵢ = zᵢ · (–) − ∂_{z̄ᵢ}`

is the adjoint of `∂_{zᵢ}` for the Fock form, and likewise `Bᵢ = z̄ᵢ · (–) − ∂_{zᵢ}` is the
adjoint of `∂_{z̄ᵢ}`.  Together with the commutation relations `[∂_{zᵢ}, A_j] = δᵢⱼ`,
`[∂_{zᵢ}, B_j] = 0` this is all that is needed for the orthogonality computation.
-/

namespace PolyFock.Fock

open Finset MvPolynomial

noncomputable section

variable {d : ℕ}

/-! ### `σ` intertwines the two families of derivatives -/

lemma mapDomain_swap_apply (η : Idx d →₀ ℕ) (x : Idx d) :
    (η.mapDomain Sum.swap) x = η x.swap := by
  classical
  have hinj : Function.Injective (Sum.swap : Idx d → Idx d) := fun a b h => by
    have h2 := congrArg Sum.swap h
    simpa using h2
  have h := Finsupp.mapDomain_apply hinj η x.swap
  simpa using h

lemma mapDomain_swap_sub (η : Idx d →₀ ℕ) (x : Idx d) :
    (η - Finsupp.single x 1).mapDomain Sum.swap
      = η.mapDomain Sum.swap - Finsupp.single x.swap 1 := by
  classical
  ext y
  rw [mapDomain_swap_apply, Finsupp.tsub_apply, Finsupp.tsub_apply, mapDomain_swap_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  congr 1
  by_cases h : x = y.swap
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hc
    exact h (by rw [← hc]; simp)

lemma sig_pderiv_inl (i : Fin d) (p : P d) :
    sig ((pderiv (Sum.inl i)) p) = (pderiv (Sum.inr i)) (sig p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial ν c =>
      rw [pderiv_monomial, sig_monomial, sig_monomial, pderiv_monomial,
        mapDomain_swap_sub, mapDomain_swap_apply]
      simp
  | add p q hp hq => simp [map_add, hp, hq]

lemma sig_pderiv_inr (i : Fin d) (p : P d) :
    sig ((pderiv (Sum.inr i)) p) = (pderiv (Sum.inl i)) (sig p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial ν c =>
      rw [pderiv_monomial, sig_monomial, sig_monomial, pderiv_monomial,
        mapDomain_swap_sub, mapDomain_swap_apply]
      simp
  | add p q hp hq => simp [map_add, hp, hq]

/-! ### The creation operators -/

/-- The creation operator `Aᵢ = zᵢ · (–) − ∂_{z̄ᵢ}`, adjoint to `∂_{zᵢ}`. -/
def A (i : Fin d) (p : P d) : P d := X (Sum.inl i) * p - (pderiv (Sum.inr i)) p

/-- The creation operator `Bᵢ = z̄ᵢ · (–) − ∂_{zᵢ}`, adjoint to `∂_{z̄ᵢ}`. -/
def B (i : Fin d) (p : P d) : P d := X (Sum.inr i) * p - (pderiv (Sum.inl i)) p

lemma T_sub (u v : P d) : T (u - v) = T u - T v := by
  simpa using map_sub (Tl (d := d)) u v

/-- **Adjointness**: `⟪Aᵢ p, q⟫ = ⟪p, ∂_{zᵢ} q⟫`. -/
lemma form_A (i : Fin d) (p q : P d) :
    form (A i p) q = form p ((pderiv (Sum.inl i)) q) := by
  have h1 : T (X (Sum.inl i) * (p * sig q)) = T ((pderiv (Sum.inr i)) (p * sig q)) :=
    T_X_inl_mul i _
  have h2 : (pderiv (Sum.inr i)) (p * sig q)
      = (pderiv (Sum.inr i)) p * sig q + p * (pderiv (Sum.inr i)) (sig q) := pderiv_mul
  rw [form, form, A, sub_mul, T_sub, mul_assoc, h1, h2, T_add, sig_pderiv_inl]
  ring

/-- **Adjointness**: `⟪Bᵢ p, q⟫ = ⟪p, ∂_{z̄ᵢ} q⟫`. -/
lemma form_B (i : Fin d) (p q : P d) :
    form (B i p) q = form p ((pderiv (Sum.inr i)) q) := by
  have h1 : T (X (Sum.inr i) * (p * sig q)) = T ((pderiv (Sum.inl i)) (p * sig q)) :=
    T_X_inr_mul i _
  have h2 : (pderiv (Sum.inl i)) (p * sig q)
      = (pderiv (Sum.inl i)) p * sig q + p * (pderiv (Sum.inl i)) (sig q) := pderiv_mul
  rw [form, form, B, sub_mul, T_sub, mul_assoc, h1, h2, T_add, sig_pderiv_inr]
  ring

end

end PolyFock.Fock
