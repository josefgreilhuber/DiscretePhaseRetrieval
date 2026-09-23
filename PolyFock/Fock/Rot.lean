/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Fock.Ortho

/-!
# The rotation action on `ℂ[z, z̄]`

For a matrix `U` we let `R U` be the algebra endomorphism of `ℂ[z, z̄]` determined by

`zᵢ ↦ ∑ⱼ Uᵢⱼ zⱼ`,  `z̄ᵢ ↦ ∑ⱼ conj(Uᵢⱼ) z̄ⱼ`,

so that `ev z (R U p) = ev (U z) p`: it is precomposition with the linear map `z ↦ U z`.

The main results are the chain rule for `R U`, and — for **unitary** `U` — the invariance
`T ∘ R U = T` and hence `⟪R U p, R U q⟫ = ⟪p, q⟫`.
-/

namespace PolyFock.Fock

open Finset MvPolynomial Matrix

noncomputable section

variable {d : ℕ}

/-- The substitution `zᵢ ↦ ∑ⱼ Uᵢⱼ zⱼ`, `z̄ᵢ ↦ ∑ⱼ conj(Uᵢⱼ) z̄ⱼ`. -/
def rotVar (U : Matrix (Fin d) (Fin d) ℂ) : Idx d → P d
  | Sum.inl i => ∑ j, C (U i j) * X (Sum.inl j)
  | Sum.inr i => ∑ j, C ((starRingEnd ℂ) (U i j)) * X (Sum.inr j)

/-- Precomposition with the linear map `z ↦ U z`, as an algebra endomorphism of `ℂ[z, z̄]`. -/
def R (U : Matrix (Fin d) (Fin d) ℂ) : P d →ₐ[ℂ] P d := MvPolynomial.aeval (rotVar U)

@[simp] lemma R_X_inl (U : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    R U (X (Sum.inl i)) = ∑ j, C (U i j) * X (Sum.inl j) := by simp [R, rotVar]

@[simp] lemma R_X_inr (U : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    R U (X (Sum.inr i)) = ∑ j, C ((starRingEnd ℂ) (U i j)) * X (Sum.inr j) := by simp [R, rotVar]

/-! ### `R U` is precomposition with `z ↦ U z` -/

lemma ev_R (U : Matrix (Fin d) (Fin d) ℂ) (z : Fin d → ℂ) (p : P d) :
    ev z (R U p) = ev (U *ᵥ z) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [R, ev]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
      rw [map_mul, map_mul, map_mul, hp]
      congr 1
      cases v with
      | inl i =>
          rw [R_X_inl, ev_X_inl, map_sum]
          simp [Matrix.mulVec, dotProduct, ev]
      | inr i =>
          rw [R_X_inr, ev_X_inr, map_sum]
          simp [Matrix.mulVec, dotProduct, ev, map_sum]

/-! ### `σ` commutes with `R U` -/

lemma sig_R (U : Matrix (Fin d) (Fin d) ℂ) (p : P d) : sig (R U p) = R U (sig p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [R, sig]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
      rw [map_mul, map_mul, map_mul, map_mul, hp]
      congr 1
      cases v with
      | inl i =>
          rw [R_X_inl, sig_X_inl, R_X_inr, map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_mul, sig_C, sig_X_inl]
      | inr i =>
          rw [R_X_inr, sig_X_inr, R_X_inl, map_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [map_mul, sig_C, sig_X_inr, Complex.conj_conj]

/-! ### The chain rule -/

lemma pderiv_aeval (f : Idx d → P d) (v : Idx d) (p : P d) :
    (pderiv v) (aeval f p) = ∑ w : Idx d, (aeval f) ((pderiv w) p) * (pderiv v) (f w) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_mul, ← Finset.sum_add_distrib]
  | mul_X p w₀ hp =>
      rw [map_mul, aeval_X, pderiv_mul, hp, Finset.sum_mul]
      have hsum : ∀ w : Idx d, (aeval f) ((pderiv w) (p * X w₀)) * (pderiv v) (f w)
          = (aeval f) ((pderiv w) p) * (pderiv v) (f w) * f w₀
            + (if w = w₀ then (aeval f) p * (pderiv v) (f w) else 0) := by
        intro w
        rw [pderiv_mul, map_add, map_mul, aeval_X, add_mul]
        congr 1
        · ring
        · by_cases hw : w = w₀
          · subst hw; simp
          · rw [pderiv_X_of_ne (Ne.symm hw), if_neg hw]
            simp
      rw [Finset.sum_congr rfl fun w _ => hsum w, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ w₀ (fun w => (aeval f) p * (pderiv v) (f w))]
      simp

lemma pderiv_inl_R (U : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) (p : P d) :
    (pderiv (Sum.inl j)) (R U p) = ∑ k, C (U k j) * R U ((pderiv (Sum.inl k)) p) := by
  classical
  have h1 : ∀ k : Fin d, (pderiv (Sum.inl j)) (rotVar U (Sum.inl k)) = C (U k j) := by
    intro k
    simp only [rotVar, map_sum, pderiv_mul, pderiv_C, zero_mul, zero_add]
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl
      rw [pderiv_X_of_ne (by simpa using hl : (Sum.inl l : Idx d) ≠ Sum.inl j)]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  have h2 : ∀ k : Fin d, (pderiv (Sum.inl j)) (rotVar U (Sum.inr k)) = 0 := by
    intro k
    simp only [rotVar, map_sum, pderiv_mul, pderiv_C, zero_mul, zero_add]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [pderiv_X_of_ne (by simp : (Sum.inr l : Idx d) ≠ Sum.inl j)]
    simp
  rw [R, pderiv_aeval, Fintype.sum_sum_type]
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma pderiv_inr_R (U : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) (p : P d) :
    (pderiv (Sum.inr j)) (R U p)
      = ∑ k, C ((starRingEnd ℂ) (U k j)) * R U ((pderiv (Sum.inr k)) p) := by
  classical
  have h1 : ∀ k : Fin d,
      (pderiv (Sum.inr j)) (rotVar U (Sum.inr k)) = C ((starRingEnd ℂ) (U k j)) := by
    intro k
    simp only [rotVar, map_sum, pderiv_mul, pderiv_C, zero_mul, zero_add]
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl
      rw [pderiv_X_of_ne (by simpa using hl : (Sum.inr l : Idx d) ≠ Sum.inr j)]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  have h2 : ∀ k : Fin d, (pderiv (Sum.inr j)) (rotVar U (Sum.inl k)) = 0 := by
    intro k
    simp only [rotVar, map_sum, pderiv_mul, pderiv_C, zero_mul, zero_add]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [pderiv_X_of_ne (by simp : (Sum.inl l : Idx d) ≠ Sum.inr j)]
    simp
  rw [R, pderiv_aeval, Fintype.sum_sum_type]
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-! ### `T` is determined by integration by parts -/

lemma monomial_peel (ν : Idx d →₀ ℕ) (v : Idx d) (hv : ν v ≠ 0) (c : ℂ) :
    (monomial ν c : P d) = X v * monomial (ν - Finsupp.single v 1) c := by
  classical
  have hsplit : (Finsupp.single v 1 : Idx d →₀ ℕ) + (ν - Finsupp.single v 1) = ν := by
    ext w
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases h : v = w
    · subst h; rw [if_pos rfl]; omega
    · rw [if_neg h]; omega
  rw [X, MvPolynomial.monomial_mul, one_mul, hsplit]

@[simp] lemma T_C (c : ℂ) : T (C c : P d) = c := by
  rw [MvPolynomial.C_apply, T_monomial, wt]
  simp

private lemma T_unique_aux (S : P d →ₗ[ℂ] ℂ) (h1 : ∀ c : ℂ, S (C c) = c)
    (h2 : ∀ (i : Fin d) (u : P d), S (X (Sum.inl i) * u) = S ((pderiv (Sum.inr i)) u))
    (h3 : ∀ (i : Fin d) (u : P d), S (X (Sum.inr i) * u) = S ((pderiv (Sum.inl i)) u)) :
    ∀ (N : ℕ) (ν : Idx d →₀ ℕ) (c : ℂ), ν.degree ≤ N → S (monomial ν c) = T (monomial ν c) := by
  classical
  intro N
  induction N with
  | zero =>
      intro ν c hν
      have hν0 : ν = 0 := (Finsupp.degree_eq_zero_iff ν).mp (Nat.le_zero.mp hν)
      subst hν0
      rw [← MvPolynomial.C_apply, h1, T_C]
  | succ N ih =>
      intro ν c hν
      by_cases hz : ∀ v : Idx d, ν v = 0
      · have hν0 : ν = 0 := by ext v; simpa using hz v
        subst hν0
        rw [← MvPolynomial.C_apply, h1, T_C]
      · obtain ⟨v, hv⟩ : ∃ v : Idx d, ν v ≠ 0 := by
          by_contra hc
          exact hz fun v => by simpa using not_exists.mp hc v
        have hdg : (ν - Finsupp.single v 1).degree ≤ N := by
          have hsplit : Finsupp.single v 1 + (ν - Finsupp.single v 1) = ν := by
            ext w
            rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
            by_cases h : v = w
            · subst h; rw [if_pos rfl]; omega
            · rw [if_neg h]; omega
          have := map_add Finsupp.degree (Finsupp.single v 1) (ν - Finsupp.single v 1)
          rw [hsplit, Finsupp.degree_single] at this
          omega
        rw [monomial_peel ν v hv c]
        cases v with
        | inl i =>
            rw [h2, T_X_inl_mul, pderiv_monomial]
            exact ih _ _ (le_trans (Finsupp.degree_mono tsub_le_self) hdg)
        | inr i =>
            rw [h3, T_X_inr_mul, pderiv_monomial]
            exact ih _ _ (le_trans (Finsupp.degree_mono tsub_le_self) hdg)

/-- `T` is the unique linear functional with `T (C c) = c` satisfying the two
integration-by-parts identities. -/
lemma T_unique (S : P d →ₗ[ℂ] ℂ) (h1 : ∀ c : ℂ, S (C c) = c)
    (h2 : ∀ (i : Fin d) (u : P d), S (X (Sum.inl i) * u) = S ((pderiv (Sum.inr i)) u))
    (h3 : ∀ (i : Fin d) (u : P d), S (X (Sum.inr i) * u) = S ((pderiv (Sum.inl i)) u))
    (p : P d) : S p = T p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial ν c => exact T_unique_aux S h1 h2 h3 ν.degree ν c le_rfl
  | add p q hp hq => rw [map_add, T_add, hp, hq]

/-! ### Unitary invariance of the Gaussian expectation -/

lemma T_sum {ι : Type*} (s : Finset ι) (f : ι → P d) :
    T (∑ x ∈ s, f x) = ∑ x ∈ s, T (f x) :=
  map_sum (Tl (d := d)) f s

lemma T_C_mul (c : ℂ) (u : P d) : T (C c * u) = c * T u := by
  rw [← MvPolynomial.smul_eq_C_mul, T_smul]

lemma unitary_row_sum {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (i k : Fin d) : ∑ j, U i j * (starRingEnd ℂ) (U k j) = if i = k then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) k
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.star_apply, RCLike.star_def]

lemma unitary_row_sum' {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (i k : Fin d) : ∑ j, (starRingEnd ℂ) (U i j) * U k j = if i = k then 1 else 0 := by
  have h := unitary_row_sum hU i k
  have h2 : (starRingEnd ℂ) (∑ j, U i j * (starRingEnd ℂ) (U k j))
      = ∑ j, (starRingEnd ℂ) (U i j) * U k j := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, Complex.conj_conj]
  rw [← h2, h]
  split <;> simp

/-- **Invariance of the Gaussian expectation under `U(d)`.**  This is the algebraic form of
the fact that the Gaussian measure `e^{-|z|²}` is rotation invariant. -/
theorem T_R {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (p : P d) :
    T (R U p) = T p := by
  classical
  refine T_unique (Tl.comp (R U).toLinearMap) ?_ ?_ ?_ p
  · intro c
    change T (R U (C c)) = c
    rw [R, aeval_C, MvPolynomial.algebraMap_eq, T_C]
  · intro i u
    change T (R U (X (Sum.inl i) * u)) = T (R U ((pderiv (Sum.inr i)) u))
    rw [map_mul, R_X_inl, Finset.sum_mul, T_sum]
    have step1 : ∀ j : Fin d, T (C (U i j) * X (Sum.inl j) * R U u)
        = U i j * T ((pderiv (Sum.inr j)) (R U u)) := by
      intro j
      rw [mul_assoc, T_C_mul, T_X_inl_mul]
    have step2 : ∀ j : Fin d, T ((pderiv (Sum.inr j)) (R U u))
        = ∑ k, (starRingEnd ℂ) (U k j) * T (R U ((pderiv (Sum.inr k)) u)) := by
      intro j
      rw [pderiv_inr_R, T_sum]
      exact Finset.sum_congr rfl fun k _ => T_C_mul _ _
    calc ∑ j, T (C (U i j) * X (Sum.inl j) * R U u)
        = ∑ j, ∑ k, U i j * ((starRingEnd ℂ) (U k j) * T (R U ((pderiv (Sum.inr k)) u))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [step1 j, step2 j, Finset.mul_sum]
      _ = ∑ k, ∑ j, U i j * ((starRingEnd ℂ) (U k j) * T (R U ((pderiv (Sum.inr k)) u))) :=
          Finset.sum_comm
      _ = ∑ k, (∑ j, U i j * (starRingEnd ℂ) (U k j)) * T (R U ((pderiv (Sum.inr k)) u)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, (if i = k then (1 : ℂ) else 0) * T (R U ((pderiv (Sum.inr k)) u)) := by
          exact Finset.sum_congr rfl fun k _ => by rw [unitary_row_sum hU i k]
      _ = T (R U ((pderiv (Sum.inr i)) u)) := by simp
  · intro i u
    change T (R U (X (Sum.inr i) * u)) = T (R U ((pderiv (Sum.inl i)) u))
    rw [map_mul, R_X_inr, Finset.sum_mul, T_sum]
    have step1 : ∀ j : Fin d, T (C ((starRingEnd ℂ) (U i j)) * X (Sum.inr j) * R U u)
        = (starRingEnd ℂ) (U i j) * T ((pderiv (Sum.inl j)) (R U u)) := by
      intro j
      rw [mul_assoc, T_C_mul, T_X_inr_mul]
    have step2 : ∀ j : Fin d, T ((pderiv (Sum.inl j)) (R U u))
        = ∑ k, U k j * T (R U ((pderiv (Sum.inl k)) u)) := by
      intro j
      rw [pderiv_inl_R, T_sum]
      exact Finset.sum_congr rfl fun k _ => T_C_mul _ _
    calc ∑ j, T (C ((starRingEnd ℂ) (U i j)) * X (Sum.inr j) * R U u)
        = ∑ j, ∑ k, (starRingEnd ℂ) (U i j) * (U k j * T (R U ((pderiv (Sum.inl k)) u))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [step1 j, step2 j, Finset.mul_sum]
      _ = ∑ k, ∑ j, (starRingEnd ℂ) (U i j) * (U k j * T (R U ((pderiv (Sum.inl k)) u))) :=
          Finset.sum_comm
      _ = ∑ k, (∑ j, (starRingEnd ℂ) (U i j) * U k j) * T (R U ((pderiv (Sum.inl k)) u)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, (if i = k then (1 : ℂ) else 0) * T (R U ((pderiv (Sum.inl k)) u)) := by
          exact Finset.sum_congr rfl fun k _ => by rw [unitary_row_sum' hU i k]
      _ = T (R U ((pderiv (Sum.inl i)) u)) := by simp

/-- **The Fock form is `U(d)`-invariant.** -/
theorem form_R {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (p q : P d) : form (R U p) (R U q) = form p q := by
  rw [form, form, sig_R, ← map_mul, T_R hU]


end

end PolyFock.Fock
