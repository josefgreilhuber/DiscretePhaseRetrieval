/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Fock.Hermite

/-!
# Orthogonality of the tensorised complex Hermite polynomials

`Psi n q = ∏ᵢ H_{nᵢ,qᵢ}(zᵢ, z̄ᵢ)` is the unnormalised version of the comparator's
`DiscretePR.Φ`.  The main result is

`PolyFock.Fock.form_Psi : ⟪Ψ_{𝐧,𝐪}, Ψ_{𝐧',𝐪'}⟫ = δ · ∏ᵢ nᵢ! qᵢ!`,

proved from the adjointness `⟪Aᵢ p, r⟫ = ⟪p, ∂_{zᵢ} r⟫` and the commutation relations, by
induction on `‖𝐧‖₁ + ‖𝐪‖₁`.
-/

namespace PolyFock.Fock

open Finset MvPolynomial
open scoped DiscretePR

noncomputable section

variable {d : ℕ}

/-! ### Derivatives of products -/

lemma pderiv_prod_eq_zero (v : Idx d) (s : Finset (Fin d)) (f : Fin d → P d)
    (h : ∀ j ∈ s, (pderiv v) (f j) = 0) : (pderiv v) (∏ j ∈ s, f j) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, pderiv_mul, h a (Finset.mem_insert_self a s),
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]
      simp

lemma pderiv_prod_single (v : Idx d) (i : Fin d) (f : Fin d → P d)
    (h : ∀ j, j ≠ i → (pderiv v) (f j) = 0) :
    (pderiv v) (∏ j, f j) = (pderiv v) (f i) * ∏ j ∈ Finset.univ.erase i, f j := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), pderiv_mul,
    pderiv_prod_eq_zero v _ f (fun j hj => h j (Finset.ne_of_mem_erase hj))]
  ring

/-! ### The tensorised Hermite polynomials -/

/-- `Ψ_{𝐧,𝐪} = ∏ᵢ H_{nᵢ,qᵢ}(zᵢ, z̄ᵢ)`. -/
def Psi (n q : Fin d → ℕ) : P d := ∏ i, Hpoly i (n i) (q i)

@[simp] lemma Psi_zero : Psi (0 : Fin d → ℕ) 0 = 1 := by simp [Psi]

lemma Psi_eq_mul_erase (n q : Fin d → ℕ) (i : Fin d) :
    Psi n q = Hpoly i (n i) (q i) * ∏ j ∈ Finset.univ.erase i, Hpoly j (n j) (q j) := by
  classical
  rw [Psi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

lemma prod_erase_update (n q : Fin d → ℕ) (i : Fin d) (k : ℕ) :
    ∏ j ∈ Finset.univ.erase i, Hpoly j ((Function.update n i k) j) (q j)
      = ∏ j ∈ Finset.univ.erase i, Hpoly j (n j) (q j) := by
  classical
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma prod_erase_update_right (n q : Fin d → ℕ) (i : Fin d) (k : ℕ) :
    ∏ j ∈ Finset.univ.erase i, Hpoly j (n j) ((Function.update q i k) j)
      = ∏ j ∈ Finset.univ.erase i, Hpoly j (n j) (q j) := by
  classical
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- `∂_{zᵢ} Ψ_{𝐧,𝐪} = nᵢ Ψ_{𝐧-eᵢ,𝐪}`. -/
lemma pderiv_inl_Psi (n q : Fin d → ℕ) (i : Fin d) :
    (pderiv (Sum.inl i)) (Psi n q) = (n i : ℂ) • Psi (Function.update n i (n i - 1)) q := by
  classical
  rw [Psi, pderiv_prod_single _ i _ (fun j hj => pderiv_inl_Hpoly_of_ne j i (Ne.symm hj) _ _),
    pderiv_inl_Hpoly, Psi_eq_mul_erase _ _ i, Function.update_self, prod_erase_update]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

/-- `∂_{z̄ᵢ} Ψ_{𝐧,𝐪} = qᵢ Ψ_{𝐧,𝐪-eᵢ}`. -/
lemma pderiv_inr_Psi (n q : Fin d → ℕ) (i : Fin d) :
    (pderiv (Sum.inr i)) (Psi n q) = (q i : ℂ) • Psi n (Function.update q i (q i - 1)) := by
  classical
  rw [Psi, pderiv_prod_single _ i _ (fun j hj => pderiv_inr_Hpoly_of_ne j i (Ne.symm hj) _ _),
    pderiv_inr_Hpoly, Psi_eq_mul_erase _ _ i, Function.update_self, prod_erase_update_right]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

/-- `Aᵢ Ψ_{𝐧,𝐪} = Ψ_{𝐧+eᵢ,𝐪}`. -/
lemma A_Psi (n q : Fin d → ℕ) (i : Fin d) :
    A i (Psi n q) = Psi (Function.update n i (n i + 1)) q := by
  classical
  have hR : Psi (Function.update n i (n i + 1)) q
      = Hpoly i (n i + 1) (q i) * ∏ j ∈ Finset.univ.erase i, Hpoly j (n j) (q j) := by
    rw [Psi_eq_mul_erase _ _ i, Function.update_self, prod_erase_update]
  rw [hR, Hpoly_succ_left]
  simp only [A]
  rw [pderiv_inr_Psi, Psi_eq_mul_erase n q i,
    Psi_eq_mul_erase n (Function.update q i (q i - 1)) i, Function.update_self,
    prod_erase_update_right, pderiv_inr_Hpoly]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

/-- `Bᵢ Ψ_{𝐧,𝐪} = Ψ_{𝐧,𝐪+eᵢ}`. -/
lemma B_Psi (n q : Fin d → ℕ) (i : Fin d) :
    B i (Psi n q) = Psi n (Function.update q i (q i + 1)) := by
  classical
  have hR : Psi n (Function.update q i (q i + 1))
      = Hpoly i (n i) (q i + 1) * ∏ j ∈ Finset.univ.erase i, Hpoly j (n j) (q j) := by
    rw [Psi_eq_mul_erase _ _ i, Function.update_self, prod_erase_update_right]
  rw [hR, Hpoly_succ_right]
  simp only [B]
  rw [pderiv_inl_Psi, Psi_eq_mul_erase n q i,
    Psi_eq_mul_erase (Function.update n i (n i - 1)) q i, Function.update_self,
    prod_erase_update, pderiv_inl_Hpoly]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

/-! ### Orthogonality -/

/-- `⟪Ψ_{𝐧,𝐪}, 1⟫ = 0` unless `𝐧 = 𝐪 = 0`. -/
lemma form_Psi_one (n q : Fin d → ℕ) :
    form (Psi n q) 1 = if n = 0 ∧ q = 0 then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · by_cases hq : q = 0
    · subst hn; subst hq; simp
    · rw [if_neg (by tauto)]
      obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
        by_contra hc
        exact hq (funext fun j => by simpa using not_exists.mp hc j)
      have hupd : Function.update (Function.update q i (q i - 1)) i
          ((Function.update q i (q i - 1)) i + 1) = q := by
        funext j
        by_cases hj : j = i
        · subst hj; simp; omega
        · simp [Function.update_of_ne hj]
      rw [← hupd, ← B_Psi, form_B]
      simp
  · rw [if_neg (by tauto)]
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hc
      exact hn (funext fun j => by simpa using not_exists.mp hc j)
    have hupd : Function.update (Function.update n i (n i - 1)) i
        ((Function.update n i (n i - 1)) i + 1) = n := by
      funext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]
    rw [← hupd, ← A_Psi, form_A]
    simp

/-- `⟪1, Ψ_{𝐧,𝐪}⟫ = 0` unless `𝐧 = 𝐪 = 0`. -/
lemma form_one_Psi (n q : Fin d → ℕ) :
    form 1 (Psi n q) = if n = 0 ∧ q = 0 then 1 else 0 := by
  rw [form_conj_symm, form_Psi_one]
  split <;> simp

/-! ### Multi-index bookkeeping -/

lemma update_pred_succ {n : Fin d → ℕ} {i : Fin d} (hi : n i ≠ 0) :
    Function.update (Function.update n i (n i - 1)) i
      ((Function.update n i (n i - 1)) i + 1) = n := by
  classical
  funext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [Function.update_of_ne hj]

lemma sum_update_pred {n : Fin d → ℕ} {i : Fin d} (hi : n i ≠ 0) :
    (∑ j, (Function.update n i (n i - 1)) j) + 1 = ∑ j, n j := by
  classical
  have h1 : ∑ j, (Function.update n i (n i - 1)) j
      = (n i - 1) + ∑ j ∈ Finset.univ.erase i, n j := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have h2 : ∑ j, n j = n i + ∑ j ∈ Finset.univ.erase i, n j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  omega

lemma update_pred_inj {n n' : Fin d → ℕ} {i : Fin d} (hi : n i ≠ 0) (hi' : n' i ≠ 0)
    (h : Function.update n i (n i - 1) = Function.update n' i (n' i - 1)) : n = n' := by
  classical
  funext j
  by_cases hj : j = i
  · subst hj
    have h2 := congrFun h j
    simp at h2
    omega
  · have h2 := congrFun h j
    simpa [Function.update_of_ne hj] using h2

lemma prod_factorial_update {n q : Fin d → ℕ} {i : Fin d} (hi : n i ≠ 0) :
    (n i : ℂ) * ∏ j, (((Function.update n i (n i - 1)) j).factorial : ℂ) * ((q j).factorial : ℂ)
      = ∏ j, ((n j).factorial : ℂ) * ((q j).factorial : ℂ) := by
  classical
  have hfac : (n i : ℂ) * (((n i - 1).factorial : ℕ) : ℂ) = (((n i).factorial : ℕ) : ℂ) := by
    obtain ⟨k, hk⟩ : ∃ k, n i = k + 1 := ⟨n i - 1, by omega⟩
    rw [hk]
    simp [Nat.factorial_succ]
  have hsplitL : ∏ j, (((Function.update n i (n i - 1)) j).factorial : ℂ) * ((q j).factorial : ℂ)
      = (((n i - 1).factorial : ℂ) * ((q i).factorial : ℂ)) *
        ∏ j ∈ Finset.univ.erase i, ((n j).factorial : ℂ) * ((q j).factorial : ℂ) := by
    have hprod : ∏ j ∈ Finset.univ.erase i,
        (((Function.update n i (n i - 1)) j).factorial : ℂ) * ((q j).factorial : ℂ)
        = ∏ j ∈ Finset.univ.erase i, ((n j).factorial : ℂ) * ((q j).factorial : ℂ) :=
      Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, hprod]
  have hsplitR : ∏ j, ((n j).factorial : ℂ) * ((q j).factorial : ℂ)
      = (((n i).factorial : ℂ) * ((q i).factorial : ℂ)) *
        ∏ j ∈ Finset.univ.erase i, ((n j).factorial : ℂ) * ((q j).factorial : ℂ) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [hsplitL, hsplitR, ← hfac]
  ring

lemma prod_factorial_update_right {n q : Fin d → ℕ} {i : Fin d} (hi : q i ≠ 0) :
    (q i : ℂ) * ∏ j, ((n j).factorial : ℂ) * (((Function.update q i (q i - 1)) j).factorial : ℂ)
      = ∏ j, ((n j).factorial : ℂ) * ((q j).factorial : ℂ) := by
  classical
  have hfac : (q i : ℂ) * (((q i - 1).factorial : ℕ) : ℂ) = (((q i).factorial : ℕ) : ℂ) := by
    obtain ⟨k, hk⟩ : ∃ k, q i = k + 1 := ⟨q i - 1, by omega⟩
    rw [hk]
    simp [Nat.factorial_succ]
  have hsplitL : ∏ j, ((n j).factorial : ℂ) * (((Function.update q i (q i - 1)) j).factorial : ℂ)
      = (((n i).factorial : ℂ) * ((q i - 1).factorial : ℂ)) *
        ∏ j ∈ Finset.univ.erase i, ((n j).factorial : ℂ) * ((q j).factorial : ℂ) := by
    have hprod : ∏ j ∈ Finset.univ.erase i,
        ((n j).factorial : ℂ) * (((Function.update q i (q i - 1)) j).factorial : ℂ)
        = ∏ j ∈ Finset.univ.erase i, ((n j).factorial : ℂ) * ((q j).factorial : ℂ) :=
      Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, hprod]
  have hsplitR : ∏ j, ((n j).factorial : ℂ) * ((q j).factorial : ℂ)
      = (((n i).factorial : ℂ) * ((q i).factorial : ℂ)) *
        ∏ j ∈ Finset.univ.erase i, ((n j).factorial : ℂ) * ((q j).factorial : ℂ) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [hsplitL, hsplitR, ← hfac]
  ring

/-! ### The orthogonality theorem -/

private lemma form_Psi_aux : ∀ (N : ℕ) (n q n' q' : Fin d → ℕ),
    ‖n‖₁ + ‖q‖₁ ≤ N →
    form (Psi n q) (Psi n' q') =
      if n = n' ∧ q = q' then ∏ i, ((n i).factorial : ℂ) * ((q i).factorial : ℂ) else 0 := by
  classical
  simp only [DiscretePR.size]
  intro N
  induction N with
  | zero =>
      intro n q n' q' h
      have hn : n = 0 := by
        funext j
        have : n j ≤ 0 := le_trans (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)) (by omega)
        simpa using this
      have hq : q = 0 := by
        funext j
        have : q j ≤ 0 := le_trans (Finset.single_le_sum (f := q) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)) (by omega)
        simpa using this
      subst hn; subst hq
      rw [Psi_zero, form_one_Psi]
      simp [eq_comm]
  | succ N ih =>
      intro n q n' q' h
      by_cases hn : ∃ i, n i ≠ 0
      · obtain ⟨i, hi⟩ := hn
        have hPsi : Psi n q = A i (Psi (Function.update n i (n i - 1)) q) := by
          rw [A_Psi _ q i, update_pred_succ hi]
        have hsum : (∑ j, (Function.update n i (n i - 1)) j) + (∑ j, q j) ≤ N := by
          have := sum_update_pred (n := n) (i := i) hi
          omega
        rw [hPsi, form_A, pderiv_inl_Psi, form_smul_right,
          ih _ q (Function.update n' i (n' i - 1)) q' hsum, Complex.conj_natCast]
        by_cases hcase : n = n' ∧ q = q'
        · obtain ⟨rfl, rfl⟩ := hcase
          rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
          exact prod_factorial_update hi
        · rw [if_neg hcase]
          by_cases hq' : q = q'
          · subst hq'
            have hnn : n ≠ n' := fun hh => hcase ⟨hh, rfl⟩
            by_cases hn' : n' i = 0
            · rw [hn']; simp
            · rw [if_neg (fun hc => hnn (update_pred_inj hi hn' hc.1))]
              ring
          · rw [if_neg (fun hc => hq' hc.2)]
            ring
      · have hn0 : n = 0 := by
          funext j
          simpa using not_exists.mp hn j
        by_cases hq : ∃ i, q i ≠ 0
        · obtain ⟨i, hi⟩ := hq
          have hPsi : Psi n q = B i (Psi n (Function.update q i (q i - 1))) := by
            rw [B_Psi n _ i, update_pred_succ hi]
          have hsum : (∑ j, n j) + (∑ j, (Function.update q i (q i - 1)) j) ≤ N := by
            have := sum_update_pred (n := q) (i := i) hi
            omega
          rw [hPsi, form_B, pderiv_inr_Psi, form_smul_right,
            ih n _ n' (Function.update q' i (q' i - 1)) hsum, Complex.conj_natCast]
          by_cases hcase : n = n' ∧ q = q'
          · obtain ⟨rfl, rfl⟩ := hcase
            rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
            exact prod_factorial_update_right hi
          · rw [if_neg hcase]
            by_cases hn' : n = n'
            · subst hn'
              have hqq : q ≠ q' := fun hh => hcase ⟨rfl, hh⟩
              by_cases hq' : q' i = 0
              · rw [hq']; simp
              · rw [if_neg (fun hc => hqq (update_pred_inj hi hq' hc.2))]
                ring
            · rw [if_neg (fun hc => hn' hc.1)]
              ring
        · have hq0 : q = 0 := by
            funext j
            simpa using not_exists.mp hq j
          subst hn0; subst hq0
          rw [Psi_zero, form_one_Psi]
          simp [eq_comm]

/-- **Orthogonality**: `⟪Ψ_{𝐧,𝐪}, Ψ_{𝐧',𝐪'}⟫ = δ · ∏ᵢ nᵢ! qᵢ!`. -/
theorem form_Psi (n q n' q' : Fin d → ℕ) :
    form (Psi n q) (Psi n' q') =
      if n = n' ∧ q = q' then ∏ i, ((n i).factorial : ℂ) * ((q i).factorial : ℂ) else 0 :=
  form_Psi_aux _ n q n' q' le_rfl


end

end PolyFock.Fock
