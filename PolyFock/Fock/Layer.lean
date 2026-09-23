/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Fock.Bridge

/-!
# The layers `span {Ψ_{𝐧,𝐪} : ‖𝐧‖₁ = k, ‖𝐪‖₁ = l}` are `U(d)`-invariant

The key identity is `R U (Aₘ p) = ∑ᵢ Uₘᵢ Aᵢ (R U p)` for unitary `U`: conjugating a creation
operator by a rotation gives a linear combination of creation operators.  Since
`Ψ_{𝐧,𝐪} = A^𝐧 B^𝐪 1` and `R U 1 = 1`, this shows by induction that `R U Ψ_{𝐧,𝐪}` lies in the
span of the `Ψ_{𝐧',𝐪'}` with `‖𝐧'‖₁ = ‖𝐧‖₁` and `‖𝐪'‖₁ = ‖𝐪‖₁`.
-/

namespace PolyFock.Fock

open Finset MvPolynomial
open scoped DiscretePR

noncomputable section

variable {d : ℕ}

/-! ### Linearity of the creation operators -/

lemma A_add (i : Fin d) (p q : P d) : A i (p + q) = A i p + A i q := by
  simp only [A, mul_add, map_add]; ring

lemma A_smul (i : Fin d) (c : ℂ) (p : P d) : A i (c • p) = c • A i p := by
  simp only [A, MvPolynomial.smul_eq_C_mul, pderiv_mul, pderiv_C, zero_mul, zero_add, mul_sub,
    mul_left_comm]

lemma A_zero (i : Fin d) : A i (0 : P d) = 0 := by simp [A]

lemma B_add (i : Fin d) (p q : P d) : B i (p + q) = B i p + B i q := by
  simp only [B, mul_add, map_add]; ring

lemma B_smul (i : Fin d) (c : ℂ) (p : P d) : B i (c • p) = c • B i p := by
  simp only [B, MvPolynomial.smul_eq_C_mul, pderiv_mul, pderiv_C, zero_mul, zero_add, mul_sub,
    mul_left_comm]

lemma B_zero (i : Fin d) : B i (0 : P d) = 0 := by simp [B]

/-! ### Conjugating a creation operator by a rotation -/

lemma R_A {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (m : Fin d) (p : P d) : R U (A m p) = ∑ i, C (U m i) * A i (R U p) := by
  classical
  have h1 : ∑ i, C (U m i) * A i (R U p)
      = (∑ i, C (U m i) * X (Sum.inl i)) * R U p
        - ∑ i, C (U m i) * (pderiv (Sum.inr i)) (R U p) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [A]; ring
  have hstep : ∀ i : Fin d, C (U m i) * (pderiv (Sum.inr i)) (R U p)
      = ∑ k, C (U m i * (starRingEnd ℂ) (U k i)) * R U ((pderiv (Sum.inr k)) p) := by
    intro i
    rw [pderiv_inr_R, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, ← map_mul]
  have h2 : ∑ i, C (U m i) * (pderiv (Sum.inr i)) (R U p) = R U ((pderiv (Sum.inr m)) p) := by
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
    have hcol : ∀ k : Fin d,
        ∑ i, C (U m i * (starRingEnd ℂ) (U k i)) * R U ((pderiv (Sum.inr k)) p)
          = C (if m = k then 1 else 0) * R U ((pderiv (Sum.inr k)) p) := by
      intro k
      rw [← Finset.sum_mul, ← map_sum, unitary_row_sum hU m k]
    rw [Finset.sum_congr rfl fun k _ => hcol k]
    simp
  rw [h1, h2, ← R_X_inl, ← map_mul, A, map_sub]

lemma R_B {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (m : Fin d) (p : P d) :
    R U (B m p) = ∑ i, C ((starRingEnd ℂ) (U m i)) * B i (R U p) := by
  classical
  have h1 : ∑ i, C ((starRingEnd ℂ) (U m i)) * B i (R U p)
      = (∑ i, C ((starRingEnd ℂ) (U m i)) * X (Sum.inr i)) * R U p
        - ∑ i, C ((starRingEnd ℂ) (U m i)) * (pderiv (Sum.inl i)) (R U p) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [B]; ring
  have hstep : ∀ i : Fin d, C ((starRingEnd ℂ) (U m i)) * (pderiv (Sum.inl i)) (R U p)
      = ∑ k, C ((starRingEnd ℂ) (U m i) * U k i) * R U ((pderiv (Sum.inl k)) p) := by
    intro i
    rw [pderiv_inl_R, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, ← map_mul]
  have h2 : ∑ i, C ((starRingEnd ℂ) (U m i)) * (pderiv (Sum.inl i)) (R U p)
      = R U ((pderiv (Sum.inl m)) p) := by
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
    have hcol : ∀ k : Fin d,
        ∑ i, C ((starRingEnd ℂ) (U m i) * U k i) * R U ((pderiv (Sum.inl k)) p)
          = C (if m = k then 1 else 0) * R U ((pderiv (Sum.inl k)) p) := by
      intro k
      rw [← Finset.sum_mul, ← map_sum, unitary_row_sum' hU m k]
    rw [Finset.sum_congr rfl fun k _ => hcol k]
    simp
  rw [h1, h2, ← R_X_inr, ← map_mul, B, map_sub]

/-! ### The layers -/

lemma sum_update_succ (n : Fin d → ℕ) (i : Fin d) :
    (∑ j, (Function.update n i (n i + 1)) j) = (∑ j, n j) + 1 := by
  classical
  have h1 : ∑ j, (Function.update n i (n i + 1)) j
      = (n i + 1) + ∑ j ∈ Finset.univ.erase i, n j := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have h2 : ∑ j, n j = n i + ∑ j ∈ Finset.univ.erase i, n j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  omega

/-- The layer `span {Ψ_{𝐧,𝐪} : ‖𝐧‖₁ = k, ‖𝐪‖₁ = l}`. -/
def W (k l : ℕ) : Submodule ℂ (P d) :=
  Submodule.span ℂ {p : P d | ∃ n q : Fin d → ℕ, ‖n‖₁ = k ∧ ‖q‖₁ = l ∧ p = Psi n q}

lemma Psi_mem_W (n q : Fin d → ℕ) : Psi n q ∈ W ‖n‖₁ ‖q‖₁ :=
  Submodule.subset_span ⟨n, q, rfl, rfl, rfl⟩

lemma Psi_mem_W' {n q : Fin d → ℕ} {k l : ℕ} (hk : ‖n‖₁ = k) (hl : ‖q‖₁ = l) :
    Psi n q ∈ W k l := by
  subst hk; subst hl; exact Psi_mem_W n q

lemma A_mem_W (i : Fin d) {k l : ℕ} {p : P d} (hp : p ∈ W k l) : A i p ∈ W (k + 1) l := by
  classical
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨n, q, hn, hq, rfl⟩ := hx
      rw [A_Psi]
      exact Psi_mem_W' (by simp only [DiscretePR.size] at hn ⊢; rw [sum_update_succ, hn]) hq
  | zero => rw [A_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [A_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx => rw [A_smul]; exact Submodule.smul_mem _ _ ihx

lemma B_mem_W (i : Fin d) {k l : ℕ} {p : P d} (hp : p ∈ W k l) : B i p ∈ W k (l + 1) := by
  classical
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨n, q, hn, hq, rfl⟩ := hx
      rw [B_Psi]
      exact Psi_mem_W' hn (by simp only [DiscretePR.size] at hq ⊢; rw [sum_update_succ, hq])
  | zero => rw [B_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [B_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx => rw [B_smul]; exact Submodule.smul_mem _ _ ihx

/-- **The layers are `U(d)`-invariant.** -/
theorem R_Psi_mem_W {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ (N : ℕ) (n q : Fin d → ℕ), ‖n‖₁ + ‖q‖₁ ≤ N →
      R U (Psi n q) ∈ W ‖n‖₁ ‖q‖₁ := by
  classical
  simp only [DiscretePR.size]
  intro N
  induction N with
  | zero =>
      intro n q h
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
      rw [Psi_zero, map_one]
      simpa [DiscretePR.size] using Psi_mem_W (0 : Fin d → ℕ) 0
  | succ N ih =>
      intro n q h
      by_cases hn : ∃ i, n i ≠ 0
      · obtain ⟨i, hi⟩ := hn
        have hPsi : Psi n q = A i (Psi (Function.update n i (n i - 1)) q) := by
          rw [A_Psi _ q i, update_pred_succ hi]
        have hsum : (∑ j, (Function.update n i (n i - 1)) j) + (∑ j, q j) ≤ N := by
          have := sum_update_pred (n := n) (i := i) hi
          omega
        have hmem := ih (Function.update n i (n i - 1)) q hsum
        rw [hPsi, R_A hU]
        refine Submodule.sum_mem _ fun m _ => ?_
        rw [← MvPolynomial.smul_eq_C_mul]
        refine Submodule.smul_mem _ _ ?_
        have hA := A_mem_W m hmem
        have heq : (∑ j, (Function.update n i (n i - 1)) j) + 1 = ∑ j, n j :=
          sum_update_pred hi
        rw [heq] at hA
        exact hA
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
          have hmem := ih n (Function.update q i (q i - 1)) hsum
          rw [hPsi, R_B hU]
          refine Submodule.sum_mem _ fun m _ => ?_
          rw [← MvPolynomial.smul_eq_C_mul]
          refine Submodule.smul_mem _ _ ?_
          have hB := B_mem_W m hmem
          have heq : (∑ j, (Function.update q i (q i - 1)) j) + 1 = ∑ j, q j :=
            sum_update_pred hi
          rw [heq] at hB
          exact hB
        · have hq0 : q = 0 := by
            funext j
            simpa using not_exists.mp hq j
          subst hn0; subst hq0
          rw [Psi_zero, map_one]
          simpa [DiscretePR.size] using Psi_mem_W (0 : Fin d → ℕ) 0

end

end PolyFock.Fock
