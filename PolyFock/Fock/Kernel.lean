/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Fock.Layer

/-!
# Rotation invariance of the layer kernels

Each layer `W k l = span {Ψ̂_{𝐧,𝐪} : ‖𝐧‖₁ = k, ‖𝐪‖₁ = l}` is finite dimensional with the
orthonormal basis `Ψ̂`, and is preserved by `R U` for unitary `U`.  The matrix of `R U` in
that basis is therefore unitary, whence the *layer kernel*

`∑_{‖𝐧‖₁ = k, ‖𝐪‖₁ = l} Φ_{𝐧,𝐪}(z) conj (Φ_{𝐧,𝐪}(w))`

is `U(d)`-invariant.  This is the finite-dimensional replacement for "uniqueness of the
reproducing kernel".
-/

namespace PolyFock.Fock

open Finset MvPolynomial Matrix
open DiscretePR (Φ)
open scoped DiscretePR

noncomputable section

variable {d : ℕ}

/-! ### Sesquilinearity over finite sums -/

lemma form_sum_left {ι : Type*} (s : Finset ι) (f : ι → P d) (q : P d) :
    form (∑ i ∈ s, f i) q = ∑ i ∈ s, form (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, form_add_left, ih, Finset.sum_insert ha]

lemma form_sum_right {ι : Type*} (s : Finset ι) (p : P d) (g : ι → P d) :
    form p (∑ i ∈ s, g i) = ∑ i ∈ s, form p (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, form_add_right, ih, Finset.sum_insert ha]

/-! ### The layer index set -/

/-- The finite index set of a layer. -/
def LayerIdx (d k l : ℕ) : Finset ((Fin d → ℕ) × (Fin d → ℕ)) :=
  (Finset.Nat.antidiagonalTuple d k) ×ˢ (Finset.Nat.antidiagonalTuple d l)

lemma mem_LayerIdx {k l : ℕ} {x : (Fin d → ℕ) × (Fin d → ℕ)} :
    x ∈ LayerIdx d k l ↔ ‖x.1‖₁ = k ∧ ‖x.2‖₁ = l := by
  simp only [DiscretePR.size]
  rw [LayerIdx, Finset.mem_product, Finset.Nat.mem_antidiagonalTuple,
    Finset.Nat.mem_antidiagonalTuple]

lemma Psi_eq_C_nrm_mul_Psihat (n q : Fin d → ℕ) :
    Psi n q = C (((nrm n q : ℝ) : ℂ)) * Psihat n q := by
  rw [Psihat, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (nrm_ne_zero n q), map_one, one_mul]

/-! ### Expansion in the orthonormal basis of a layer -/

theorem expand_of_mem_W {k l : ℕ} {p : P d} (hp : p ∈ W k l) :
    p = ∑ x ∈ LayerIdx d k l, C (form p (Psihat x.1 x.2)) * Psihat x.1 x.2 := by
  classical
  induction hp using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨n, q, hn, hq, rfl⟩ := hy
      have hmem : ((n, q) : (Fin d → ℕ) × (Fin d → ℕ)) ∈ LayerIdx d k l :=
        mem_LayerIdx.mpr ⟨hn, hq⟩
      have hform0 : ∀ x : (Fin d → ℕ) × (Fin d → ℕ),
          form (Psi n q) (Psihat x.1 x.2)
            = if x = (n, q) then ((nrm n q : ℝ) : ℂ) else 0 := by
        intro x
        rw [Psi_eq_C_nrm_mul_Psihat n q,
          show C (((nrm n q : ℝ) : ℂ)) * Psihat n q = ((nrm n q : ℝ) : ℂ) • Psihat n q from
            (MvPolynomial.smul_eq_C_mul _ _).symm, form_smul_left, form_Psihat]
        by_cases hx : x = (n, q)
        · subst hx; rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, mul_one]
        · rw [if_neg hx, if_neg (fun hc => hx (Prod.ext_iff.mpr ⟨hc.1.symm, hc.2.symm⟩)),
            mul_zero]
      have hval : ∀ x ∈ LayerIdx d k l,
          C (form (Psi n q) (Psihat x.1 x.2)) * Psihat x.1 x.2
            = if x = (n, q) then C (((nrm n q : ℝ) : ℂ)) * Psihat n q else 0 := by
        intro x _
        rw [hform0 x]
        by_cases hx : x = (n, q)
        · subst hx; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hx, if_neg hx, map_zero, zero_mul]
      rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq' (LayerIdx d k l) ((n, q))
        (fun _ => C (((nrm n q : ℝ) : ℂ)) * Psihat n q), if_pos hmem,
        ← Psi_eq_C_nrm_mul_Psihat]
  | zero => simp
  | add u v _ _ ihu ihv =>
      have hsplit : (∑ x ∈ LayerIdx d k l, C (form (u + v) (Psihat x.1 x.2)) * Psihat x.1 x.2)
          = (∑ x ∈ LayerIdx d k l, C (form u (Psihat x.1 x.2)) * Psihat x.1 x.2)
            + (∑ x ∈ LayerIdx d k l, C (form v (Psihat x.1 x.2)) * Psihat x.1 x.2) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by rw [form_add_left, map_add, add_mul]
      rw [hsplit, ← ihu, ← ihv]
  | smul a u _ ihu =>
      have hsplit : (∑ x ∈ LayerIdx d k l, C (form (a • u) (Psihat x.1 x.2)) * Psihat x.1 x.2)
          = a • ∑ x ∈ LayerIdx d k l, C (form u (Psihat x.1 x.2)) * Psihat x.1 x.2 := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [form_smul_left, map_mul, mul_assoc, MvPolynomial.smul_eq_C_mul]
      rw [hsplit, ← ihu]

/-! ### The matrix of a rotation on a layer -/

/-- The matrix of `R U` in the orthonormal basis of the layer `W k l`. -/
def Amat (U : Matrix (Fin d) (Fin d) ℂ) (k l : ℕ) :
    Matrix (LayerIdx d k l) (LayerIdx d k l) ℂ :=
  fun x y => form (R U (Psihat x.1.1 x.1.2)) (Psihat y.1.1 y.1.2)

lemma R_Psihat_mem_W {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {k l : ℕ} {x : (Fin d → ℕ) × (Fin d → ℕ)} (hx : x ∈ LayerIdx d k l) :
    R U (Psihat x.1 x.2) ∈ W k l := by
  rw [mem_LayerIdx] at hx
  rw [Psihat, ← MvPolynomial.smul_eq_C_mul, map_smul]
  refine Submodule.smul_mem _ _ ?_
  have h := R_Psi_mem_W hU (‖x.1‖₁ + ‖x.2‖₁) x.1 x.2 le_rfl
  rw [hx.1, hx.2] at h
  exact h

lemma R_Psihat_expand {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {k l : ℕ} (x : LayerIdx d k l) :
    R U (Psihat x.1.1 x.1.2)
      = ∑ y : LayerIdx d k l, C (Amat U k l x y) * Psihat y.1.1 y.1.2 := by
  classical
  have h := expand_of_mem_W (R_Psihat_mem_W hU x.2)
  rw [← Finset.sum_coe_sort (LayerIdx d k l)
    (fun x_1 => C (form (R U (Psihat x.1.1 x.1.2)) (Psihat x_1.1 x_1.2)) * Psihat x_1.1 x_1.2)] at h
  exact h

/-- The matrix of a rotation on a layer is unitary. -/
theorem Amat_mul_conjTranspose {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (k l : ℕ) :
    (Amat U k l) * (Amat U k l)ᴴ = 1 := by
  classical
  ext x x'
  have hform : form (R U (Psihat x.1.1 x.1.2)) (R U (Psihat x'.1.1 x'.1.2))
      = ∑ y : LayerIdx d k l, Amat U k l x y * (starRingEnd ℂ) (Amat U k l x' y) := by
    rw [R_Psihat_expand hU x, R_Psihat_expand hU x', form_sum_left]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [form_sum_right]
    have hterm : ∀ y' : LayerIdx d k l,
        form (C (Amat U k l x y) * Psihat y.1.1 y.1.2)
             (C (Amat U k l x' y') * Psihat y'.1.1 y'.1.2)
          = if y' = y then Amat U k l x y * (starRingEnd ℂ) (Amat U k l x' y) else 0 := by
      intro y'
      rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul, form_smul_left,
        form_smul_right, form_Psihat]
      by_cases hy : y' = y
      · subst hy; rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]; ring
      · rw [if_neg hy,
          if_neg (fun hc => hy (Subtype.ext (Prod.ext_iff.mpr ⟨hc.1, hc.2⟩)).symm)]
        ring
    rw [Finset.sum_congr rfl fun y' _ => hterm y', Finset.sum_ite_eq' Finset.univ y
      (fun _ => Amat U k l x y * (starRingEnd ℂ) (Amat U k l x' y))]
    simp
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h2 : ∑ y : LayerIdx d k l, Amat U k l x y * (Amat U k l)ᴴ y x'
      = ∑ y : LayerIdx d k l, Amat U k l x y * (starRingEnd ℂ) (Amat U k l x' y) :=
    Finset.sum_congr rfl fun y _ => by rw [Matrix.conjTranspose_apply, RCLike.star_def]
  rw [h2, ← hform, form_R hU, form_Psihat]
  by_cases hx : x = x'
  · subst hx; simp
  · rw [if_neg hx, if_neg (fun hc => hx (Subtype.ext (Prod.ext_iff.mpr ⟨hc.1, hc.2⟩)))]

/-- The columns of `Amat` are orthonormal. -/
theorem Amat_col {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (k l : ℕ) (y y' : LayerIdx d k l) :
    ∑ x : LayerIdx d k l, Amat U k l x y * (starRingEnd ℂ) (Amat U k l x y')
      = if y = y' then 1 else 0 := by
  classical
  have h : (Amat U k l)ᴴ * (Amat U k l) = 1 :=
    mul_eq_one_comm.mp (Amat_mul_conjTranspose hU k l)
  have h2 := congrFun (congrFun h y) y'
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  have h3 : ∑ x : LayerIdx d k l, (starRingEnd ℂ) (Amat U k l x y) * Amat U k l x y'
      = if y = y' then 1 else 0 := by
    rw [← h2]
    exact Finset.sum_congr rfl fun x _ => by rw [Matrix.conjTranspose_apply, RCLike.star_def]
  have h5 : (starRingEnd ℂ) (if y = y' then (1 : ℂ) else 0) = if y = y' then (1 : ℂ) else 0 := by
    split <;> simp
  calc ∑ x : LayerIdx d k l, Amat U k l x y * (starRingEnd ℂ) (Amat U k l x y')
      = (starRingEnd ℂ) (∑ x : LayerIdx d k l,
          (starRingEnd ℂ) (Amat U k l x y) * Amat U k l x y') := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun x _ => by rw [map_mul, Complex.conj_conj, mul_comm]
    _ = (starRingEnd ℂ) (if y = y' then (1 : ℂ) else 0) := by rw [h3]
    _ = if y = y' then (1 : ℂ) else 0 := h5

/-! ### Rotation invariance of the layer kernel -/

lemma Phi_rot {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {k l : ℕ} (x : LayerIdx d k l) (z : Fin d → ℂ) :
    Φ x.1.1 x.1.2 (U *ᵥ z) = ∑ y : LayerIdx d k l, Amat U k l x y * Φ y.1.1 y.1.2 z := by
  classical
  rw [← ev_Psihat (U *ᵥ z), ← ev_R U z, R_Psihat_expand hU x, map_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [map_mul, ev_C, ev_Psihat]

/-- **Rotation invariance of the layer kernel.** -/
theorem layer_kernel_rot {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (k l : ℕ) (z w : Fin d → ℂ) :
    ∑ x ∈ LayerIdx d k l, Φ x.1 x.2 (U *ᵥ z) * (starRingEnd ℂ) (Φ x.1 x.2 (U *ᵥ w))
      = ∑ x ∈ LayerIdx d k l, Φ x.1 x.2 z * (starRingEnd ℂ) (Φ x.1 x.2 w) := by
  classical
  rw [← Finset.sum_coe_sort (LayerIdx d k l)
      (fun x => Φ x.1 x.2 (U *ᵥ z) * (starRingEnd ℂ) (Φ x.1 x.2 (U *ᵥ w))),
    ← Finset.sum_coe_sort (LayerIdx d k l)
      (fun x => Φ x.1 x.2 z * (starRingEnd ℂ) (Φ x.1 x.2 w))]
  have key : ∀ x : LayerIdx d k l,
      Φ x.1.1 x.1.2 (U *ᵥ z) * (starRingEnd ℂ) (Φ x.1.1 x.1.2 (U *ᵥ w))
        = ∑ y : LayerIdx d k l, ∑ y' : LayerIdx d k l,
            (Amat U k l x y * (starRingEnd ℂ) (Amat U k l x y')) *
              (Φ y.1.1 y.1.2 z * (starRingEnd ℂ) (Φ y'.1.1 y'.1.2 w)) := by
    intro x
    rw [Phi_rot hU x z, Phi_rot hU x w, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
    rw [map_mul]
    ring
  calc ∑ x : LayerIdx d k l, Φ x.1.1 x.1.2 (U *ᵥ z) * (starRingEnd ℂ) (Φ x.1.1 x.1.2 (U *ᵥ w))
      = ∑ x : LayerIdx d k l, ∑ y : LayerIdx d k l, ∑ y' : LayerIdx d k l,
          (Amat U k l x y * (starRingEnd ℂ) (Amat U k l x y')) *
            (Φ y.1.1 y.1.2 z * (starRingEnd ℂ) (Φ y'.1.1 y'.1.2 w)) :=
        Finset.sum_congr rfl fun x _ => key x
    _ = ∑ y : LayerIdx d k l, ∑ y' : LayerIdx d k l, ∑ x : LayerIdx d k l,
          (Amat U k l x y * (starRingEnd ℂ) (Amat U k l x y')) *
            (Φ y.1.1 y.1.2 z * (starRingEnd ℂ) (Φ y'.1.1 y'.1.2 w)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y : LayerIdx d k l, ∑ y' : LayerIdx d k l,
          (if y = y' then (1 : ℂ) else 0) *
            (Φ y.1.1 y.1.2 z * (starRingEnd ℂ) (Φ y'.1.1 y'.1.2 w)) := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
        rw [← Finset.sum_mul, Amat_col hU k l y y']
    _ = ∑ y : LayerIdx d k l, Φ y.1.1 y.1.2 z * (starRingEnd ℂ) (Φ y.1.1 y.1.2 w) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have hcv : ∀ y' : LayerIdx d k l,
            (if y = y' then (1 : ℂ) else 0) *
                (Φ y.1.1 y.1.2 z * (starRingEnd ℂ) (Φ y'.1.1 y'.1.2 w))
              = if y = y' then
                  Φ y.1.1 y.1.2 z * (starRingEnd ℂ) (Φ y'.1.1 y'.1.2 w) else 0 := by
          intro y'; split <;> simp
        rw [Finset.sum_congr rfl fun y' _ => hcv y', Finset.sum_ite_eq Finset.univ y
          (fun y' => Φ y.1.1 y.1.2 z * (starRingEnd ℂ) (Φ y'.1.1 y'.1.2 w))]
        simp

/-- **Rotation invariance of the diagonal of the layer kernel**, in real form. -/
theorem layer_diag_rot {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (k l : ℕ) (z : Fin d → ℂ) :
    ∑ x ∈ LayerIdx d k l, ‖Φ x.1 x.2 (U *ᵥ z)‖ ^ 2
      = ∑ x ∈ LayerIdx d k l, ‖Φ x.1 x.2 z‖ ^ 2 := by
  have h := layer_kernel_rot hU k l z z
  have hL : ∀ (v : Fin d → ℂ),
      ∑ x ∈ LayerIdx d k l, Φ x.1 x.2 v * (starRingEnd ℂ) (Φ x.1 x.2 v)
        = ((∑ x ∈ LayerIdx d k l, ‖Φ x.1 x.2 v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Complex.mul_conj']; push_cast; ring
  rw [hL, hL] at h
  exact_mod_cast h

end

end PolyFock.Fock
