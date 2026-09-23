/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Fock.Rot

/-!
# The normalised basis, and the bridge to the basis `Φ`

`Psihat n q` is `Ψ_{𝐧,𝐪}` divided by `∏ᵢ √(nᵢ! qᵢ!)`.  It is orthonormal for the Fock form,
and evaluating it at `z ∈ ℂ^d` gives exactly `DiscretePR.Φ n q z`, the comparator's basis
element of `Definitions.lean`.
-/

namespace PolyFock.Fock

open Finset MvPolynomial
open DiscretePR (HermitePoly Φ)

noncomputable section

variable {d : ℕ}

/-- The normalising factor `∏ᵢ √(nᵢ! qᵢ!)`. -/
def nrm (n q : Fin d → ℕ) : ℝ := ∏ i, Real.sqrt ((n i).factorial * (q i).factorial)

lemma nrm_pos (n q : Fin d → ℕ) : 0 < nrm n q := by
  refine Finset.prod_pos fun i _ => Real.sqrt_pos.mpr ?_
  have h1 : (0 : ℝ) < (n i).factorial := by exact_mod_cast (n i).factorial_pos
  have h2 : (0 : ℝ) < (q i).factorial := by exact_mod_cast (q i).factorial_pos
  positivity

lemma nrm_ne_zero (n q : Fin d → ℕ) : (nrm n q : ℂ) ≠ 0 := by
  exact_mod_cast (nrm_pos n q).ne'

lemma nrm_sq (n q : Fin d → ℕ) :
    ((nrm n q : ℂ)) ^ 2 = ∏ i, ((n i).factorial : ℂ) * ((q i).factorial : ℂ) := by
  have h : (nrm n q) ^ 2 = ∏ i, ((n i).factorial : ℝ) * ((q i).factorial : ℝ) := by
    rw [nrm, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : (0 : ℝ) ≤ ((n i).factorial : ℝ) * ((q i).factorial : ℝ) := by positivity
    rw [Real.sq_sqrt this]
  calc ((nrm n q : ℂ)) ^ 2 = (((nrm n q) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = ((∏ i, ((n i).factorial : ℝ) * ((q i).factorial : ℝ) : ℝ) : ℂ) := by rw [h]
    _ = ∏ i, ((n i).factorial : ℂ) * ((q i).factorial : ℂ) := by push_cast; ring

/-! ### Evaluation -/

@[simp] lemma ev_C (z : Fin d → ℂ) (c : ℂ) : ev z (C c) = c := by simp [ev]

lemma ev_Hpoly (z : Fin d → ℂ) (i : Fin d) (m n : ℕ) :
    ev z (Hpoly i m n)
      = ((Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)) : ℝ) : ℂ) * HermitePoly m n (z i) := by
  classical
  have hne : ((Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have h1 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
    have h2 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have : (0 : ℝ) < Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)) :=
      Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  rw [HermitePoly, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, Hpoly, map_sum]
  simp only [RCLike.star_def]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, ev_X_inl, ev_X_inr, ev_C, cc]

lemma ev_Psi (z : Fin d → ℂ) (n q : Fin d → ℕ) :
    ev z (Psi n q) = ((nrm n q : ℝ) : ℂ) * Φ n q z := by
  classical
  rw [Psi, map_prod, Φ, nrm]
  push_cast
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => ev_Hpoly z i (n i) (q i)

/-! ### The normalised basis -/

/-- The normalised tensorised Hermite polynomial: `Ψ̂_{𝐧,𝐪} = Ψ_{𝐧,𝐪} / ∏ᵢ √(nᵢ! qᵢ!)`. -/
def Psihat (n q : Fin d → ℕ) : P d := C (((nrm n q : ℝ) : ℂ))⁻¹ * Psi n q

lemma ev_Psihat (z : Fin d → ℂ) (n q : Fin d → ℕ) : ev z (Psihat n q) = Φ n q z := by
  rw [Psihat, map_mul, ev_Psi, ev_C, ← mul_assoc, inv_mul_cancel₀ (nrm_ne_zero n q), one_mul]

/-- **The normalised basis is orthonormal for the Fock form.** -/
theorem form_Psihat (n q n' q' : Fin d → ℕ) :
    form (Psihat n q) (Psihat n' q') = if n = n' ∧ q = q' then 1 else 0 := by
  classical
  rw [Psihat, Psihat, ← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul,
    form_smul_left, form_smul_right, form_Psi]
  have hconj : (starRingEnd ℂ) (((nrm n' q' : ℝ) : ℂ))⁻¹ = (((nrm n' q' : ℝ) : ℂ))⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  rw [hconj]
  by_cases h : n = n' ∧ q = q'
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, ← nrm_sq n q]
    have h0 : ((nrm n q : ℝ) : ℂ) ≠ 0 := nrm_ne_zero n q
    field_simp
  · rw [if_neg h, if_neg h]
    ring

end

end PolyFock.Fock
