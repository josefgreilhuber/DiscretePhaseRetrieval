/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Basic
import Definitions

/-!
# Rotation invariance of the tail kernel

The true polyanalytic Fock space `𝓕^d_L` is `U(d)`-invariant: it is the orthogonal
complement of `⨁_{ℓ<L} 𝓕^d_ℓ` inside the space of `L²(ℂ^d ; e^{-|·|²})`-functions that are
polyanalytic of order `L`, and both polyanalyticity and the inner product are preserved by a
holomorphic rotation `z ↦ U z`.  The same holds for each layer `span {Φ_{𝐧,𝐪} : ‖𝐪‖₁ = L,
‖𝐧‖₁ = k}`, because a holomorphic rotation preserves the bidegree of a monomial `z^α z̄^β`.
Consequently the reproducing kernels of these spaces — in particular the tail kernel
`K_{L,N}` — are `U(d)`-invariant kernels.

This file provides the geometric half of that reduction:

* `PolyFock.radialPoint x` — the point `(x, 0, …, 0) ∈ ℂ^d`;
* `PolyFock.exists_unitary_radialPoint` — every `z ∈ ℂ^d` is a unitary image of the radial
  point `(|z|, 0, …, 0)`.

The analytic half — that `z ↦ K_{L,N}(z,z)` is invariant under a unitary change of variables
— is proved in `PolyFock/Fock/` (`Fock.layer_diag_rot`); the two are combined in
`PolyFock.tailKernelDiag_le_of_radial_bound` (`PolyFock/RadialReduction.lean`), which
transfers a bound at the radial points to all of `ℂ^d`.  Nothing here is assumed: every
statement of this development is proved from the definitions.

The Euclidean geometry of `ℂ^d` is the comparator's: the radius of `z` is
`DiscretePR.euclideanDist z 0`, and this file records the three elementary facts about it that
the tail-bound proof uses.
-/

namespace DiscretePR

variable {d : ℕ}

/-! ### The Euclidean radius `|z| = euclideanDist z 0` -/

/-- The Euclidean distance to the origin is the Euclidean norm `|z| = (∑ᵢ |zᵢ|²)^{1/2}`. -/
@[simp] theorem euclideanDist_zero (z : Fin d → ℂ) :
    euclideanDist z 0 = Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
  rw [euclideanDist]
  simp

theorem euclideanDist_zero_nonneg (z : Fin d → ℂ) : 0 ≤ euclideanDist z 0 :=
  Real.sqrt_nonneg _

theorem euclideanDist_zero_sq (z : Fin d → ℂ) : euclideanDist z 0 ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  rw [euclideanDist_zero]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)

end DiscretePR

namespace PolyFock

open Finset Matrix
open DiscretePR (euclideanDist euclideanDist_zero euclideanDist_zero_nonneg euclideanDist_zero_sq)

noncomputable section

variable {d : ℕ}

/-! ### The point `(|z|, 0, …, 0)` -/

/-- The point `(x, 0, …, 0) ∈ ℂ^d`. -/
def radialPoint [NeZero d] (x : ℝ) : Fin d → ℂ := Pi.single 0 (x : ℂ)

lemma radialPoint_apply [NeZero d] (x : ℝ) (i : Fin d) :
    radialPoint (d := d) x i = if i = 0 then (x : ℂ) else 0 := by
  simp [radialPoint, Pi.single_apply]

/-! ### Consequences -/

/-- Any point of `ℂ^d` is a unitary image of `(|z|, 0, …, 0)`. -/
lemma exists_unitary_radialPoint [NeZero d] (z : Fin d → ℂ) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ, U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      U *ᵥ radialPoint (euclideanDist z 0) = z := by
  rcases eq_or_ne (euclideanDist z 0) 0 with h0 | h0
  · refine ⟨1, Submonoid.one_mem _, ?_⟩
    have hzero : ∑ i, ‖z i‖ ^ 2 = 0 := by
      have h := euclideanDist_zero_sq z
      rw [h0] at h
      simpa using h.symm
    have hz : z = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity : ∀ i ∈ Finset.univ,
        (0:ℝ) ≤ ‖z i‖ ^ 2)).mp hzero i (Finset.mem_univ i)
      simpa using this
    rw [h0, hz]
    simp [radialPoint]
  · set r := euclideanDist z 0 with hr
    have hrpos : 0 < r := lt_of_le_of_ne (euclideanDist_zero_nonneg z) (Ne.symm h0)
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    set u : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (fun i => (r : ℂ)⁻¹ * z i) with hu
    have huapp : ∀ i, u i = (r : ℂ)⁻¹ * z i := fun _ => rfl
    have hnormu : ‖u‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      have hsum : ∑ i, ‖u i‖ ^ 2 = 1 := by
        have hterm : ∀ i, ‖u i‖ ^ 2 = (r ^ 2)⁻¹ * ‖z i‖ ^ 2 := by
          intro i
          rw [huapp i, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hrpos, inv_pow]
        rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, ← euclideanDist_zero_sq z,
          ← hr]
        field_simp
      rw [hsum, Real.sqrt_one]
    have hon : Orthonormal ℂ (({0} : Set (Fin d)).restrict (fun _ : Fin d => u)) := by
      refine ⟨fun i => by simpa using hnormu, fun i j hij => ?_⟩
      exact absurd (Subtype.ext ((Set.mem_singleton_iff.mp i.2).trans
        (Set.mem_singleton_iff.mp j.2).symm)) hij
    obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
    have hb0 : b 0 = u := hb 0 rfl
    refine ⟨Matrix.of fun i j => (b j : EuclideanSpace ℂ (Fin d)) i, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff']
      ext j k
      have hbo := (orthonormal_iff_ite.mp b.orthonormal) j k
      rw [PiLp.inner_apply] at hbo
      simp only [RCLike.inner_apply] at hbo
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
      simpa [RCLike.star_def, mul_comm] using hbo
    · rw [radialPoint, Matrix.mulVec_single]
      funext i
      change (b 0 : EuclideanSpace ℂ (Fin d)) i * (r : ℂ) = z i
      rw [hb0, huapp i]
      field_simp

end

end PolyFock
