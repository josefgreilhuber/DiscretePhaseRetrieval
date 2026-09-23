/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Rotation
import PolyFock.Fock.Kernel

/-!
# The radial reduction, proved

Rotation invariance of the layer kernels (`PolyFock.Fock.layer_diag_rot`) reduces the tail at
an arbitrary `z ∈ ℂ^d` to the tail at the radial point `(|z|, 0, …, 0)`: every finite partial
sum of `∑ ‖Φ_{𝐧,𝐪}(z)‖²` over the tail index set is bounded by a finite partial sum of the
same quantity at the radial point, because the index set is a disjoint union of layers and
each layer sum is rotation invariant.
-/

namespace PolyFock

open Finset Matrix Fock
open DiscretePR (euclideanDist Φ)
open scoped DiscretePR

noncomputable section

variable {d : ℕ}

/-- **The radial reduction.**  Any uniform bound on the finite partial sums of the tail at the
radial point `(|z|, 0, …, 0)` bounds the tail at `z`. -/
theorem tailKernelDiag_le_of_radial_bound [NeZero d] (L N : ℕ) (z : Fin d → ℂ) (c : ℝ)
    (hc : ∀ S : Finset ((Fin d → ℕ) × (Fin d → ℕ)),
      ∑ p ∈ S, (if ‖p.2‖₁ = L ∧ N < ‖p.1‖₁ then
        ‖Φ p.1 p.2 (radialPoint (d := d) (euclideanDist z 0))‖ ^ 2 else 0) ≤ c) :
    tailKernelDiag L N z ≤ c := by
  classical
  obtain ⟨U, hU, hUz⟩ := exists_unitary_radialPoint z
  refine Real.tsum_le_of_sum_le (fun p => diagTerm_nonneg L N z p) ?_
  intro S
  set cond : (Fin d → ℕ) × (Fin d → ℕ) → Prop :=
    fun p => ‖p.2‖₁ = L ∧ N < ‖p.1‖₁ with hcond
  set K : Finset ℕ := (S.image (fun p => ‖p.1‖₁)).filter (fun k => N < k) with hK
  set S' : Finset ((Fin d → ℕ) × (Fin d → ℕ)) := K.biUnion (fun k => LayerIdx d k L) with hS'
  have hdisj : (K : Set ℕ).PairwiseDisjoint (fun k => LayerIdx d k L) := by
    intro k _ k' _ hne
    refine Finset.disjoint_left.mpr fun p hp hp' => ?_
    rw [mem_LayerIdx] at hp hp'
    exact hne (hp.1.symm.trans hp'.1)
  -- Step 1: restrict to the support and enlarge to a union of layers.
  have hsub : S.filter cond ⊆ S' := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hS', Finset.mem_biUnion]
    refine ⟨‖p.1‖₁, ?_, mem_LayerIdx.mpr ⟨rfl, hp.2.1⟩⟩
    rw [hK, Finset.mem_filter]
    exact ⟨Finset.mem_image_of_mem _ hp.1, hp.2.2⟩
  have hrestrict : ∑ p ∈ S, (if cond p then ‖Φ p.1 p.2 z‖ ^ 2 else 0)
      = ∑ p ∈ S.filter cond, (if cond p then ‖Φ p.1 p.2 z‖ ^ 2 else 0) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun p hpS hp => ?_).symm
    rw [Finset.mem_filter] at hp
    rw [if_neg (fun hc => hp ⟨hpS, hc⟩)]
  -- Step 2: each layer sum is rotation invariant.
  have hlayer : ∀ k ∈ K, ∑ p ∈ LayerIdx d k L, (if cond p then ‖Φ p.1 p.2 z‖ ^ 2 else 0)
      = ∑ p ∈ LayerIdx d k L,
          (if cond p then ‖Φ p.1 p.2 (radialPoint (d := d) (euclideanDist z 0))‖ ^ 2 else 0) := by
    intro k hk
    rw [hK, Finset.mem_filter] at hk
    have hcondall : ∀ p ∈ LayerIdx d k L, cond p := by
      intro p hp
      rw [mem_LayerIdx] at hp
      exact ⟨hp.2, by rw [hp.1]; exact hk.2⟩
    have hinv := layer_diag_rot hU k L (radialPoint (d := d) (euclideanDist z 0))
    rw [hUz] at hinv
    rw [Finset.sum_congr rfl fun p hp => if_pos (hcondall p hp),
      Finset.sum_congr rfl fun p hp => if_pos (hcondall p hp)]
    exact hinv
  calc ∑ p ∈ S, (if cond p then ‖Φ p.1 p.2 z‖ ^ 2 else 0)
      = ∑ p ∈ S.filter cond, (if cond p then ‖Φ p.1 p.2 z‖ ^ 2 else 0) := hrestrict
    _ ≤ ∑ p ∈ S', (if cond p then ‖Φ p.1 p.2 z‖ ^ 2 else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => ?_
        split <;> positivity
    _ = ∑ k ∈ K, ∑ p ∈ LayerIdx d k L, (if cond p then ‖Φ p.1 p.2 z‖ ^ 2 else 0) :=
        Finset.sum_biUnion hdisj
    _ = ∑ k ∈ K, ∑ p ∈ LayerIdx d k L,
          (if cond p then ‖Φ p.1 p.2 (radialPoint (d := d) (euclideanDist z 0))‖ ^ 2 else 0) :=
        Finset.sum_congr rfl hlayer
    _ = ∑ p ∈ S', (if cond p then
          ‖Φ p.1 p.2 (radialPoint (d := d) (euclideanDist z 0))‖ ^ 2 else 0) :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ c := hc S'

end

end PolyFock
