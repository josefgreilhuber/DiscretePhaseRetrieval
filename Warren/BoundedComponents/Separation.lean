/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-! # Bounded components: Separation

Pure point-set topology on `Fin n → ℝ`.

* `exists_separating_opens`: finitely many pairwise distinct bounded connected components of a
  closed set `Z` can be separated by pairwise disjoint open sets `V i ⊆ ball 0 (M + 1)`, together
  with an open set `V'` disjoint from all `V i`, such that `Z ∩ closedBall 0 (M + 1)` is covered
  by `(⋃ i, V i) ∪ V'`.
* `exists_sublevel_subset`: if the zero set of a continuous nonnegative `Q` inside a closed ball is
  contained in an open set `U`, then a sublevel set `{Q < ε₀}` inside that ball is also in `U`.
* `connectedComponentIn_subset_of_subset_union`: a connected component is trapped in an open set
  `V ⊆ ball 0 R` when `F ∩ closedBall 0 R ⊆ V ∪ W` with `W` open and disjoint from `V`.
-/

namespace BoundedComponents

open Set Metric

variable {n : ℕ}

/-- In a compact Hausdorff space, the connected component of `y` can be separated from a compact
set `F` disjoint from it by a clopen set. -/
theorem exists_isClopen_subset_disjoint {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (y : X) {F : Set X} (hF : IsCompact F)
    (hdisj : Disjoint (connectedComponent y) F) :
    ∃ W : Set X, IsClopen W ∧ connectedComponent y ⊆ W ∧ Disjoint W F := by
  have key : ∀ z : F, ∃ W : Set X, IsClopen W ∧ y ∈ W ∧ (z : X) ∉ W := by
    intro z
    have hz : (z : X) ∉ connectedComponent y := fun h => Set.disjoint_left.1 hdisj h z.2
    rw [connectedComponent_eq_iInter_isClopen] at hz
    simp only [mem_iInter, not_forall, Subtype.exists, exists_prop] at hz
    obtain ⟨W, ⟨hW, hyW⟩, hzW⟩ := hz
    exact ⟨W, hW, hyW, hzW⟩
  choose W hW using key
  obtain ⟨t, ht⟩ := hF.elim_finite_subcover (fun z : F => (W z)ᶜ)
    (fun z => (hW z).1.1.isOpen_compl) (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, (hW ⟨z, hz⟩).2.2⟩)
  have hclopen : IsClopen (⋂ z ∈ t, W z) := isClopen_biInter_finset fun z _ => (hW z).1
  refine ⟨⋂ z ∈ t, W z, hclopen, ?_, ?_⟩
  · exact hclopen.connectedComponent_subset (mem_iInter₂.2 fun z _ => (hW z).2.1)
  · rw [Set.disjoint_left]
    intro p hp hpF
    obtain ⟨z, hzt, hpz⟩ := mem_iUnion₂.1 (ht hpF)
    exact hpz (mem_iInter₂.1 hp z hzt)

/-- In a compact Hausdorff space, finitely many pairwise distinct connected components, all
disjoint from a compact set `F`, are contained in pairwise disjoint clopen sets disjoint from
`F`. -/
theorem exists_isClopen_pairwise_disjoint {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {N : ℕ} (y : Fin N → X)
    (hy : ∀ i j, connectedComponent (y i) = connectedComponent (y j) → i = j)
    {F : Set X} (hF : IsCompact F) (hyF : ∀ i, Disjoint (connectedComponent (y i)) F) :
    ∃ W : Fin N → Set X, (∀ i, IsClopen (W i)) ∧ (∀ i, connectedComponent (y i) ⊆ W i) ∧
      Pairwise (fun i j => Disjoint (W i) (W j)) ∧ ∀ i, Disjoint (W i) F := by
  have hG : ∀ i : Fin N, IsCompact (F ∪ ⋃ j : {j // j ≠ i}, connectedComponent (y j.1)) :=
    fun i => hF.union (isCompact_iUnion fun j => isClosed_connectedComponent.isCompact)
  have hyG : ∀ i : Fin N, Disjoint (connectedComponent (y i))
      (F ∪ ⋃ j : {j // j ≠ i}, connectedComponent (y j.1)) := by
    intro i
    refine Disjoint.union_right (hyF i) (Set.disjoint_iUnion_right.2 fun j => ?_)
    exact connectedComponent_disjoint fun h => j.2 (hy _ _ h).symm
  choose W₀ hW₀ using fun i => exists_isClopen_subset_disjoint (y i) (hG i) (hyG i)
  have hW₀F : ∀ i j, j ≠ i → Disjoint (connectedComponent (y j)) (W₀ i) := by
    intro i j hji
    refine ((hW₀ i).2.2.mono_right ?_).symm
    exact (subset_iUnion (fun j : {j // j ≠ i} => connectedComponent (y j.1)) ⟨j, hji⟩).trans
      subset_union_right
  refine ⟨fun i => W₀ i \ ⋃ j : {j // j ≠ i}, W₀ j, fun i => ?_, fun i => ?_, ?_, fun i => ?_⟩
  · exact (hW₀ i).1.diff (isClopen_iUnion_of_finite fun j => (hW₀ j).1)
  · exact subset_diff.2 ⟨(hW₀ i).2.1, Set.disjoint_iUnion_right.2 fun j => hW₀F j i (Ne.symm j.2)⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro p hpi hpj
    exact hpj.2 (mem_iUnion.2 ⟨⟨i, hij⟩, hpi.1⟩)
  · exact ((hW₀ i).2.2.mono_right subset_union_left).mono_left diff_subset

/-- A positive lower bound for finitely many positive reals. -/
theorem exists_pos_forall_le {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  | inr h =>
    haveI := Fintype.ofFinite ι
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/-- **S1**: separation of finitely many bounded components of a closed set by disjoint open sets. -/
theorem exists_separating_opens (Z : Set (Fin n → ℝ)) (hZ : IsClosed Z) {N : ℕ}
    (x : Fin N → (Fin n → ℝ)) (hx : ∀ i, x i ∈ Z)
    (hdist : ∀ i j, connectedComponentIn Z (x i) = connectedComponentIn Z (x j) → i = j)
    (M : ℝ) (hM : ∀ i, connectedComponentIn Z (x i) ⊆ Metric.ball 0 M) :
    ∃ (V : Fin N → Set (Fin n → ℝ)) (V' : Set (Fin n → ℝ)),
      (∀ i, IsOpen (V i)) ∧ IsOpen V' ∧
      (∀ i, connectedComponentIn Z (x i) ⊆ V i) ∧
      (∀ i, V i ⊆ Metric.ball 0 (M + 1)) ∧
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧
      (∀ i, Disjoint (V i) V') ∧
      Z ∩ Metric.closedBall 0 (M + 1) ⊆ (⋃ i, V i) ∪ V' := by
  classical
  set K : Set (Fin n → ℝ) := Z ∩ closedBall 0 (M + 1) with hKdef
  have hK : IsCompact K := (isCompact_closedBall (0 : Fin n → ℝ) (M + 1)).inter_left hZ
  have hball : ball (0 : Fin n → ℝ) M ⊆ closedBall 0 (M + 1) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hCK : ∀ i, connectedComponentIn Z (x i) ⊆ K := fun i =>
    subset_inter (connectedComponentIn_subset Z (x i)) ((hM i).trans hball)
  have hxK : ∀ i, x i ∈ K := fun i => hCK i (mem_connectedComponentIn (hx i))
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨y, hy⟩ : ∃ y : Fin N → K, ∀ i, y i = ⟨x i, hxK i⟩ := ⟨_, fun _ => rfl⟩
  -- the components of `Z` at the `x i` are the images of the components of `K`
  have hCeq : ∀ i, connectedComponentIn Z (x i) = Subtype.val '' connectedComponent (y i) := by
    intro i
    rw [hy i, ← connectedComponentIn_eq_image (hxK i)]
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (hx i)) (hCK i)
    · exact connectedComponentIn_mono _ inter_subset_left
  have hydist : ∀ i j, connectedComponent (y i) = connectedComponent (y j) → i = j := by
    intro i j h
    apply hdist
    rw [hCeq i, hCeq j, h]
  -- the sphere, as a compact subset of `K`
  obtain ⟨S, hSdef⟩ : ∃ S : Set K, S = Subtype.val ⁻¹' sphere (0 : Fin n → ℝ) (M + 1) :=
    ⟨_, rfl⟩
  have hS : IsCompact S := by
    rw [hSdef]; exact (isClosed_sphere.preimage continuous_subtype_val).isCompact
  have hyS : ∀ i, Disjoint (connectedComponent (y i)) S := by
    intro i
    rw [Set.disjoint_left]
    intro p hp hpS
    have h1 : (p : Fin n → ℝ) ∈ connectedComponentIn Z (x i) := by
      rw [hCeq i]; exact mem_image_of_mem _ hp
    have h2 : (p : Fin n → ℝ) ∈ ball 0 M := hM i h1
    have h3 : (p : Fin n → ℝ) ∈ sphere 0 (M + 1) := by rw [hSdef] at hpS; exact hpS
    rw [mem_ball] at h2
    rw [mem_sphere] at h3
    linarith
  obtain ⟨W, hWclopen, hWsub, hWdisj, hWS⟩ := exists_isClopen_pairwise_disjoint y hydist hS hyS
  -- transport back to `Fin n → ℝ`
  obtain ⟨Kc, hKc⟩ : ∃ Kc : Fin N → Set (Fin n → ℝ), ∀ i, Kc i = Subtype.val '' W i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : Set (Fin n → ℝ), K' = Subtype.val '' (⋃ i, W i)ᶜ := ⟨_, rfl⟩
  have hKc_compact : ∀ i, IsCompact (Kc i) := fun i => by
    rw [hKc i]; exact (hWclopen i).1.isCompact.image continuous_subtype_val
  have hK'_compact : IsCompact K' := by
    rw [hK']
    exact (isOpen_iUnion fun i => (hWclopen i).2).isClosed_compl.isCompact.image
      continuous_subtype_val
  have hCKc : ∀ i, connectedComponentIn Z (x i) ⊆ Kc i := fun i => by
    rw [hKc i, hCeq i]; exact image_mono (hWsub i)
  have hKc_disj : Pairwise (fun i j => Disjoint (Kc i) (Kc j)) := fun i j hij => by
    change Disjoint (Kc i) (Kc j)
    rw [hKc i, hKc j]; exact (Set.disjoint_image_iff Subtype.val_injective).2 (hWdisj hij)
  have hKcK' : ∀ i, Disjoint (Kc i) K' := fun i => by
    rw [hKc i, hK']
    refine (Set.disjoint_image_iff Subtype.val_injective).2 ?_
    rw [Set.disjoint_left]
    intro p hp hp'
    exact hp' (mem_iUnion.2 ⟨i, hp⟩)
  have hKc_ball : ∀ i, Kc i ⊆ ball 0 (M + 1) := by
    intro i p hp
    rw [hKc i] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have h1 : (q : Fin n → ℝ) ∈ closedBall 0 (M + 1) :=
      (show (q : Fin n → ℝ) ∈ Z ∩ closedBall 0 (M + 1) from q.2).2
    have h2 : (q : Fin n → ℝ) ∉ sphere 0 (M + 1) := fun h =>
      Set.disjoint_left.1 (hWS i) hq (by rw [hSdef]; exact h)
    rw [mem_closedBall] at h1
    rw [mem_sphere] at h2
    rw [mem_ball]
    exact lt_of_le_of_ne h1 h2
  have hcover : K ⊆ (⋃ i, Kc i) ∪ K' := by
    intro p hp
    by_cases h : (⟨p, hp⟩ : K) ∈ ⋃ i, W i
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact Or.inl (mem_iUnion.2 ⟨i, by rw [hKc i]; exact ⟨_, hi, rfl⟩⟩)
    · exact Or.inr (by rw [hK']; exact ⟨_, h, rfl⟩)
  -- thickenings
  have hρ : ∀ i, ∃ ρ : ℝ, 0 < ρ ∧ thickening ρ (Kc i) ⊆ ball 0 (M + 1) := fun i =>
    (hKc_compact i).exists_thickening_subset_open isOpen_ball (hKc_ball i)
  choose ρ hρpos hρ using hρ
  have hother : ∀ i, IsCompact (K' ∪ ⋃ j : {j // j ≠ i}, Kc j) := fun i =>
    hK'_compact.union (isCompact_iUnion fun j => hKc_compact j.1)
  have hη : ∀ i, ∃ η : ℝ, 0 < η ∧
      Disjoint (thickening η (Kc i)) (thickening η (K' ∪ ⋃ j : {j // j ≠ i}, Kc j)) := by
    intro i
    refine Disjoint.exists_thickenings ?_ (hKc_compact i) (hother i).isClosed
    exact Disjoint.union_right (hKcK' i)
      (Set.disjoint_iUnion_right.2 fun j => hKc_disj (Ne.symm j.2))
  choose η hηpos hη using hη
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_forall_le (fun i => min (ρ i) (η i))
    (fun i => lt_min (hρpos i) (hηpos i))
  have hδρ : ∀ i, δ ≤ ρ i := fun i => (hδ i).trans (min_le_left _ _)
  have hδη : ∀ i, δ ≤ η i := fun i => (hδ i).trans (min_le_right _ _)
  refine ⟨fun i => thickening δ (Kc i), thickening δ K', fun i => isOpen_thickening,
    isOpen_thickening, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => (hCKc i).trans (self_subset_thickening hδpos _)
  · exact fun i => (thickening_mono (hδρ i) _).trans (hρ i)
  · intro i j hij
    refine (hη i).mono (thickening_mono (hδη i) _)
      ((thickening_mono (hδη i) _).trans (thickening_subset_of_subset _ ?_))
    exact (subset_iUnion (fun j : {j // j ≠ i} => Kc j) ⟨j, Ne.symm hij⟩).trans
      subset_union_right
  · intro i
    exact (hη i).mono (thickening_mono (hδη i) _)
      ((thickening_mono (hδη i) _).trans (thickening_subset_of_subset _ subset_union_left))
  · refine hcover.trans (union_subset_union ?_ (self_subset_thickening hδpos _))
    exact iUnion_mono fun i => self_subset_thickening hδpos _

/-- **S2**: sublevel capture. -/
theorem exists_sublevel_subset (Q : (Fin n → ℝ) → ℝ) (hQ : Continuous Q)
    (hQ0 : ∀ x, 0 ≤ Q x) (R : ℝ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hZU : {x | Q x = 0} ∩ Metric.closedBall 0 R ⊆ U) :
    ∃ ε₀ > 0, ∀ x ∈ Metric.closedBall 0 R, Q x < ε₀ → x ∈ U := by
  have hS : IsCompact (closedBall (0 : Fin n → ℝ) R \ U) := (isCompact_closedBall 0 R).diff hU
  rcases (closedBall (0 : Fin n → ℝ) R \ U).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun x hx _ => ?_⟩
    by_contra hxU
    have hmem : x ∈ closedBall (0 : Fin n → ℝ) R \ U := ⟨hx, hxU⟩
    rw [hemp] at hmem
    exact hmem
  · obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hQ.continuousOn
    refine ⟨Q x₀, ?_, fun x hx hlt => ?_⟩
    · exact lt_of_le_of_ne (hQ0 x₀) fun h => hx₀.2 (hZU ⟨h.symm, hx₀.1⟩)
    · by_contra hxU
      exact absurd ((isMinOn_iff.1 hmin) x ⟨hx, hxU⟩) (not_le.2 hlt)

/-- **S3**: trapping of a component in an open set. -/
theorem connectedComponentIn_subset_of_subset_union (F : Set (Fin n → ℝ)) (R : ℝ)
    (V W : Set (Fin n → ℝ)) (hV : IsOpen V) (hW : IsOpen W) (hVW : Disjoint V W)
    (hVR : V ⊆ Metric.ball 0 R) (hF : F ∩ Metric.closedBall 0 R ⊆ V ∪ W)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ V) (hx₀F : x₀ ∈ F) :
    connectedComponentIn F x₀ ⊆ V := by
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hV
    (hW.union (isClosed_closedBall : IsClosed (closedBall (0 : Fin n → ℝ) R)).isOpen_compl) ?_ ?_
    ⟨x₀, mem_connectedComponentIn hx₀F, hx₀⟩
  · refine Disjoint.union_right hVW ?_
    rw [Set.disjoint_left]
    intro p hp hp'
    exact hp' (ball_subset_closedBall (hVR hp))
  · intro p hp
    by_cases hpB : p ∈ closedBall (0 : Fin n → ℝ) R
    · rcases hF ⟨connectedComponentIn_subset F x₀ hp, hpB⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr hpB)

end BoundedComponents
