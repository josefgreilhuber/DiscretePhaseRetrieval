/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.PolynomialSard
import Warren.BoundedComponents.Separation
import Warren.BoundedComponents.CriticalPoint
import Warren.BoundedComponents.Perturbation

/-! # Bounded components: Main

The joint real zero set of polynomials `p₁, …, pₘ` in `n` variables of degree `≤ d` has at most
`(2d)ⁿ` bounded connected components (`bounded_components`).

Proof sketch.  Given `N` pairwise distinct bounded components with base points `x i`, separate
them by disjoint open sets `V i` (`exists_separating_opens`), all inside a ball of radius `R`.
Let `Q = Σ pᵢ²`.  Perturb to `F = Q − ε + δ Σⱼ xⱼ^(2d+1)` with `ε, δ` small: then `F < 0` on
each component and the sublevel set `{F ≤ 0} ∩ closedBall 0 R` lies in `(⋃ V i) ∪ V'`, so the
component of `x i` in `{F ≤ 0}` is trapped in `V i` and bounded, hence contains a critical point
of `F` (`exists_fderiv_eq_zero_of_isBounded`).  These `N` critical points are distinct, and the
critical set of `F` has at most `(2d)ⁿ` points (`criticalSet_pert_finite`).
-/

namespace BoundedComponents

open Set Metric MvPolynomial

variable {n m : ℕ}

/-- The joint real zero set of the polynomials `p i`. -/
def zeroSet (p : Fin m → MvPolynomial (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {y | ∀ k, eval y (p k) = 0}

/-- The set of bounded connected components of the joint zero set. -/
def boundedComponents (p : Fin m → MvPolynomial (Fin n) ℝ) : Set (Set (Fin n → ℝ)) :=
  {C | ∃ x, (∀ i, eval x (p i) = 0) ∧ C = connectedComponentIn (zeroSet p) x ∧
    Bornology.IsBounded C}

theorem isClosed_zeroSet (p : Fin m → MvPolynomial (Fin n) ℝ) : IsClosed (zeroSet p) := by
  have h : zeroSet p = ⋂ k, {y | eval y (p k) = 0} := by
    ext y
    simp [zeroSet]
  rw [h]
  exact isClosed_iInter fun k =>
    isClosed_eq (AlgebraicTransversality.differentiable_evalPoly (p k)).continuous
      continuous_const

/-- **Core lemma.** Any `N` pairwise distinct bounded components of the joint zero set satisfy
`N ≤ (2d)ⁿ`. -/
theorem card_le_of_boundedComponents (p : Fin m → MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hdeg : ∀ i, (p i).totalDegree ≤ d) {N : ℕ}
    (x : Fin N → (Fin n → ℝ)) (hx : ∀ i, ∀ k, eval (x i) (p k) = 0)
    (hdist : ∀ i j, connectedComponentIn (zeroSet p) (x i) = connectedComponentIn (zeroSet p) (x j)
      → i = j)
    (hbdd : ∀ i, Bornology.IsBounded (connectedComponentIn (zeroSet p) (x i))) :
    N ≤ (2 * d) ^ n := by
  classical
  have hZ : IsClosed (zeroSet p) := isClosed_zeroSet p
  have hx' : ∀ i, x i ∈ zeroSet p := fun i => hx i
  -- a common ball containing all the components
  obtain ⟨M, hM1, hM⟩ :
      ∃ M : ℝ, 1 ≤ M ∧ ∀ i, connectedComponentIn (zeroSet p) (x i) ⊆ ball 0 M := by
    have hb : Bornology.IsBounded (⋃ i, connectedComponentIn (zeroSet p) (x i)) :=
      Bornology.isBounded_iUnion.2 hbdd
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_ball 0).1 hb
    exact ⟨max r 1, le_max_right _ _, fun i =>
      ((subset_iUnion _ i).trans hr).trans (ball_subset_ball (le_max_left _ _))⟩
  set R : ℝ := M + 1 with hRdef
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 ≤ R := by linarith
  -- separating open sets
  obtain ⟨V, V', hVopen, hV'open, hCV, hVball, hVdisj, hVV', hcover⟩ :=
    exists_separating_opens (zeroSet p) hZ x hx' hdist M hM
  -- the sum of squares
  set Q : (Fin n → ℝ) → ℝ := fun y => eval y (sumSq p) with hQdef
  have hQ : Continuous Q := (AlgebraicTransversality.differentiable_evalPoly _).continuous
  have hQ0 : ∀ y, 0 ≤ Q y := fun y => sumSq_nonneg p y
  have hQZ : {y | Q y = 0} = zeroSet p := by
    ext y
    change eval y (sumSq p) = 0 ↔ ∀ k, eval y (p k) = 0
    exact eval_sumSq_eq_zero_iff p y
  set U : Set (Fin n → ℝ) := (⋃ i, V i) ∪ V' with hUdef
  have hU : IsOpen U := (isOpen_iUnion hVopen).union hV'open
  have hZU : {y | Q y = 0} ∩ closedBall 0 R ⊆ U := by
    rw [hQZ]
    exact hcover
  obtain ⟨ε₀, hε₀, hsub⟩ := exists_sublevel_subset Q hQ hQ0 R U hU hZU
  -- the constants
  set ε : ℝ := ε₀ / 2 with hεdef
  have hε : 0 < ε := half_pos hε₀
  set A : ℝ := (n : ℝ) * R ^ (2 * d + 1) with hAdef
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hR0 _)
  set δ : ℝ := ε / (2 * (A + 1)) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδA : δ * A ≤ ε / 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (A + 1))]
    have h : ε / 2 * (2 * (A + 1)) = ε * A + ε := by ring
    rw [h]
    linarith
  -- the perturbed polynomial
  set F : (Fin n → ℝ) → ℝ := fun y => eval y (pert p ε δ d) with hFdef
  have hF : Differentiable ℝ F := AlgebraicTransversality.differentiable_evalPoly _
  have hkey : ∀ y, ‖y‖ ≤ R → |F y - (Q y - ε)| ≤ ε / 2 := by
    intro y hy
    have h := abs_eval_pert_sub_le p ε δ d y hy hR0
    rw [abs_of_pos hδ] at h
    calc |F y - (Q y - ε)| ≤ δ * n * R ^ (2 * d + 1) := h
      _ = δ * A := by rw [hAdef]; ring
      _ ≤ ε / 2 := hδA
  -- (a) `F < 0` on the components
  have hFneg : ∀ i, ∀ y ∈ connectedComponentIn (zeroSet p) (x i), F y < 0 := by
    intro i y hy
    have hyZ : y ∈ zeroSet p := connectedComponentIn_subset (zeroSet p) (x i) hy
    have hQy : Q y = 0 := by
      rw [← hQZ] at hyZ
      exact hyZ
    have hyR : ‖y‖ ≤ R := by
      have := hM i hy
      rw [mem_ball_zero_iff] at this
      linarith
    obtain ⟨h1, h2⟩ := abs_le.1 (hkey y hyR)
    rw [hQy] at h2
    linarith
  -- (b) the sublevel set inside the ball lies in `U`
  have hsubU : ∀ y, F y ≤ 0 → ‖y‖ ≤ R → y ∈ U := by
    intro y hFy hyR
    obtain ⟨h1, h2⟩ := abs_le.1 (hkey y hyR)
    have hQy : Q y < ε₀ := by linarith
    exact hsub y (mem_closedBall_zero_iff.2 hyR) hQy
  -- trapping: the component of `x i` in `{F ≤ 0}` lies in `V i`
  have hDsub : ∀ i, connectedComponentIn {y | F y ≤ 0} (x i) ⊆ V i := by
    intro i
    set W : Set (Fin n → ℝ) := (⋃ j : {j // j ≠ i}, V j.1) ∪ V' with hWdef
    have hW : IsOpen W := (isOpen_iUnion fun j : {j // j ≠ i} => hVopen j.1).union hV'open
    have hVW : Disjoint (V i) W :=
      Disjoint.union_right (Set.disjoint_iUnion_right.2 fun j => hVdisj (Ne.symm j.2)) (hVV' i)
    have hFU : {y | F y ≤ 0} ∩ closedBall 0 R ⊆ V i ∪ W := by
      rintro y ⟨hy1, hy2⟩
      have hyU : y ∈ U := hsubU y hy1 (mem_closedBall_zero_iff.1 hy2)
      rcases hyU with hyV | hyV'
      · obtain ⟨j, hj⟩ := mem_iUnion.1 hyV
        by_cases hji : j = i
        · rw [hji] at hj
          exact Or.inl hj
        · exact Or.inr (Or.inl (mem_iUnion.2 ⟨⟨j, hji⟩, hj⟩))
      · exact Or.inr (Or.inr hyV')
    have hxV : x i ∈ V i := hCV i (mem_connectedComponentIn (hx' i))
    have hxF : x i ∈ {y | F y ≤ 0} := (hFneg i (x i) (mem_connectedComponentIn (hx' i))).le
    exact connectedComponentIn_subset_of_subset_union _ R (V i) W (hVopen i) hW hVW (hVball i)
      hFU (x i) hxV hxF
  have hDbdd : ∀ i, Bornology.IsBounded (connectedComponentIn {y | F y ≤ 0} (x i)) :=
    fun i => isBounded_ball.subset ((hDsub i).trans (hVball i))
  -- critical points
  have hcrit : ∀ i, ∃ y ∈ connectedComponentIn {y | F y ≤ 0} (x i),
      y ∈ PolynomialSard.criticalSet (pert p ε δ d) := by
    intro i
    obtain ⟨y, hy, hfy⟩ := exists_fderiv_eq_zero_of_isBounded F hF (x i)
      (hFneg i (x i) (mem_connectedComponentIn (hx' i))) (hDbdd i)
    exact ⟨y, hy, (fderiv_eval_eq_zero_iff (pert p ε δ d) y).1 hfy⟩
  choose y hyD hycrit using hcrit
  -- the critical points are distinct
  have hyinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    have hi : y i ∈ V i := hDsub i (hyD i)
    have hj : y i ∈ V j := by
      rw [hij]
      exact hDsub j (hyD j)
    exact Set.disjoint_left.1 (hVdisj hne) hi hj
  -- counting
  obtain ⟨hfin, hcard⟩ := criticalSet_pert_finite p ε δ d hd hdeg hδ.ne'
  have hrange : Set.range y ⊆ PolynomialSard.criticalSet (pert p ε δ d) := by
    rintro _ ⟨i, rfl⟩
    exact hycrit i
  calc N = (Set.range y).ncard := by
        rw [Set.ncard_range_of_injective hyinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    _ ≤ (PolynomialSard.criticalSet (pert p ε δ d)).ncard := Set.ncard_le_ncard hrange hfin
    _ ≤ (2 * d) ^ n := hcard

/-- A set all of whose finite injective enumerations have length `≤ B` is finite with at most
`B` elements. -/
theorem finite_and_ncard_le_of_forall_injective {α : Type*} {Z : Set α} {B : ℕ}
    (h : ∀ (N : ℕ) (x : Fin N → α), Function.Injective x → (∀ j, x j ∈ Z) → N ≤ B) :
    Z.Finite ∧ Z.ncard ≤ B := by
  classical
  have hfinset : ∀ T : Finset α, ↑T ⊆ Z → T.card ≤ B := by
    intro T hT
    have hinj : Function.Injective fun j : Fin T.card => (T.equivFin.symm j : α) :=
      Subtype.coe_injective.comp T.equivFin.symm.injective
    exact h T.card _ hinj fun j => hT (Finset.mem_coe.mpr (T.equivFin.symm j).2)
  have hfin : Z.Finite := by
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (B + 1)
    have := hfinset T hTsub
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card Z hfin]
  exact hfinset hfin.toFinset hfin.coe_toFinset.subset

/-- **Bounded components bound.** The joint zero set of polynomials `p₁, …, pₘ` in `n` real
variables of degree `≤ d` has at most `(2d)ⁿ` bounded connected components. -/
theorem bounded_components {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hdeg : ∀ i, (p i).totalDegree ≤ d) :
    (boundedComponents p).Finite ∧ (boundedComponents p).ncard ≤ (2 * d) ^ n := by
  apply finite_and_ncard_le_of_forall_injective
  intro N C hinj hmem
  have hmem' : ∀ j, ∃ x, (∀ i, eval x (p i) = 0) ∧
      C j = connectedComponentIn (zeroSet p) x ∧ Bornology.IsBounded (C j) := hmem
  choose x hx hCx hbC using hmem'
  refine card_le_of_boundedComponents p d hd hdeg x hx ?_ ?_
  · intro i j hij
    apply hinj
    rw [hCx i, hCx j, hij]
  · intro i
    rw [← hCx i]
    exact hbC i

end BoundedComponents
