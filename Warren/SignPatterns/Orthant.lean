/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.Transversality

/-!
# Sign patterns: local orthant structure at a transversal point

Let `q 1, ..., q m` be polynomials in `n` real variables and let `x` be a point.  Let `J` be the
set of indices `j` with `q j (x) = 0`, and assume the gradients `∇(q j)(x)`, `j ∈ J`, are
linearly independent.  Then, by the implicit function theorem, near `x` the family
`(q j)_{j ∈ J}` looks like a system of coordinates: there is an open neighbourhood `W` of `x`
on which

* every `q k`, `k ∉ J`, has no zero;
* for every sign pattern `τ` on `J` (with no zeros), the set of points of `W` realising `τ`
  is preconnected (it is the image of a convex set under a homeomorphism);
* every common zero `z ∈ W` of the `q j`, `j ∈ J`, lies in the closure of each of these
  sign-pattern sets.

The main result is `SignPatterns.exists_orthant_nhd`.
-/

open MvPolynomial Metric Set Topology Filter
open AlgebraicTransversality

namespace SignPatterns

variable {n m : ℕ}

/-- The evaluation map `y ↦ (eval y (q j))_{j ∈ J}` is strictly differentiable, with derivative
the `pi` of the differentials `dualCLM (gradient (q j) x)`. -/
theorem hasStrictFDerivAt_evalPi (q : Fin m → MvPolynomial (Fin n) ℝ) (J : Finset (Fin m))
    (x : Fin n → ℝ) :
    HasStrictFDerivAt (fun y : Fin n → ℝ => fun j : J => eval y (q j))
      (ContinuousLinearMap.pi fun j : J => dualCLM (gradient (q j) x)) x := by
  refine hasStrictFDerivAt_pi.2 fun j => ?_
  have hcd : ContDiff ℝ 1 (fun y : Fin n → ℝ => eval y (q j)) :=
    (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ) (q j)).contDiff
  exact hcd.contDiffAt.hasStrictFDerivAt' (hasFDerivAt_eval (q j) x) one_ne_zero

/-- If the vectors `v j` are linearly independent, the map `u ↦ (⟨v j, u⟩)_j` is surjective. -/
theorem range_pi_dualCLM_eq_top {ι : Type*} [Finite ι] (v : ι → (Fin n → ℝ))
    (hv : LinearIndependent ℝ v) :
    (ContinuousLinearMap.pi fun j => dualCLM (v j)).range = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  set L : (Fin n → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun j => dualCLM (v j) with hL
  by_contra hne
  have hlt : L.range < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set c : ι → ℝ := fun i => φ (fun j => if i = j then 1 else 0) with hc
  have hexp : ∀ w : ι → ℝ, φ w = ∑ i, w i * c i := by
    intro w
    rw [LinearMap.pi_apply_eq_sum_univ]
    rfl
  have hker : ∀ k : Fin n, ∑ i, v i k * c i = 0 := by
    intro k
    have hmem := hφ (LinearMap.mem_range_self (L : (Fin n → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single k 1))
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hexp] at hmem
    simp only [hL, ContinuousLinearMap.pi_apply, dualCLM_single] at hmem
    exact hmem
  have hc0 : ∀ i, c i = 0 := by
    refine Fintype.linearIndependent_iff.1 hv c ?_
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hker k]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  apply hφ0
  refine LinearMap.ext fun w => ?_
  rw [hexp]
  simp [hc0]

/-- A convex set intersected with an open orthant (in the first factor) is convex. -/
theorem convex_inter_orthant {ι K : Type*} [AddCommGroup K] [Module ℝ K]
    (τ : ι → SignType) (hτ : ∀ j, τ j ≠ 0) (s : Set ((ι → ℝ) × K)) (hs : Convex ℝ s) :
    Convex ℝ (s ∩ ⋂ j, {w : (ι → ℝ) × K | SignType.sign (w.1 j) = τ j}) := by
  have hcases : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  refine hs.inter (convex_iInter fun j => ?_)
  have hlin : IsLinearMap ℝ (fun w : (ι → ℝ) × K => w.1 j) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rcases hcases (τ j) (hτ j) with h | h
  · have : {w : (ι → ℝ) × K | SignType.sign (w.1 j) = τ j} = {w | (0 : ℝ) < w.1 j} := by
      ext w; simp [h, sign_eq_one_iff]
    rw [this]
    exact convex_halfSpace_gt hlin 0
  · have : {w : (ι → ℝ) × K | SignType.sign (w.1 j) = τ j} = {w | w.1 j < (0 : ℝ)} := by
      ext w; simp [h, sign_eq_neg_one_iff]
    rw [this]
    exact convex_halfSpace_lt hlin 0

/-- A point with vanishing first factor lies in the closure of every open orthant. -/
theorem mem_closure_orthant {ι K : Type*} [TopologicalSpace K]
    (τ : ι → SignType) (hτ : ∀ j, τ j ≠ 0) (c : K) :
    ((0 : ι → ℝ), c) ∈ closure (⋂ j, {w : (ι → ℝ) × K | SignType.sign (w.1 j) = τ j}) := by
  have hcases : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  set τ' : ι → ℝ := fun j => SignType.cast (τ j) with hτ'
  have hlim : Tendsto (fun t : ℝ => ((t • τ', c) : (ι → ℝ) × K)) (𝓝[>] 0)
      (𝓝 ((0 : ι → ℝ), c)) := by
    have : Tendsto (fun t : ℝ => ((t • τ', c) : (ι → ℝ) × K)) (𝓝 0)
        (𝓝 (((0 : ℝ) • τ', c))) :=
      ((continuous_id.smul continuous_const).prodMk continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Set.mem_iInter]
  intro j
  change SignType.sign ((t • τ') j) = τ j
  rw [Pi.smul_apply, smul_eq_mul]
  have ht' : (0 : ℝ) < t := ht
  rcases hcases (τ j) (hτ j) with h | h
  · have h1 : τ' j = 1 := by
      change SignType.cast (τ j) = 1
      rw [h]
      rfl
    rw [h, h1, mul_one]
    exact sign_pos ht'
  · have h1 : τ' j = -1 := by
      change SignType.cast (τ j) = -1
      rw [h]
      rfl
    rw [h, h1, mul_neg, mul_one]
    exact sign_neg (neg_lt_zero.2 ht')

/-- **Local orthant structure at a transversal point.**

Let `J` be the set of indices of the polynomials vanishing at `x`, and assume their gradients
at `x` are linearly independent.  Then there is an open neighbourhood `W` of `x` such that no
other polynomial vanishes on `W`, every sign pattern on `J` is realised on a preconnected
subset of `W`, and every common zero (in `W`) of the `q j`, `j ∈ J`, is in the closure of each
of these sign-pattern sets. -/
theorem exists_orthant_nhd {n m : ℕ} (q : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (J : Finset (Fin m)) (hJ : ∀ j, j ∈ J ↔ MvPolynomial.eval x (q j) = 0)
    (hind : LinearIndependent ℝ (fun j : J => AlgebraicTransversality.gradient (q j) x)) :
    ∃ W : Set (Fin n → ℝ), IsOpen W ∧ x ∈ W ∧
      (∀ k ∉ J, ∀ y ∈ W, MvPolynomial.eval y (q k) ≠ 0) ∧
      ∀ τ : Fin m → SignType, (∀ j ∈ J, τ j ≠ 0) →
        IsPreconnected {y ∈ W | ∀ j ∈ J, SignType.sign (MvPolynomial.eval y (q j)) = τ j} ∧
        ∀ z ∈ W, (∀ j ∈ J, MvPolynomial.eval z (q j) = 0) →
          z ∈ closure {y ∈ W | ∀ j ∈ J, SignType.sign (MvPolynomial.eval y (q j)) = τ j} := by
  classical
  -- Step 1/2: the map `f`, its strict derivative `f'`, and surjectivity of `f'`.
  have hf : HasStrictFDerivAt (fun y : Fin n → ℝ => fun j : J => eval y (q j))
      (ContinuousLinearMap.pi fun j : J => dualCLM (gradient (q j) x)) x :=
    hasStrictFDerivAt_evalPi q J x
  have hf' : (ContinuousLinearMap.pi fun j : J => dualCLM (gradient (q j) x)).range = ⊤ :=
    range_pi_dualCLM_eq_top _ hind
  -- Step 3: the implicit-function chart.
  set Φ := hf.implicitToOpenPartialHomeomorph _ _ hf' with hΦ
  have hxs : x ∈ Φ.source := hf.mem_implicitToOpenPartialHomeomorph_source hf'
  have hΦfst : ∀ y (j : J), (Φ y).1 j = eval y (q j) := fun y j =>
    congrFun (hf.implicitToOpenPartialHomeomorph_fst hf' y) j
  -- Step 4: shrinking.
  set N : Set (Fin n → ℝ) := {y | ∀ k ∉ J, eval y (q k) ≠ 0} with hN
  have hNopen : IsOpen N := by
    have : N = ⋂ k ∈ (Jᶜ : Finset (Fin m)), {y : Fin n → ℝ | eval y (q k) ≠ 0} := by
      ext y; simp [hN, Finset.mem_compl]
    rw [this]
    exact isOpen_biInter_finset fun k _ =>
      isOpen_ne_fun (differentiable_evalPoly (q k)).continuous continuous_const
  have hxN : x ∈ N := fun k hk h => hk ((hJ k).2 h)
  have hΦxt : Φ x ∈ Φ.target := Φ.map_source hxs
  have hnhds : Φ.target ∩ Φ.symm ⁻¹' N ∈ 𝓝 (Φ x) := by
    refine Filter.inter_mem (Φ.open_target.mem_nhds hΦxt) ?_
    refine (Φ.continuousAt_symm hΦxt).preimage_mem_nhds ?_
    rw [Φ.left_inv hxs]
    exact hNopen.mem_nhds hxN
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  have hballt : ball (Φ x) r ⊆ Φ.target := fun w hw => (hball hw).1
  have hballN : ∀ w ∈ ball (Φ x) r, Φ.symm w ∈ N := fun w hw => (hball hw).2
  set W : Set (Fin n → ℝ) := Φ.symm '' ball (Φ x) r with hW
  have hWeq : W = Φ.source ∩ Φ ⁻¹' ball (Φ x) r :=
    Φ.symm_image_eq_source_inter_preimage hballt
  have hWopen : IsOpen W := by
    rw [hWeq]
    exact Φ.isOpen_inter_preimage isOpen_ball
  have hxW : x ∈ W := ⟨Φ x, mem_ball_self hr, Φ.left_inv hxs⟩
  have hWs : ∀ y ∈ W, y ∈ Φ.source := by
    intro y hy
    rw [hWeq] at hy
    exact hy.1
  have hWb : ∀ y ∈ W, Φ y ∈ ball (Φ x) r := by
    intro y hy
    rw [hWeq] at hy
    exact hy.2
  refine ⟨W, hWopen, hxW, fun k hk y hy => ?_, fun τ hτ => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hy
    exact hballN w hw k hk
  -- Step 5: the orthant upstairs.
  set O := ball (Φ x) r ∩ ⋂ j : J, {w | SignType.sign (w.1 j) = τ j} with hO
  have hOsub : O ⊆ ball (Φ x) r := Set.inter_subset_left
  have hOt : O ⊆ Φ.target := hOsub.trans hballt
  have hSeq : {y ∈ W | ∀ j ∈ J, SignType.sign (eval y (q j)) = τ j} = Φ.symm '' O := by
    ext y
    constructor
    · rintro ⟨hyW, hy⟩
      refine ⟨Φ y, ⟨hWb y hyW, ?_⟩, Φ.left_inv (hWs y hyW)⟩
      rw [Set.mem_iInter]
      intro j
      change SignType.sign ((Φ y).1 j) = τ j
      rw [hΦfst]
      exact hy j j.2
    · rintro ⟨w, ⟨hwb, hw⟩, rfl⟩
      refine ⟨⟨w, hwb, rfl⟩, fun j hj => ?_⟩
      rw [Set.mem_iInter] at hw
      have h0 := hw ⟨j, hj⟩
      rw [Set.mem_setOf_eq] at h0
      have h1 : eval (Φ.symm w) (q j) = w.1 ⟨j, hj⟩ := by
        have h2 := hΦfst (Φ.symm w) ⟨j, hj⟩
        rw [Φ.right_inv (hballt hwb)] at h2
        exact h2.symm
      rw [h1]
      exact h0
  have hOconv : Convex ℝ O :=
    convex_inter_orthant (fun j : J => τ j) (fun j => hτ j j.2) _ (convex_ball _ _)
  refine ⟨?_, fun z hzW hz => ?_⟩
  · rw [hSeq]
    exact hOconv.isPreconnected.image Φ.symm (Φ.continuousOn_symm.mono hOt)
  -- Step 6: closure.
  have hΦz : Φ z = ((0 : J → ℝ), (Φ z).2) := by
    refine Prod.ext ?_ rfl
    funext j
    rw [hΦfst z j, hz j j.2]
    rfl
  have hcl : Φ z ∈ closure (⋂ j : J, {w | SignType.sign (w.1 j) = τ j}) := by
    rw [hΦz]
    exact mem_closure_orthant (fun j : J => τ j) (fun j => hτ j j.2) (Φ z).2
  have hclO : Φ z ∈ closure O := isOpen_ball.inter_closure ⟨hWb z hzW, hcl⟩
  have hcw : ContinuousWithinAt Φ.symm O (Φ z) :=
    (Φ.continuousOn_symm.continuousWithinAt (hballt (hWb z hzW))).mono hOt
  have := hcw.mem_closure_image hclO
  rw [Φ.left_inv (hWs z hzW)] at this
  rw [hSeq]
  exact this

end SignPatterns
