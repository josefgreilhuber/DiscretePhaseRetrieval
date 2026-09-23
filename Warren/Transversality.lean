/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-!
# Algebraic Thom transversality

Let `p 1, ..., p m` be polynomials in `n` real variables.  This file proves that after an
arbitrarily small perturbation of their coefficients one can arrange that, **for every
subfamily**, the differentials are linearly independent at every common zero of that
subfamily:

* `AlgebraicTransversality.transversality` — the statement with the gradient vectors
  `(∂(q k)/∂xⱼ)(x)`.

The perturbation is explicit: only the coefficients of degree `≤ 1` are moved, i.e.
`q k = p k + ∑ j, C (a k j) * X j + C (c k)` with all `|a k j|, |c k| < ε`.

## Proof strategy

Full Sard's theorem is *not* needed.  Because we perturb the linear coefficients as well as
the constant terms, the set of bad parameters is covered by finitely many images of maps
whose derivative is everywhere singular, and the easy "fixed dimension" Sard lemma
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` applies.

Concretely, write a perturbation parameter as `z : Param m n = (Fin m × Fin n → ℝ) × (Fin m → ℝ)`,
so `q k = p k + ∑ j, C (z.1 (k, j)) * X j + C (z.2 k)`.  Transversality fails at `z` exactly
when there are a point `x` and a nonzero multiplier vector `lam` with
`lam k ≠ 0 → q k (x) = 0` and `∑ k, lam k • ∇(q k)(x) = 0` (this is `Bad`).

Given such a failure, normalise `lam` at some index `i` where it is nonzero, and let `S` be
its support.  Then `x`, the multipliers `lam k` for `k ∈ S \ {i}`, the coefficients
`z.1 (k, ·)` for `k ≠ i`, and the constants `z.2 k` for `k ∉ S` determine `z` completely:
the relation `∑ k, lam k • ∇(q k)(x) = 0` solves for `z.1 (i, ·)`, and `q k (x) = 0` solves
for `z.2 k`, `k ∈ S`.  This is the map `cover p S i`, a self-map of the parameter space that
*does not depend on the coordinate `z.2 i`* (`cover_kill`); hence its derivative is
everywhere singular and its image is null (`measure_range_cover`).  Since a ball has
positive measure, good parameters exist arbitrarily close to `0` (`exists_not_bad`).
-/

open MvPolynomial MeasureTheory Metric Set

namespace AlgebraicTransversality

variable {n : ℕ}

/-- The gradient of a multivariate polynomial `q` at `x`, as the vector of partial
derivatives `(∂q/∂xⱼ)(x)`. -/
noncomputable def gradient (q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => eval x (pderiv j q)

/-- The linear functional `v ↦ ∑ j, w j * v j` attached to a vector `w`. -/
noncomputable def dualCLM (w : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, w j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)

@[simp] lemma dualCLM_apply (w v : Fin n → ℝ) : dualCLM w v = ∑ j, w j * v j := by
  simp [dualCLM]

@[simp] lemma dualCLM_single (w : Fin n → ℝ) (j : Fin n) :
    dualCLM w (Pi.single j 1) = w j := by
  simp [dualCLM_apply, Pi.single_apply, Finset.sum_ite_eq']

/-- Evaluation of a polynomial is differentiable, with derivative given by the gradient. -/
theorem hasFDerivAt_eval (q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => eval y q) (dualCLM (gradient q x)) x := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      have hg : dualCLM (gradient (C a : MvPolynomial (Fin n) ℝ) x) = 0 := by
        ext v; simp [dualCLM_apply, gradient]
      simp only [eval_C, hg]
      exact hasFDerivAt_const a x
  | add q r hq hr =>
      have hg : dualCLM (gradient (q + r) x)
          = dualCLM (gradient q x) + dualCLM (gradient r x) := by
        ext v
        simp [dualCLM_apply, gradient, add_mul, Finset.sum_add_distrib]
      simp only [map_add, hg]
      exact hq.add hr
  | mul_X q i hq =>
      have hx : HasFDerivAt (fun y : Fin n → ℝ => y i)
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply i x
      have h := hq.mul hx
      have key : ∀ j, eval x (pderiv j (q * X i))
          = eval x (pderiv j q) * x i + (if j = i then eval x q else 0) := by
        intro j
        rw [pderiv_mul]
        simp only [pderiv_X, map_add, map_mul, eval_X, Pi.single_apply]
        rcases eq_or_ne j i with rfl | hj
        · simp
        · simp [hj, Ne.symm hj]
      have hg : dualCLM (gradient (q * X i) x)
          = eval x q • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
            + x i • dualCLM (gradient q x) := by
        ext v
        simp only [dualCLM_apply, gradient, key, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
          add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, Finset.mul_sum]
        ring_nf
        rw [add_comm]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      simp only [map_mul, eval_X, hg]
      exact h

/-! ## Part 2: the perturbation and its parameter space -/

variable {m : ℕ}

/-- The space of perturbation parameters: a linear coefficient `z.1 (k, j)` for each
variable `xⱼ` in each polynomial `p k`, and a constant term `z.2 k` for each `p k`. -/
abbrev Param (m n : ℕ) := (Fin m × Fin n → ℝ) × (Fin m → ℝ)

noncomputable instance : Measure.IsAddHaarMeasure (volume : Measure (Param m n)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The perturbed family of polynomials: only the degree `≤ 1` coefficients are moved. -/
noncomputable def pert (p : Fin m → MvPolynomial (Fin n) ℝ) (z : Param m n) (k : Fin m) :
    MvPolynomial (Fin n) ℝ :=
  p k + (∑ j, C (z.1 (k, j)) * X j) + C (z.2 k)

@[simp] lemma eval_pert (p : Fin m → MvPolynomial (Fin n) ℝ) (z : Param m n) (k : Fin m)
    (x : Fin n → ℝ) :
    eval x (pert p z k) = eval x (p k) + (∑ j, z.1 (k, j) * x j) + z.2 k := by
  simp [pert]

@[simp] lemma gradient_pert (p : Fin m → MvPolynomial (Fin n) ℝ) (z : Param m n) (k : Fin m)
    (x : Fin n → ℝ) (j : Fin n) :
    gradient (pert p z k) x j = gradient (p k) x j + z.1 (k, j) := by
  simp [gradient, pert, Pi.single_apply, Finset.sum_ite_eq']

/-! ## Part 3: bad parameters -/

/-- `z` is a **bad** parameter for `p` when the perturbed family `pert p z` fails
transversality: there is a point `x` and a nonzero vector of multipliers `lam`,
supported on indices where the perturbed polynomial vanishes at `x`, which annihilates
the corresponding gradients. -/
def Bad (p : Fin m → MvPolynomial (Fin n) ℝ) (z : Param m n) : Prop :=
  ∃ (x : Fin n → ℝ) (lam : Fin m → ℝ), lam ≠ 0 ∧
    (∀ k, lam k ≠ 0 → eval x (pert p z k) = 0) ∧
    ∀ j, ∑ k, lam k * gradient (pert p z k) x j = 0

/-- A parameter that is not bad yields a transversal perturbed family. -/
theorem linearIndependent_of_not_bad (p : Fin m → MvPolynomial (Fin n) ℝ) (z : Param m n)
    (hz : ¬ Bad p z) (x : Fin n → ℝ) (S : Finset (Fin m))
    (hS : ∀ k ∈ S, eval x (pert p z k) = 0) :
    LinearIndependent ℝ (fun k : S => gradient (pert p z k) x) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k0
  set lam : Fin m → ℝ := fun k => if h : k ∈ S then g ⟨k, h⟩ else 0 with hlamdef
  have hlamS : ∀ k (hk : k ∈ S), lam k = g ⟨k, hk⟩ := fun k hk => dif_pos hk
  have hlamnot : ∀ k, k ∉ S → lam k = 0 := fun k hk => dif_neg hk
  have hlam0 : lam = 0 := by
    by_contra hne
    refine hz ⟨x, lam, hne, ?_, ?_⟩
    · intro k hk
      refine hS k ?_
      by_contra hkS
      exact hk (hlamnot k hkS)
    · intro j
      have h0 : ∑ k : S, g k * gradient (pert p z (k : Fin m)) x j = 0 := by
        have := congrFun hg j
        simpa [Finset.sum_apply] using this
      have h1 : ∑ k ∈ S, lam k * gradient (pert p z k) x j = 0 := by
        rw [← Finset.sum_coe_sort S (fun k => lam k * gradient (pert p z k) x j)]
        rw [← h0]
        exact Finset.sum_congr rfl fun k _ => by rw [hlamS k k.2]
      rw [← Finset.sum_subset (Finset.subset_univ S) ?_]
      · exact h1
      · intro k _ hk
        rw [hlamnot k hk, zero_mul]
  have := congrFun hlam0 (k0 : Fin m)
  rw [hlamS (k0 : Fin m) k0.2] at this
  simpa using this

/-! ## Part 4: the covering maps

For each pair `(S, i)` we build a self-map `cover p S i` of the parameter space which does
not depend on the coordinate `z.2 i`, and whose image contains every bad parameter whose
witnessing multiplier vector is supported in `S` and nonzero at `i`. -/

/-- The point of `ℝⁿ` read off from a parameter. -/
def coverX (i : Fin m) (w : Param m n) : Fin n → ℝ := fun j => w.1 (i, j)

/-- The multipliers read off from a parameter, normalised so that the `i`-th one is `1`. -/
def coverLam (S : Finset (Fin m)) (i : Fin m) (w : Param m n) : Fin m → ℝ :=
  fun k => if k = i then 1 else if k ∈ S then w.2 k else 0

/-- The linear coefficients produced by the covering map. -/
noncomputable def coverA (p : Fin m → MvPolynomial (Fin n) ℝ) (S : Finset (Fin m)) (i : Fin m)
    (w : Param m n) : Fin m × Fin n → ℝ := fun kj =>
  if kj.1 = i then
    -(gradient (p i) (coverX i w) kj.2)
      - ∑ k ∈ Finset.univ.erase i,
          coverLam S i w k * (gradient (p k) (coverX i w) kj.2 + w.1 (k, kj.2))
  else w.1 kj

/-- The covering map attached to the pair `(S, i)`. -/
noncomputable def cover (p : Fin m → MvPolynomial (Fin n) ℝ) (S : Finset (Fin m)) (i : Fin m)
    (w : Param m n) : Param m n :=
  (coverA p S i w,
    fun k => if k ∈ insert i S then
        -(eval (coverX i w) (p k) + ∑ j, coverA p S i w (k, j) * coverX i w j)
      else w.2 k)

/-- Every bad parameter lies in the image of one of the covering maps. -/
theorem bad_mem_range (p : Fin m → MvPolynomial (Fin n) ℝ) (z : Param m n) (hz : Bad p z) :
    ∃ (S : Finset (Fin m)) (i : Fin m), z ∈ Set.range (cover p S i) := by
  classical
  obtain ⟨x, lam, hne, hvanish, hdep⟩ := hz
  obtain ⟨i, hi⟩ : ∃ i, lam i ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hne (funext h)
  set mu : Fin m → ℝ := fun k => lam k / lam i with hmudef
  have hmui : mu i = 1 := div_self hi
  have hmuz : ∀ k, mu k ≠ 0 → lam k ≠ 0 := by
    intro k hk h0
    exact hk (by simp [hmudef, h0])
  set S : Finset (Fin m) := Finset.univ.filter (fun k => mu k ≠ 0) with hSdef
  have hmemS : ∀ k, k ∈ S ↔ mu k ≠ 0 := by intro k; simp [hSdef]
  obtain ⟨w, hw1, hw2⟩ : ∃ w : Param m n,
      (∀ kj, w.1 kj = if kj.1 = i then x kj.2 else z.1 kj) ∧
      (∀ k, w.2 k = if k = i then 0 else if k ∈ S then mu k else z.2 k) :=
    ⟨(fun kj => if kj.1 = i then x kj.2 else z.1 kj,
      fun k => if k = i then 0 else if k ∈ S then mu k else z.2 k), fun _ => rfl, fun _ => rfl⟩
  have hX : coverX i w = x := by funext j; simp [coverX, hw1]
  have hLam : coverLam S i w = mu := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [coverLam, hmui]
    · by_cases hkS : k ∈ S
      · simp [coverLam, hk, hkS, hw2]
      · have h0 : mu k = 0 := by
          by_contra h
          exact hkS ((hmemS k).2 h)
        simp [coverLam, hk, hkS, h0]
  have hdep' : ∀ j, ∑ k, mu k * (gradient (p k) x j + z.1 (k, j)) = 0 := by
    intro j
    have h := hdep j
    simp only [gradient_pert] at h
    have : ∑ k, mu k * (gradient (p k) x j + z.1 (k, j))
        = (∑ k, lam k * (gradient (p k) x j + z.1 (k, j))) / lam i := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by simp [hmudef]; ring
    rw [this, h, zero_div]
  have hA : coverA p S i w = z.1 := by
    funext kj
    obtain ⟨k, j⟩ := kj
    by_cases hk : k = i
    · subst hk
      simp only [coverA, hX, hLam, if_true]
      have hrw : ∀ k' ∈ Finset.univ.erase k,
          mu k' * (gradient (p k') x j + w.1 (k', j))
            = mu k' * (gradient (p k') x j + z.1 (k', j)) := by
        intro k' hk'
        have hne' : k' ≠ k := Finset.ne_of_mem_erase hk'
        rw [hw1 (k', j)]
        simp [hne']
      rw [Finset.sum_congr rfl hrw]
      have h := hdep' j
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hmui, one_mul] at h
      linarith
    · simp [coverA, hk, hw1]
  refine ⟨S, i, w, ?_⟩
  refine Prod.ext hA ?_
  funext k
  by_cases hk : k ∈ insert i S
  · simp only [cover, hX, hA, if_pos hk]
    have hlk : lam k ≠ 0 := by
      rcases Finset.mem_insert.1 hk with rfl | hkS
      · exact hi
      · exact hmuz k ((hmemS k).1 hkS)
    have h := hvanish k hlk
    rw [eval_pert] at h
    linarith
  · have hki : k ≠ i := fun h => hk (by simp [h])
    have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
    simp [cover, hw2, hki, hkS]

/-! ## Part 5: the covering maps are differentiable and degenerate -/

/-- Evaluation of a polynomial is differentiable. -/
@[fun_prop] theorem differentiable_evalPoly (q : MvPolynomial (Fin n) ℝ) :
    Differentiable ℝ (fun x : Fin n → ℝ => eval x q) :=
  fun x => (hasFDerivAt_eval q x).differentiableAt

/-- Reading off a linear coefficient is a continuous linear functional on parameters. -/
noncomputable def prm1 (kj : Fin m × Fin n) : Param m n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj kj).comp (ContinuousLinearMap.fst ℝ (Fin m × Fin n → ℝ) (Fin m → ℝ))

/-- Reading off a constant term is a continuous linear functional on parameters. -/
noncomputable def prm2 (k : Fin m) : Param m n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℝ (Fin m × Fin n → ℝ) (Fin m → ℝ))

/-- Reading off the point `x` is a continuous linear map on parameters. -/
noncomputable def coverXCLM (i : Fin m) : Param m n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun j => prm1 (i, j)

@[fun_prop] theorem differentiable_coverX (i : Fin m) :
    Differentiable ℝ (fun w : Param m n => coverX i w) := (coverXCLM i).differentiable

@[fun_prop] theorem differentiable_gradComp (q : MvPolynomial (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Differentiable ℝ (fun w : Param m n => gradient q (coverX i w) j) :=
  (differentiable_evalPoly (pderiv j q)).comp (differentiable_coverX i)

@[fun_prop] theorem differentiable_coverLam (S : Finset (Fin m)) (i k : Fin m) :
    Differentiable ℝ (fun w : Param m n => coverLam S i w k) := by
  unfold coverLam
  split_ifs
  · exact differentiable_const 1
  · exact (prm2 k).differentiable
  · exact differentiable_const 0

@[fun_prop] theorem differentiable_coverA (p : Fin m → MvPolynomial (Fin n) ℝ) (S : Finset (Fin m))
    (i : Fin m) (kj : Fin m × Fin n) :
    Differentiable ℝ (fun w : Param m n => coverA p S i w kj) := by
  unfold coverA
  split_ifs
  · exact ((differentiable_gradComp (p i) i kj.2).neg).sub
      (Differentiable.fun_sum fun k _ => (differentiable_coverLam S i k).mul
        ((differentiable_gradComp (p k) i kj.2).add (prm1 (k, kj.2)).differentiable))
  · exact (prm1 kj).differentiable

theorem differentiable_cover (p : Fin m → MvPolynomial (Fin n) ℝ) (S : Finset (Fin m))
    (i : Fin m) : Differentiable ℝ (cover p S i) := by
  unfold cover
  refine Differentiable.prodMk ?_ ?_
  · exact differentiable_pi.2 fun kj => differentiable_coverA p S i kj
  · refine differentiable_pi.2 fun k => ?_
    split_ifs
    · exact ((Differentiable.fun_comp (differentiable_evalPoly (p k)) (differentiable_coverX i)).add
        (Differentiable.fun_sum fun j _ => (differentiable_coverA p S i (k, j)).mul
          (differentiable_pi.1 (differentiable_coverX i) j))).fun_neg
    · exact (prm2 k).differentiable

/-! ## Part 6: the image of each covering map is null -/

/-- The continuous linear map on parameters that kills the coordinate `z.2 i`. -/
noncomputable def killCLM (i : Fin m) : Param m n →L[ℝ] Param m n :=
  (ContinuousLinearMap.id ℝ (Fin m × Fin n → ℝ)).prodMap
    (ContinuousLinearMap.id ℝ (Fin m → ℝ) -
      (ContinuousLinearMap.proj i).smulRight (Pi.single i (1 : ℝ)))

@[simp] lemma killCLM_fst (i : Fin m) (w : Param m n) : (killCLM i w).1 = w.1 := rfl

@[simp] lemma killCLM_snd (i : Fin m) (w : Param m n) (k : Fin m) :
    (killCLM i w).2 k = if k = i then 0 else w.2 k := by
  by_cases hk : k = i
  · subst hk; simp [killCLM]
  · simp [killCLM, hk]

/-- The covering map is unchanged by killing the `i`-th constant-term coordinate. -/
theorem cover_kill (p : Fin m → MvPolynomial (Fin n) ℝ) (S : Finset (Fin m)) (i : Fin m)
    (w : Param m n) : cover p S i (killCLM i w) = cover p S i w := by
  have hX : coverX i (killCLM i w) = coverX i w := rfl
  have hLam : coverLam S i (killCLM i w) = coverLam S i w := by
    funext k
    by_cases hk : k = i
    · simp [coverLam, hk]
    · simp [coverLam, hk]
  have hA : coverA p S i (killCLM i w) = coverA p S i w := by
    funext kj
    simp only [coverA, hX, hLam, killCLM_fst]
  refine Prod.ext hA ?_
  funext k
  by_cases hk : k ∈ insert i S
  · simp only [cover, hX, hA, if_pos hk]
  · have hki : k ≠ i := fun h => hk (by simp [h])
    simp only [cover, if_neg hk, killCLM_snd, if_neg hki]

/-- The image of a covering map is a Lebesgue-null subset of the parameter space. -/
theorem measure_range_cover (p : Fin m → MvPolynomial (Fin n) ℝ) (S : Finset (Fin m))
    (i : Fin m) : volume (Set.range (cover p S i)) = 0 := by
  have hdiff := differentiable_cover p S i
  have hker : LinearMap.det
      ((killCLM i : Param m n →L[ℝ] Param m n) : Param m n →ₗ[ℝ] Param m n) = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
    refine ⟨((0 : Fin m × Fin n → ℝ), Pi.single i (1 : ℝ)), ?_, ?_⟩
    · simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      refine Prod.ext rfl ?_
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    · intro h
      have h2 : (Pi.single i (1 : ℝ)) = (0 : Fin m → ℝ) := by
        simpa using congrArg Prod.snd h
      simpa using congrFun h2 i
  have hfd : ∀ w ∈ (Set.univ : Set (Param m n)),
      HasFDerivWithinAt (cover p S i)
        ((fderiv ℝ (cover p S i) (killCLM i w)).comp (killCLM i)) Set.univ w := by
    intro w _
    have h1 : HasFDerivAt (fun v : Param m n => cover p S i (killCLM i v))
        ((fderiv ℝ (cover p S i) (killCLM i w)).comp (killCLM i)) w :=
      ((hdiff (killCLM i w)).hasFDerivAt).comp w (killCLM i).hasFDerivAt
    rw [show (fun v : Param m n => cover p S i (killCLM i v)) = cover p S i from
      funext (cover_kill p S i)] at h1
    exact h1.hasFDerivWithinAt
  have hdet : ∀ w ∈ (Set.univ : Set (Param m n)),
      ((fderiv ℝ (cover p S i) (killCLM i w)).comp (killCLM i)).det = 0 := by
    intro w _
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp, hker, mul_zero]
  have h := MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (volume : Measure (Param m n)) hfd hdet
  simpa [Set.image_univ] using h

/-! ## Part 7: good parameters exist arbitrarily close to zero -/

/-- Non-bad parameters exist in every ball around the origin. -/
theorem exists_not_bad (p : Fin m → MvPolynomial (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Param m n, ‖z‖ < ε ∧ ¬ Bad p z := by
  classical
  set U : Set (Param m n) :=
    ⋃ (Si : Finset (Fin m) × Fin m), Set.range (cover p Si.1 Si.2) with hUdef
  have hU : volume U = 0 := measure_iUnion_null fun Si => measure_range_cover p Si.1 Si.2
  have hball : 0 < volume (Metric.ball (0 : Param m n) ε) := Metric.measure_ball_pos _ _ hε
  have hns : ¬ (Metric.ball (0 : Param m n) ε ⊆ U) := fun hsub =>
    absurd (measure_mono_null hsub hU) (ne_of_gt hball)
  obtain ⟨z, hz, hzU⟩ := Set.not_subset.1 hns
  refine ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz, ?_⟩
  intro hbad
  obtain ⟨S, i, hSi⟩ := bad_mem_range p z hbad
  exact hzU (Set.mem_iUnion.2 ⟨(S, i), hSi⟩)

/-- A small parameter has small entries. -/
theorem entries_lt_of_norm_lt {z : Param m n} {ε : ℝ} (h : ‖z‖ < ε) :
    (∀ kj, |z.1 kj| < ε) ∧ (∀ k, |z.2 k| < ε) := by
  constructor
  · intro kj
    calc |z.1 kj| = ‖z.1 kj‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖z.1‖ := norm_le_pi_norm _ _
      _ ≤ ‖z‖ := le_max_left _ _
      _ < ε := h
  · intro k
    calc |z.2 k| = ‖z.2 k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖z.2‖ := norm_le_pi_norm _ _
      _ ≤ ‖z‖ := le_max_right _ _
      _ < ε := h

/-- The coefficients of the perturbed polynomials are close to the original ones. -/
theorem abs_coeff_pert_sub_lt (p : Fin m → MvPolynomial (Fin n) ℝ) (z : Param m n)
    {ε : ℝ} (hε : 0 < ε) (h1 : ∀ kj, |z.1 kj| < ε) (h2 : ∀ k, |z.2 k| < ε)
    (k : Fin m) (d : Fin n →₀ ℕ) :
    |coeff d (pert p z k) - coeff d (p k)| < ε := by
  classical
  have hcoeff : coeff d (pert p z k) - coeff d (p k)
      = (∑ j, if Finsupp.single j 1 = d then z.1 (k, j) else 0)
        + (if (0 : Fin n →₀ ℕ) = d then z.2 k else 0) := by
    simp [pert, coeff_add, coeff_sum, coeff_C_mul, coeff_X, coeff_C]
    ring
  by_cases hd0 : (0 : Fin n →₀ ℕ) = d
  · have hs : ∀ j : Fin n, (if Finsupp.single j 1 = d then z.1 (k, j) else 0) = 0 := by
      intro j
      refine if_neg fun h => ?_
      exact (Finsupp.single_ne_zero.2 (one_ne_zero)) (h.trans hd0.symm)
    rw [hcoeff, if_pos hd0, Finset.sum_congr rfl (fun j _ => hs j), Finset.sum_const_zero,
      zero_add]
    exact h2 k
  · by_cases hex : ∃ j0 : Fin n, Finsupp.single j0 1 = d
    · obtain ⟨j0, hj0⟩ := hex
      have hs : (∑ j, if Finsupp.single j 1 = d then z.1 (k, j) else 0) = z.1 (k, j0) := by
        rw [Finset.sum_eq_single j0]
        · rw [if_pos hj0]
        · intro j _ hj
          refine if_neg fun h => ?_
          exact hj (Finsupp.single_left_injective one_ne_zero (h.trans hj0.symm))
        · intro h; exact absurd (Finset.mem_univ j0) h
      rw [hcoeff, hs, if_neg hd0, add_zero]
      exact h1 (k, j0)
    · simp only [not_exists] at hex
      have hs : ∀ j : Fin n, (if Finsupp.single j 1 = d then z.1 (k, j) else 0) = 0 :=
        fun j => if_neg (hex j)
      rw [hcoeff, if_neg hd0, Finset.sum_congr rfl (fun j _ => hs j), Finset.sum_const_zero,
        add_zero, abs_zero]
      exact hε

/-! ## Part 8: the main theorem -/

/-- **Algebraic Thom transversality, gradient form.**

Given polynomials `p 1, ..., p m` in `n` real variables and any `ε > 0`, there are
polynomials `q 1, ..., q m` all of whose coefficients are within `ε` of the corresponding
coefficients of `p`, such that for *every* subfamily `S` and every point `x` at which all
the `q k`, `k ∈ S`, vanish, the gradients `∇(q k)(x)`, `k ∈ S`, are linearly independent. -/
theorem transversality (p : Fin m → MvPolynomial (Fin n) ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Fin m → MvPolynomial (Fin n) ℝ,
      (∀ k d, |coeff d (q k) - coeff d (p k)| < ε) ∧
      ∀ (x : Fin n → ℝ) (S : Finset (Fin m)), (∀ k ∈ S, eval x (q k) = 0) →
        LinearIndependent ℝ (fun k : S => gradient (q k) x) := by
  obtain ⟨z, hz, hbad⟩ := exists_not_bad p hε
  obtain ⟨h1, h2⟩ := entries_lt_of_norm_lt hz
  exact ⟨pert p z, fun k d => abs_coeff_pert_sub_lt p z hε h1 h2 k d,
    fun x S hS => linearIndependent_of_not_bad p z hbad x S hS⟩

end AlgebraicTransversality
