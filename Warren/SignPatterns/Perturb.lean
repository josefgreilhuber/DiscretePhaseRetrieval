/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.Transversality
import Warren.BoundedComponents.Perturbation

/-!
# Sign patterns: generic augmentation

Given polynomials `p 1, ..., p m` in `n` real variables of total degree `≤ d` and a finite
set `X` of points at which none of the `p j` vanish, we produce a family of `m + 1`
polynomials `q 0, ..., q m` of total degree `≤ max 2 d` such that

* the family `q` is in general position (transversal) in the sense of
  `AlgebraicTransversality`: at every common zero of a subfamily the gradients are
  linearly independent;
* the sublevel set `{q 0 ≤ 0}` is bounded;
* `q 0` is negative on `X`, and `q (j+1)` has the same sign as `p j` on `X`.

The construction *adds one polynomial* `q₀ = ∑ᵢ xᵢ² − M²` (with `M` large enough that `X`
sits inside the ball of radius `M`) to the list, and then applies the affine perturbation
`AlgebraicTransversality.pert` with a small non-bad parameter `z` given by
`AlgebraicTransversality.exists_not_bad`.
-/

open MvPolynomial Metric Set

namespace SignPatterns

open AlgebraicTransversality

/-! ## The polynomial `∑ xᵢ²` -/

/-- The polynomial `∑ i, X i ^ 2`, the sum of squares of the coordinate functions. -/
noncomputable def sqNorm (n : ℕ) : MvPolynomial (Fin n) ℝ :=
  BoundedComponents.sumSq (X : Fin n → MvPolynomial (Fin n) ℝ)

@[simp] lemma eval_sqNorm {n : ℕ} (x : Fin n → ℝ) : eval x (sqNorm n) = ∑ i, x i ^ 2 := by
  simp [sqNorm, BoundedComponents.eval_sumSq]

/-- The sup norm squared is bounded by the sum of squares. -/
lemma sq_norm_le_sum_sq {n : ℕ} (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  have hsum : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have h : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, x i ^ 2 := Real.sq_sqrt hsum

lemma totalDegree_sqNorm_le (n : ℕ) : (sqNorm n).totalDegree ≤ 2 := by
  simpa [sqNorm] using BoundedComponents.totalDegree_sumSq_le (X : Fin n → MvPolynomial (Fin n) ℝ)
    (fun i => (totalDegree_X i).le)

/-! ## Elementary helpers -/

/-- A finite set of reals is bounded above by a nonnegative constant. -/
theorem exists_bound_of_finite {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ s, f x ≤ A := by
  rcases s.eq_empty_or_nonempty with h | h
  · exact ⟨0, le_rfl, fun x hx => by simp [h] at hx⟩
  · obtain ⟨a, _, ha⟩ := Set.exists_max_image s f hs h
    exact ⟨max 0 (f a), le_max_left _ _, fun x hx => (ha x hx).trans (le_max_right _ _)⟩

/-- A perturbation smaller than `|b|` does not change the sign of `b`. -/
theorem sign_eq_of_abs_sub_lt {a b : ℝ} (h : |a - b| < |b|) :
    SignType.sign a = SignType.sign b := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [abs_of_neg hb, abs_lt] at h
    have ha : a < 0 := by linarith
    rw [sign_neg ha, sign_neg hb]
  · subst hb
    rw [sub_zero, abs_zero] at h
    exact absurd h (not_lt.2 (abs_nonneg a))
  · rw [abs_of_pos hb, abs_lt] at h
    have ha : 0 < a := by linarith
    rw [sign_pos ha, sign_pos hb]

/-- A positive lower bound for `|p j|` on a finite set on which no `p j` vanishes. -/
theorem exists_min_abs_eval {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ)
    {X : Set (Fin n → ℝ)} (hX : X.Finite)
    (hXne : ∀ x ∈ X, ∀ j, eval x (p j) ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ X, ∀ j, μ ≤ |eval x (p j)| := by
  classical
  by_cases hne : (X ×ˢ (Set.univ : Set (Fin m))).Nonempty
  · obtain ⟨⟨x0, j0⟩, hmem, hmin⟩ := Set.exists_min_image _
      (fun xj : (Fin n → ℝ) × Fin m => |eval xj.1 (p xj.2)|) (hX.prod Set.finite_univ) hne
    exact ⟨_, abs_pos.2 (hXne x0 (Set.mem_prod.1 hmem).1 j0),
      fun x hx j => hmin (x, j) (Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩)⟩
  · exact ⟨1, one_pos, fun x hx j =>
      absurd ⟨(x, j), Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩⟩ hne⟩

/-! ## Degree and size of the affine perturbation -/

lemma totalDegree_pert_le {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) (z : Param m n)
    {D : ℕ} (hD : 1 ≤ D) (hp : ∀ k, (p k).totalDegree ≤ D) (k : Fin m) :
    (pert p z k).totalDegree ≤ D := by
  unfold pert
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le (hp k) ?_)) ?_)
  · refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X, zero_add]
    exact hD
  · rw [totalDegree_C]
    exact Nat.zero_le _

/-- The size of the affine perturbation added by `pert`. -/
lemma abs_pert_term_le {n m : ℕ} (z : Param m n) {ε : ℝ} (hε : 0 < ε)
    (hz1 : ∀ kj, |z.1 kj| < ε) (hz2 : ∀ k, |z.2 k| < ε) (k : Fin m) (x : Fin n → ℝ) :
    |(∑ j, z.1 (k, j) * x j) + z.2 k| ≤ ε * (n * ‖x‖ + 1) := by
  have h1 : ∀ j, |z.1 (k, j) * x j| ≤ ε * ‖x‖ := fun j => by
    rw [abs_mul]
    refine mul_le_mul (hz1 (k, j)).le ?_ (abs_nonneg _) hε.le
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm x j
  calc |(∑ j, z.1 (k, j) * x j) + z.2 k| ≤ |∑ j, z.1 (k, j) * x j| + |z.2 k| := abs_add_le _ _
    _ ≤ (∑ j, |z.1 (k, j) * x j|) + ε :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (hz2 k).le
    _ ≤ (∑ _j : Fin n, ε * ‖x‖) + ε := add_le_add (Finset.sum_le_sum fun j _ => h1 j) le_rfl
    _ = ε * (n * ‖x‖ + 1) := by simp; ring

/-! ## The main theorem -/

/-- **Generic augmentation realising a sign pattern.**

Given polynomials `p` of total degree `≤ d` and a finite set `X` on which no `p j` vanishes,
there is a family `q` of `m + 1` polynomials of total degree `≤ max 2 d` which is transversal
(in the sense of `AlgebraicTransversality`), whose zeroth member has bounded sublevel set
`{q 0 ≤ 0}` and is negative on `X`, and whose remaining members have the same signs as the
`p j` on `X`. -/
theorem exists_generic_augmentation {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hdeg : ∀ j, (p j).totalDegree ≤ d)
    (X : Set (Fin n → ℝ)) (hX : X.Finite)
    (hXne : ∀ x ∈ X, ∀ j, MvPolynomial.eval x (p j) ≠ 0) :
    ∃ q : Fin (m + 1) → MvPolynomial (Fin n) ℝ,
      (∀ j, (q j).totalDegree ≤ max 2 d) ∧
      (∀ (x : Fin n → ℝ) (S : Finset (Fin (m + 1))), (∀ j ∈ S, MvPolynomial.eval x (q j) = 0) →
        LinearIndependent ℝ (fun j : S => AlgebraicTransversality.gradient (q j) x)) ∧
      Bornology.IsBounded {x | MvPolynomial.eval x (q 0) ≤ 0} ∧
      (∀ x ∈ X, SignType.sign (MvPolynomial.eval x (q 0)) = -1) ∧
      (∀ x ∈ X, ∀ j, SignType.sign (MvPolynomial.eval x (q j.succ)) =
        SignType.sign (MvPolynomial.eval x (p j))) := by
  classical
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- bounds on `X`
  obtain ⟨A, hA0, hA⟩ := exists_bound_of_finite hX (fun x => ∑ i, x i ^ 2)
  obtain ⟨B, hB0, hB⟩ := exists_bound_of_finite hX (fun x : Fin n → ℝ => ‖x‖)
  obtain ⟨M, hMsq⟩ : ∃ M : ℝ, A + 1 ≤ M ^ 2 := ⟨A + 1, by nlinarith⟩
  -- the extra polynomial `q₀ = ∑ xᵢ² − M²`
  set q₀ : MvPolynomial (Fin n) ℝ := sqNorm n - C (M ^ 2) with hq₀def
  have heq₀ : ∀ x : Fin n → ℝ, eval x q₀ = (∑ i, x i ^ 2) - M ^ 2 := by
    intro x; simp [hq₀def]
  have hq₀X : ∀ x ∈ X, eval x q₀ ≤ -1 := by
    intro x hx
    rw [heq₀]
    have := hA x hx
    linarith
  have hdeg₀ : q₀.totalDegree ≤ 2 := by
    refine (totalDegree_sub _ _).trans (max_le (totalDegree_sqNorm_le n) ?_)
    rw [totalDegree_C]
    exact Nat.zero_le _
  -- the augmented family
  set p' : Fin (m + 1) → MvPolynomial (Fin n) ℝ := Fin.cons q₀ p with hp'def
  have hp'0 : p' 0 = q₀ := by simp [hp'def]
  have hp'succ : ∀ i : Fin m, p' i.succ = p i := by intro i; simp [hp'def]
  have hdegp' : ∀ j, (p' j).totalDegree ≤ max 2 d := by
    intro j
    induction j using Fin.cases with
    | zero => rw [hp'0]; exact hdeg₀.trans (le_max_left _ _)
    | succ i => rw [hp'succ]; exact (hdeg i).trans (le_max_right _ _)
  -- a uniform positive lower bound for `|p' j|` on `X`
  obtain ⟨μ₁, hμ₁, hμ₁X⟩ := exists_min_abs_eval p hX hXne
  set μ : ℝ := min μ₁ 1 with hμdef
  have hμ : 0 < μ := lt_min hμ₁ one_pos
  have hμX : ∀ x ∈ X, ∀ j : Fin (m + 1), μ ≤ |eval x (p' j)| := by
    intro x hx j
    induction j using Fin.cases with
    | zero =>
        rw [hp'0]
        have h := hq₀X x hx
        have h1 : (1 : ℝ) ≤ |eval x q₀| := by
          rw [abs_of_nonpos (by linarith)]; linarith
        exact (min_le_right μ₁ 1).trans h1
    | succ i => rw [hp'succ]; exact (min_le_left _ _).trans (hμ₁X x hx i)
  -- the size of the admissible perturbation
  have hnB : (0 : ℝ) < (n : ℝ) * B + 1 := by positivity
  set ε' : ℝ := μ / (2 * ((n : ℝ) * B + 1)) with hε'def
  have hε' : 0 < ε' := by positivity
  have hε'μ : ε' * ((n : ℝ) * B + 1) = μ / 2 := by
    rw [hε'def]; field_simp
  -- the transversal parameter
  obtain ⟨z, hz, hbad⟩ := exists_not_bad p' hε'
  obtain ⟨hz1, hz2⟩ := entries_lt_of_norm_lt hz
  have hpert := abs_pert_term_le z hε' hz1 hz2
  -- signs are preserved on `X`
  have hsign : ∀ x ∈ X, ∀ j : Fin (m + 1),
      SignType.sign (eval x (pert p' z j)) = SignType.sign (eval x (p' j)) := by
    intro x hx j
    refine sign_eq_of_abs_sub_lt ?_
    rw [eval_pert]
    have hxB : ‖x‖ ≤ B := hB x hx
    have h2 : ε' * ((n : ℝ) * ‖x‖ + 1) ≤ ε' * ((n : ℝ) * B + 1) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hε'.le
    calc |eval x (p' j) + (∑ i, z.1 (j, i) * x i) + z.2 j - eval x (p' j)|
        = |(∑ i, z.1 (j, i) * x i) + z.2 j| := by congr 1; ring
      _ ≤ ε' * ((n : ℝ) * ‖x‖ + 1) := hpert j x
      _ < μ := by rw [hε'μ] at h2; linarith
      _ ≤ |eval x (p' j)| := hμX x hx j
  refine ⟨pert p' z, fun j => totalDegree_pert_le p' z (by omega) hdegp' j,
    fun x S hS => linearIndependent_of_not_bad p' z hbad x S hS, ?_, ?_, ?_⟩
  · -- boundedness of `{q 0 ≤ 0}`
    set c : ℝ := ε' * ((n : ℝ) + 1) with hcdef
    have hc0 : 0 ≤ c := by positivity
    set R : ℝ := max 1 (M ^ 2 + c + 1) with hRdef
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := R)).subset ?_
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    rw [mem_closedBall_zero_iff]
    by_contra hxR
    rw [not_le] at hxR
    have hr1 : (1 : ℝ) ≤ ‖x‖ := (le_max_left _ _).trans hxR.le
    have hr2 : M ^ 2 + c + 1 ≤ ‖x‖ := (le_max_right _ _).trans hxR.le
    have hP := hpert 0 x
    rw [abs_le] at hP
    have hsq : ‖x‖ * ‖x‖ ≤ ∑ i, x i ^ 2 := by
      rw [← pow_two]; exact sq_norm_le_sum_sq x
    have heval : eval x (pert p' z 0)
        = (∑ i, x i ^ 2) - M ^ 2 + ((∑ i, z.1 (0, i) * x i) + z.2 0) := by
      rw [eval_pert, hp'0, heq₀]; ring
    rw [heval] at hx
    have hs1 : ε' * ((n : ℝ) * ‖x‖ + 1) ≤ c * ‖x‖ := by
      rw [hcdef]; nlinarith
    have key : ‖x‖ * (M ^ 2 + c + 1) ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left hr2 (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hr1) (sq_nonneg M)]
  · -- `q 0` is negative on `X`
    intro x hx
    rw [hsign x hx 0, hp'0]
    exact sign_neg (by linarith [hq₀X x hx])
  · -- the remaining signs agree with those of `p`
    intro x hx j
    rw [hsign x hx j.succ, hp'succ]

end SignPatterns
