/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Remez.Pressing
import Remez.Interpolation

/-!
# The Remez inequality

This file proves the classical one-dimensional **Remez inequality**
(Theorem 1.2 in M. I. Ganzburg, *Polynomial inequalities on measurable sets and their
applications*, Constr. Approx. 17 (2001)): for a set `E ⊆ [a, b]` of positive Lebesgue
measure and a real polynomial `P` of degree at most `n`,

  `max_{x ∈ [a, b]} |P(x)| ≤ Tₙ(2(b - a)/|E| - 1) · sup_{x ∈ E} |P(x)|`,

where `Tₙ` is the Chebyshev polynomial of degree `n`.  The main statements are
`Remez.remez_inequality` (with an explicit bound `K` for `|P|` on `E`) and
`Remez.remez_inequality_sSup` (with the supremum).  No measurability of `E` is needed.

We follow B. Bojanov, *Elementary proof of the Remez inequality*, Amer. Math. Monthly 100
(1993), 483–485, with one small change: Bojanov first picks an extremal polynomial for an
interior point; we avoid this compactness argument by applying the endpoint estimate directly
to an affine reparametrisation of `P` (`remez_right_endpoint`, `remez_left_endpoint`).

## Proof outline

1. (`remez_normalized`) Let `E ⊆ [-1, y]`, `|P| ≤ 1` on `E` and `|E| ≥ 2`.  Replace `E` by the
   closed set `M = {t ∈ [-1, y] : |P(t)| ≤ 1} ⊇ E`.  Using the pressing lemma
   `Remez.exists_cdf_eq`, choose `xᵢ ∈ M` with `|M ∩ (-∞, xᵢ]| = ηᵢ + 1`, where
   `ηᵢ = cos(iπ/n)` are the extremal points of `Tₙ`.  Then `xᵢ ≥ ηᵢ` and
   `|xᵢ - xⱼ| ≥ |ηᵢ - ηⱼ|`.  Lagrange interpolation at the nodes `xᵢ` gives
   `|P(y)| ≤ ∑ᵢ ∏_{j≠i} |y - xⱼ|/|xᵢ - xⱼ| ≤ ∑ᵢ ∏_{j≠i} |y - ηⱼ|/|ηᵢ - ηⱼ| = Tₙ(y)`.
2. (`remez_right_endpoint`, `remez_left_endpoint`) Affine rescaling gives the bound at the
   endpoints of an arbitrary interval `[a, b]`.
3. (`remez_of_abs_le_one`) For an interior point `x`, split `E` into `E ∩ [a, x]` and
   `E ∩ [x, b]`; one of the pieces has at least the proportional share of the measure, and the
   endpoint estimate on the corresponding subinterval gives exactly the claimed constant.
4. (`remez_inequality`) Normalise `P` by `K = sup_E |P|`.
-/

open MeasureTheory Set Polynomial Polynomial.Chebyshev

namespace Remez

/-! ### Step 1: the normalized endpoint estimate -/

/-- **Bojanov's endpoint estimate.** If `E ⊆ [-1, y]` has measure at least `2`, and
`|P| ≤ 1` on `E`, then `|P(y)| ≤ Tₙ(y)` for every polynomial `P` of degree at most `n`. -/
theorem remez_normalized {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) {y : ℝ} {E : Set ℝ}
    (hE : E ⊆ Icc (-1) y) (hpE : ∀ t ∈ E, |p.eval t| ≤ 1) (hvol : 2 ≤ volume E) :
    |p.eval y| ≤ (T ℝ n).eval y := by
  set M := Icc (-1) y ∩ {t | |p.eval t| ≤ 1} with hM_def
  have hMc : IsClosed M := isClosed_Icc.inter (isClosed_le p.continuous.abs continuous_const)
  have hEM : E ⊆ M := fun t ht => ⟨hE ht, hpE t ht⟩
  have hM : M ⊆ Icc (-1) y := inter_subset_left
  have hvolM : 2 ≤ volume M := hvol.trans (measure_mono hEM)
  have hne : M.Nonempty := by
    refine nonempty_of_measure_ne_zero (μ := volume) fun h => ?_
    rw [h] at hvolM
    exact absurd hvolM (by simp)
  -- the "pressed" points
  have hpts : ∀ i : ℕ, ∃ x ∈ M, cdf M x = node n i + 1 := by
    intro i
    have h1 := (node_mem_Icc (n := n) (i := i)).1
    have h2 := (node_mem_Icc (n := n) (i := i)).2
    refine exists_cdf_eq hMc hM hne (by linarith) ?_
    calc ENNReal.ofReal (node n i + 1) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by linarith)
      _ = 2 := by norm_num
      _ ≤ volume M := hvolM
  choose x hxM hxc using hpts
  have hxle : ∀ i, x i ≤ y := fun i => (hM (hxM i)).2
  have hxge : ∀ i, node n i ≤ x i := by
    intro i
    have := cdf_le_sub hM (hM (hxM i)).1
    rw [hxc] at this
    linarith
  have hxdiff : ∀ i j, |node n i - node n j| ≤ |x i - x j| := by
    intro i j
    have := abs_cdf_sub_le hM hMc.measurableSet (x i) (x j)
    rwa [hxc, hxc, show node n i + 1 - (node n j + 1) = node n i - node n j by ring] at this
  have hy1 : 1 ≤ y := by
    have := hxge 0
    rw [node_eq_one] at this
    exact this.trans (hxle 0)
  have hinj : Set.InjOn x (Finset.range (n + 1)) := by
    intro i hi j hj hij
    refine (strictAntiOn_node n).injOn hi hj ?_
    have := hxdiff i j
    rw [hij, sub_self, abs_zero] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  have hdeg : p.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  calc |p.eval y|
      ≤ ∑ i ∈ Finset.range (n + 1), |p.eval (x i)| *
          ∏ j ∈ (Finset.range (n + 1)).erase i, (|y - x j| / |x i - x j|) :=
        abs_eval_le_sum _ hinj hdeg y
    _ ≤ ∑ i ∈ Finset.range (n + 1), 1 *
          ∏ j ∈ (Finset.range (n + 1)).erase i, (|y - node n j| / |node n i - node n j|) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul (hxM i).2 ?_ (Finset.prod_nonneg fun j _ => by positivity) zero_le_one
        refine Finset.prod_le_prod (fun j _ => by positivity) fun j hj => ?_
        have hji : j ≠ i := (Finset.mem_erase.1 hj).1
        have hj' : j ∈ Finset.range (n + 1) := (Finset.mem_erase.1 hj).2
        have hnode : node n i ≠ node n j := fun h =>
          hji ((strictAntiOn_node n).injOn hj' hi h.symm)
        refine div_le_div₀ (abs_nonneg _) ?_ (abs_pos.2 (sub_ne_zero.2 hnode)) (hxdiff i j)
        rw [abs_of_nonneg (sub_nonneg.2 (hxle j)),
          abs_of_nonneg (sub_nonneg.2 ((hxge j).trans (hxle j)))]
        linarith [hxge j]
    _ = (T ℝ n).eval y := by
        simp only [one_mul]
        exact (eval_T_eq_sum n hy1).symm

/-! ### Step 2: affine reparametrisation and the endpoint estimates on `[a, b]` -/

lemma natDegree_comp_affine_le (p : ℝ[X]) (α β : ℝ) :
    (p.comp (C α * X + C β)).natDegree ≤ p.natDegree :=
  natDegree_comp_le.trans (mul_le_of_le_one_right (Nat.zero_le _) natDegree_linear_le)

lemma eval_comp_affine (p : ℝ[X]) (α β t : ℝ) :
    (p.comp (C α * X + C β)).eval t = p.eval (α * t + β) := by
  simp [eval_comp]

lemma volume_preimage_affine {α : ℝ} (hα : α ≠ 0) (β : ℝ) (E : Set ℝ) :
    volume ((fun t => α * t + β) ⁻¹' E) = ENNReal.ofReal |α⁻¹| * volume E := by
  have : (fun t => α * t + β) ⁻¹' E = (fun t => α * t) ⁻¹' ((fun s => s + β) ⁻¹' E) := rfl
  rw [this, Real.volume_preimage_mul_left hα, measure_preimage_add_right]

/-- The Remez inequality at the right endpoint of `[a, b]`. -/
theorem remez_right_endpoint {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) {a b : ℝ}
    {E : Set ℝ} (hE : E ⊆ Icc a b) (hpE : ∀ t ∈ E, |p.eval t| ≤ 1) {m : ℝ} (hm : 0 < m)
    (hvol : ENNReal.ofReal m ≤ volume E) :
    |p.eval b| ≤ (T ℝ n).eval (2 * (b - a) / m - 1) := by
  set q := p.comp (C (m / 2) * X + C (m / 2 + a)) with hq_def
  have hq : q.natDegree ≤ n := (natDegree_comp_affine_le _ _ _).trans hp
  have hqeval : ∀ s, q.eval s = p.eval (m / 2 * s + (m / 2 + a)) := fun s =>
    eval_comp_affine p _ _ s
  set E' := (fun s => m / 2 * s + (m / 2 + a)) ⁻¹' E with hE'_def
  have hE' : E' ⊆ Icc (-1) (2 * (b - a) / m - 1) := by
    intro s hs
    have h := hE hs
    simp only [Set.mem_Icc] at h ⊢
    constructor
    · nlinarith [h.1]
    · rw [le_sub_iff_add_le, le_div_iff₀ hm]
      nlinarith [h.2]
  have hpE' : ∀ s ∈ E', |q.eval s| ≤ 1 := fun s hs => by rw [hqeval]; exact hpE _ hs
  have hvol' : 2 ≤ volume E' := by
    rw [hE'_def, volume_preimage_affine (by positivity)]
    calc (2 : ENNReal) = ENNReal.ofReal |(m / 2)⁻¹| * ENNReal.ofReal m := by
          rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity)]
          rw [show (m / 2)⁻¹ * m = 2 by field_simp]
          norm_num
      _ ≤ ENNReal.ofReal |(m / 2)⁻¹| * volume E := by gcongr
  have key := remez_normalized hq hE' hpE' hvol'
  rw [hqeval] at key
  convert key using 3
  field_simp
  ring

/-- The Remez inequality at the left endpoint of `[a, b]`. -/
theorem remez_left_endpoint {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) {a b : ℝ}
    {E : Set ℝ} (hE : E ⊆ Icc a b) (hpE : ∀ t ∈ E, |p.eval t| ≤ 1) {m : ℝ} (hm : 0 < m)
    (hvol : ENNReal.ofReal m ≤ volume E) :
    |p.eval a| ≤ (T ℝ n).eval (2 * (b - a) / m - 1) := by
  set r := p.comp (C (-1) * X + C (a + b)) with hr_def
  have hr : r.natDegree ≤ n := (natDegree_comp_affine_le _ _ _).trans hp
  have hreval : ∀ s, r.eval s = p.eval (-1 * s + (a + b)) := fun s => eval_comp_affine p _ _ s
  set E' := (fun s => -1 * s + (a + b)) ⁻¹' E with hE'_def
  have hE' : E' ⊆ Icc a b := by
    intro s hs
    have h := hE hs
    simp only [Set.mem_Icc] at h ⊢
    constructor <;> linarith
  have hpE' : ∀ s ∈ E', |r.eval s| ≤ 1 := fun s hs => by rw [hreval]; exact hpE _ hs
  have hvol' : ENNReal.ofReal m ≤ volume E' := by
    rw [hE'_def, volume_preimage_affine (by norm_num)]
    simpa using hvol
  have key := remez_right_endpoint hr hE' hpE' hm hvol'
  rw [hreval] at key
  convert key using 3
  ring

/-! ### Step 3: interior points -/

/-- The Remez inequality with `|P| ≤ 1` on `E` and an explicit lower bound `m ≤ |E|`. -/
theorem remez_of_abs_le_one {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) {a b : ℝ} (hab : a < b)
    {E : Set ℝ} (hE : E ⊆ Icc a b) (hpE : ∀ t ∈ E, |p.eval t| ≤ 1) {m : ℝ} (hm : 0 < m)
    (hvol : ENNReal.ofReal m ≤ volume E) {x : ℝ} (hx : x ∈ Icc a b) :
    |p.eval x| ≤ (T ℝ n).eval (2 * (b - a) / m - 1) := by
  set E₁ := E ∩ Icc a x with hE₁_def
  set E₂ := E ∩ Icc x b with hE₂_def
  have hsub : E ⊆ E₁ ∪ E₂ := by
    intro t ht
    by_cases h : t ≤ x
    · exact Or.inl ⟨ht, (hE ht).1, h⟩
    · exact Or.inr ⟨ht, le_of_not_ge h, (hE ht).2⟩
  have hfin : volume E ≠ ⊤ := volume_ne_top_of_subset_Icc hE
  have hfin₁ : volume E₁ ≠ ⊤ := volume_inter_ne_top hE _
  have hfin₂ : volume E₂ ≠ ⊤ := volume_inter_ne_top hE _
  set v := (volume E).toReal with hv_def
  set v₁ := (volume E₁).toReal with hv₁_def
  set v₂ := (volume E₂).toReal with hv₂_def
  have hsum : v ≤ v₁ + v₂ := by
    have := (measure_mono (μ := volume) hsub).trans (measure_union_le E₁ E₂)
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin₁, hfin₂⟩) this
    rwa [ENNReal.toReal_add hfin₁ hfin₂] at this
  have hmv : m ≤ v := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hvol
  have hv₁ : v₁ ≤ v := ENNReal.toReal_mono hfin (measure_mono inter_subset_left)
  have hab' : 0 < b - a := sub_pos.2 hab
  have key : (a < x ∧ m * (x - a) / (b - a) ≤ v₁) ∨ (x < b ∧ m * (b - x) / (b - a) ≤ v₂) := by
    by_cases hxa : x = a
    · right
      subst hxa
      refine ⟨hab, ?_⟩
      have h1 : v₁ = 0 := by
        have : E₁ ⊆ {x} := fun t ht => mem_singleton_iff.2 (le_antisymm ht.2.2 ht.2.1)
        simp [hv₁_def, measure_mono_null this Real.volume_singleton]
      rw [mul_div_assoc, div_self hab'.ne', mul_one]
      linarith
    · have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
      by_cases hxb : x = b
      · left
        subst hxb
        refine ⟨hax, ?_⟩
        have h1 : v₁ = v := by
          have : E₁ = E := inter_eq_left.2 hE
          rw [hv₁_def, this]
        rw [mul_div_assoc, div_self hab'.ne', mul_one]
        linarith
      · have hxb' : x < b := lt_of_le_of_ne hx.2 hxb
        by_contra h
        rw [not_or, not_and, not_and] at h
        have h1 := not_le.1 (h.1 hax)
        have h2 := not_le.1 (h.2 hxb')
        have : m * (x - a) / (b - a) + m * (b - x) / (b - a) = m := by
          field_simp
          ring
        linarith
  rcases key with ⟨hax, h₁⟩ | ⟨hxb, h₂⟩
  · have hm₁ : 0 < m * (x - a) / (b - a) := by positivity
    have hvol₁ : ENNReal.ofReal (m * (x - a) / (b - a)) ≤ volume E₁ :=
      (ENNReal.ofReal_le_iff_le_toReal hfin₁).2 h₁
    have key := remez_right_endpoint hp (E := E₁) inter_subset_right
      (fun t ht => hpE t ht.1) hm₁ hvol₁
    convert key using 3
    have hxa : x - a ≠ 0 := (sub_pos.2 hax).ne'
    field_simp
  · have hm₂ : 0 < m * (b - x) / (b - a) := by positivity
    have hvol₂ : ENNReal.ofReal (m * (b - x) / (b - a)) ≤ volume E₂ :=
      (ENNReal.ofReal_le_iff_le_toReal hfin₂).2 h₂
    have key := remez_left_endpoint hp (E := E₂) inter_subset_right
      (fun t ht => hpE t ht.1) hm₂ hvol₂
    convert key using 3
    have hbx : b - x ≠ 0 := (sub_pos.2 hxb).ne'
    field_simp

/-- The Remez inequality with an explicit bound `K` on `E` and an explicit lower bound
`m ≤ |E|`: `|P(x)| ≤ Tₙ(2(b - a)/m - 1) · K` for `x ∈ [a, b]`. -/
theorem remez_of_abs_le {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) {a b : ℝ} (hab : a < b)
    {E : Set ℝ} (hE : E ⊆ Icc a b) {K : ℝ} (hpE : ∀ t ∈ E, |p.eval t| ≤ K) {m : ℝ} (hm : 0 < m)
    (hvol : ENNReal.ofReal m ≤ volume E) {x : ℝ} (hx : x ∈ Icc a b) :
    |p.eval x| ≤ (T ℝ n).eval (2 * (b - a) / m - 1) * K := by
  have hvol0 : volume E ≠ 0 := by
    intro h
    rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hvol
    exact absurd hvol (not_le.2 hm)
  have hne : E.Nonempty := nonempty_of_measure_ne_zero hvol0
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hpE _ hne.some_mem)
  rcases hK0.eq_or_lt with rfl | hK
  · have hEinf : E.Infinite := fun hfin' => hvol0 (hfin'.measure_zero volume)
    have hroot : E ⊆ {t | p.IsRoot t} := fun t ht => abs_nonpos_iff.1 (hpE t ht)
    have hp0 : p = 0 := eq_zero_of_infinite_isRoot p (hEinf.mono hroot)
    simp [hp0]
  · set q := C K⁻¹ * p with hq_def
    have hq : q.natDegree ≤ n := (natDegree_C_mul_le _ _).trans hp
    have hqeval : ∀ t, q.eval t = K⁻¹ * p.eval t := fun t => by simp [hq_def]
    have hqE : ∀ t ∈ E, |q.eval t| ≤ 1 := by
      intro t ht
      rw [hqeval, abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK, mul_one]
      exact hpE t ht
    have key := remez_of_abs_le_one hq hab hE hqE hm hvol hx
    rw [hqeval, abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK] at key
    linarith

/-! ### Step 4: the Remez inequality -/

/-- **The Remez inequality** (Ganzburg, Theorem 1.2).  Let `E ⊆ [a, b]` be a set of positive
Lebesgue measure and `P` a real polynomial of degree at most `n` with `|P| ≤ K` on `E`.
Then for every `x ∈ [a, b]`,
`|P(x)| ≤ Tₙ(2(b - a)/|E| - 1) · K`, where `Tₙ` is the Chebyshev polynomial of degree `n`. -/
theorem remez_inequality {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) {a b : ℝ} (hab : a < b)
    {E : Set ℝ} (hE : E ⊆ Icc a b) (hvol : 0 < volume E) {K : ℝ}
    (hpE : ∀ t ∈ E, |p.eval t| ≤ K) {x : ℝ} (hx : x ∈ Icc a b) :
    |p.eval x| ≤ (T ℝ n).eval (2 * (b - a) / (volume E).toReal - 1) * K := by
  have hfin : volume E ≠ ⊤ := volume_ne_top_of_subset_Icc hE
  have hne : E.Nonempty := nonempty_of_measure_ne_zero hvol.ne'
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hpE _ hne.some_mem)
  rcases hK0.eq_or_lt with rfl | hK
  · -- `p` vanishes on the infinite set `E`, hence `p = 0`
    have hEinf : E.Infinite := fun hfin' => by
      have := hfin'.measure_zero volume
      exact hvol.ne' this
    have hroot : E ⊆ {t | p.IsRoot t} := fun t ht =>
      abs_nonpos_iff.1 (hpE t ht)
    have hp0 : p = 0 := eq_zero_of_infinite_isRoot p (hEinf.mono hroot)
    simp [hp0]
  · set q := C K⁻¹ * p with hq_def
    have hq : q.natDegree ≤ n := (natDegree_C_mul_le _ _).trans hp
    have hqeval : ∀ t, q.eval t = K⁻¹ * p.eval t := fun t => by simp [hq_def]
    have hqE : ∀ t ∈ E, |q.eval t| ≤ 1 := by
      intro t ht
      rw [hqeval, abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK, mul_one]
      exact hpE t ht
    have hm : 0 < (volume E).toReal := ENNReal.toReal_pos hvol.ne' hfin
    have hvol' : ENNReal.ofReal (volume E).toReal ≤ volume E := by
      rw [ENNReal.ofReal_toReal hfin]
    have key := remez_of_abs_le_one hq hab hE hqE hm hvol' hx
    rw [hqeval, abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK] at key
    linarith

/-- **The Remez inequality**, supremum form: for `E ⊆ [a, b]` of positive measure and `P` of
degree at most `n`, `|P(x)| ≤ Tₙ(2(b - a)/|E| - 1) · sup_{t ∈ E} |P(t)|` for all `x ∈ [a, b]`. -/
theorem remez_inequality_sSup {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) {a b : ℝ} (hab : a < b)
    {E : Set ℝ} (hE : E ⊆ Icc a b) (hvol : 0 < volume E) {x : ℝ} (hx : x ∈ Icc a b) :
    |p.eval x| ≤ (T ℝ n).eval (2 * (b - a) / (volume E).toReal - 1) *
      sSup ((fun t => |p.eval t|) '' E) := by
  have hbdd : BddAbove ((fun t => |p.eval t|) '' E) :=
    (isCompact_Icc.bddAbove_image p.continuous.abs.continuousOn).mono (Set.image_mono hE)
  exact remez_inequality hp hab hE hvol (fun t ht => le_csSup hbdd (mem_image_of_mem _ ht)) hx

end Remez
