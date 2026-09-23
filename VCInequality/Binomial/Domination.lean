import VCInequality.Defs

/-!
# Stochastic domination in `p`

`p ↦ P[Bin(m,p) ≥ k] = binTail m k p` is monotone on `[0,1]`.

Route: instead of differentiating, we use the Pascal recursion for the binomial tail,
`P[Bin(m+1,p) ≥ k+1] = p · P[Bin(m,p) ≥ k] + (1−p) · P[Bin(m,p) ≥ k+1]`
(`binTail_succ_succ`), which follows from `C(m+1,j) = C(m,j−1) + C(m,j)` after reindexing.
Monotonicity then follows by induction on `m`: writing `A = binTail m k q`, `B = binTail m (k+1) q`,
`C = binTail m k p`, `D = binTail m (k+1) p` for `0 ≤ p ≤ q ≤ 1`,

    (q·A + (1−q)·B) − (p·C + (1−p)·D) = (q−p)(A−B) + p(A−C) + (1−p)(B−D) ≥ 0,

where `A − B ≥ 0` is the trivial monotonicity in `k` (`binTail_succ_le`) and the other two
differences are nonnegative by the induction hypothesis.
For `k = 0` the tail is identically `1` (binomial theorem `add_pow`), and for `m = 0`, `k ≥ 1`
the sum is empty.
Also the trivial monotonicity in `k`: more terms, `binTail m (k+1) p ≤ binTail m k p` for
`0 ≤ p ≤ 1`.
-/

open Finset

namespace VCInequality

/-- The full binomial tail is `1` (binomial theorem). -/
private lemma binTail_eq_one (m : ℕ) (p : ℝ) : binTail m 0 p = 1 := by
  have h : Finset.Icc 0 m = Finset.range (m + 1) := by
    ext x; simp
  have h2 : ((p + (1 - p)) : ℝ) ^ m
      = ∑ j ∈ range (m + 1), p ^ j * (1 - p) ^ (m - j) * (m.choose j : ℝ) :=
    add_pow p (1 - p) m
  have h3 : (p + (1 - p) : ℝ) = 1 := by ring
  rw [h3, one_pow] at h2
  unfold binTail binPmf
  rw [h]
  exact Eq.trans (Finset.sum_congr rfl fun j _ => by ring) h2.symm

/-- Dropping the bottom term of the tail decreases it, for `p ∈ [0,1]`. -/
private lemma binTail_anti_k (m k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binTail m (k + 1) p ≤ binTail m k p := by
  unfold binTail binPmf
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl) ?_
  intro i _ _
  have h : (0:ℝ) ≤ 1 - p := by linarith
  positivity

/-- Pascal recursion for the binomial tail:
`P[Bin(m+1,p) ≥ k+1] = p · P[Bin(m,p) ≥ k] + (1−p) · P[Bin(m,p) ≥ k+1]`. -/
private lemma binTail_succ_succ (m k : ℕ) (p : ℝ) :
    binTail (m + 1) (k + 1) p = p * binTail m k p + (1 - p) * binTail m (k + 1) p := by
  by_cases hkm : k ≤ m
  · have hmap : (Icc k m).map (addRightEmbedding 1) = Icc (k + 1) (m + 1) :=
      Finset.map_add_right_Icc k m 1
    have step1 : binTail (m + 1) (k + 1) p
        = (∑ i ∈ Icc k m, (m.choose i : ℝ) * p ^ (i + 1) * (1 - p) ^ (m - i))
          + ∑ i ∈ Icc k m, (m.choose (i + 1) : ℝ) * p ^ (i + 1) * (1 - p) ^ (m - i) := by
      rw [← Finset.sum_add_distrib]
      unfold binTail binPmf
      rw [← hmap, Finset.sum_map]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [addRightEmbedding_apply]
      have he : m + 1 - (i + 1) = m - i := by omega
      rw [he, Nat.choose_succ_succ]
      push_cast
      ring
    have stepA : (∑ i ∈ Icc k m, (m.choose i : ℝ) * p ^ (i + 1) * (1 - p) ^ (m - i))
        = p * binTail m k p := by
      unfold binTail binPmf
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have stepB : (∑ i ∈ Icc k m, (m.choose (i + 1) : ℝ) * p ^ (i + 1) * (1 - p) ^ (m - i))
        = (1 - p) * binTail m (k + 1) p := by
      have h1 : (∑ i ∈ Icc k m, (m.choose (i + 1) : ℝ) * p ^ (i + 1) * (1 - p) ^ (m - i))
          = ∑ j ∈ Icc (k + 1) (m + 1), (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m + 1 - j) := by
        rw [← hmap, Finset.sum_map]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [addRightEmbedding_apply]
        have he : m + 1 - (i + 1) = m - i := by omega
        rw [he]
      have hz : ((m.choose (m + 1) : ℕ) : ℝ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        norm_num
      rw [h1, Finset.sum_Icc_succ_top (show k + 1 ≤ m + 1 by omega), hz]
      simp only [zero_mul, add_zero]
      unfold binTail binPmf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      have he : m + 1 - j = (m - j) + 1 := by omega
      rw [he]
      ring
    rw [step1, stepA, stepB]
  · have e1 : Icc (k + 1) (m + 1) = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    have e2 : Icc k m = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    have e3 : Icc (k + 1) m = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    unfold binTail binPmf
    rw [e1, e2, e3]
    simp

/-- Monotonicity of `p ↦ binTail m k p` on `[0,1]`, in the `∀`-form used by the induction. -/
private lemma binTail_mono_aux (m : ℕ) : ∀ (k : ℕ) (p q : ℝ), 0 ≤ p → p ≤ q → q ≤ 1 →
    binTail m k p ≤ binTail m k q := by
  induction m with
  | zero =>
    intro k p q _ _ _
    cases k with
    | zero => simp [binTail_eq_one]
    | succ k =>
      have he : Icc (k + 1) 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      unfold binTail binPmf
      rw [he]
      simp
  | succ m ih =>
    intro k p q hp hpq hq1
    cases k with
    | zero => simp [binTail_eq_one]
    | succ k =>
      rw [binTail_succ_succ, binTail_succ_succ]
      have hq0 : (0:ℝ) ≤ q := le_trans hp hpq
      have h1 : binTail m (k + 1) q ≤ binTail m k q := binTail_anti_k m k hq0 hq1
      have h2 : binTail m k p ≤ binTail m k q := ih k p q hp hpq hq1
      have h3 : binTail m (k + 1) p ≤ binTail m (k + 1) q := ih (k + 1) p q hp hpq hq1
      nlinarith [mul_nonneg (sub_nonneg.2 hpq) (sub_nonneg.2 h1),
        mul_nonneg hp (sub_nonneg.2 h2),
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (sub_nonneg.2 h3)]

theorem binTail_mono (m k : ℕ) : MonotoneOn (binTail m k) (Set.Icc 0 1) := by
  intro p hp q hq hpq
  exact binTail_mono_aux m k p q hp.1 hpq hq.2

theorem binTail_succ_le (m k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binTail m (k + 1) p ≤ binTail m k p := binTail_anti_k m k hp0 hp1

theorem binTail_zero (m : ℕ) (p : ℝ) : binTail m 0 p = 1 := binTail_eq_one m p

end VCInequality
