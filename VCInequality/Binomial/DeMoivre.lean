import VCInequality.Defs
import VCInequality.Binomial.Domination

/-!
# A Cauchy–Schwarz / De Moivre lower bound for the upper tail at an integer mean

For `Y ~ Bin(m, k/m)` with `1 ≤ k < m`:

    P[Y ≥ k+1] ≥ (k (m−k) / m) · P[Y = k]².

Proof. Let `P_j = C(m,j) p^j q^{m−j}`, `p = k/m`, `q = 1 − p`, `μ = mp = k`.
1. (De Moivre) `E (Y − k)₊ = ∑_{j ≥ k+1} (j − k) P_j = m p q · P[Bin(m−1,p) = k]`,
   which equals `(k(m−k)/m) · P_k`.
   We prove the equivalent telescoping form `∑_{j ≥ r} (j − mp) P_j = r q P_r` (valid for every
   `r ≤ m+1`) by downward induction, using only the one-step recursion
   `(j+1) q P_{j+1} = (m−j) p P_j`; at `r = k+1` it gives `∑_{j≥k+1} (j−k) P_j = (m−k) p P_k`.
2. (Second moment) The same recursion gives, again by downward induction,
   `∑_{j ≥ r} (j − mp)² P_j = (r − 1 − mp + q) · r q P_r + q (mp) ∑_{j ≥ r} P_j`.
   At `r = k+1` (where `mp = k`) this reads
   `∑_{j≥k+1} (j−k)² P_j = q · ∑_{j≥k+1} (j−k) P_j + q k · P[Y ≥ k+1]`,
   the tail form of `Var Y = m p q`.
3. (Cauchy–Schwarz on the finite sum)
   `(∑_{j≥k+1} (j−k) P_j)² ≤ (∑_{j≥k+1} (j−k)² P_j)(∑_{j≥k+1} P_j)`
   (`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`). Writing `c = (m−k) p = k q`, `u = P_k`,
   `T = P[Y ≥ k+1]`, steps 1–3 give `(c u)² ≤ (q (c u) + c T) T = c T (q u + T) ≤ c T`, because
   `q u + T ≤ u + T ≤ 1` (the events `{Y = k}` and `{Y ≥ k+1}` are disjoint; the total mass is
   `(p + q)^m = 1` by the binomial theorem). Dividing by `c > 0` yields `c u² ≤ T`.
-/

open Finset

namespace VCInequality

/-- Peel off the bottom term of a sum over `Finset.Icc`. -/
private lemma sum_Icc_split {m r : ℕ} (h : r ≤ m) (f : ℕ → ℝ) :
    ∑ j ∈ Icc r m, f j = f r + ∑ j ∈ Icc (r + 1) m, f j := by
  have hset : Icc r m = insert r (Icc (r + 1) m) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hset, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]

/-- The one-step recursion `(j+1) q P_{j+1} = (m−j) p P_j` for the binomial pmf. -/
private lemma binPmf_succ_ratio (m : ℕ) (p : ℝ) {j : ℕ} (hj : j ≤ m) :
    ((j : ℝ) + 1) * (1 - p) * binPmf m p (j + 1) = ((m : ℝ) - j) * p * binPmf m p j := by
  rcases eq_or_lt_of_le hj with rfl | hlt
  · simp [binPmf]
  · have hc : (m.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = (m.choose j : ℝ) * ((m : ℝ) - j) := by
      have h := Nat.choose_succ_right_eq m j
      have h2 : ((m - j : ℕ) : ℝ) = (m : ℝ) - j := by rw [Nat.cast_sub hlt.le]
      calc (m.choose (j + 1) : ℝ) * ((j : ℝ) + 1)
          = ((m.choose (j + 1) * (j + 1) : ℕ) : ℝ) := by push_cast; ring
        _ = ((m.choose j * (m - j) : ℕ) : ℝ) := by rw [h]
        _ = (m.choose j : ℝ) * ((m : ℝ) - j) := by push_cast [h2]; ring
    have hpow : (1 - p) ^ (m - j) = (1 - p) * (1 - p) ^ (m - (j + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    unfold binPmf
    rw [hpow]
    linear_combination ((1 - p) * p ^ (j + 1) * (1 - p) ^ (m - (j + 1))) * hc

/-- De Moivre's telescoping identity `∑_{j ≥ r} (j − mp) P_j = r q P_r`, proved by downward
induction (`r + i = m + 1`). -/
private lemma sum_centered (m : ℕ) (p : ℝ) :
    ∀ i r : ℕ, r + i = m + 1 →
      ∑ j ∈ Icc r m, ((j : ℝ) - m * p) * binPmf m p j = r * (1 - p) * binPmf m p r := by
  intro i
  induction i with
  | zero =>
    intro r hr
    have hrm : r = m + 1 := by omega
    subst hrm
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    simp [binPmf]
  | succ i ih =>
    intro r hr
    have hrm : r ≤ m := by omega
    have h1 : r + 1 + i = m + 1 := by omega
    rw [sum_Icc_split hrm (fun j => ((j : ℝ) - m * p) * binPmf m p j), ih (r + 1) h1]
    have hratio := binPmf_succ_ratio m p hrm
    push_cast
    linear_combination hratio

/-- Second-moment companion of `sum_centered`:
`∑_{j ≥ r} (j − mp)² P_j = (r − 1 − mp + q) · r q P_r + q (mp) ∑_{j ≥ r} P_j`. -/
private lemma sum_centered_sq (m : ℕ) (p : ℝ) :
    ∀ i r : ℕ, r + i = m + 1 →
      ∑ j ∈ Icc r m, ((j : ℝ) - m * p) ^ 2 * binPmf m p j
        = ((r : ℝ) - 1 - m * p + (1 - p)) * ((r : ℝ) * (1 - p) * binPmf m p r)
          + (1 - p) * (m * p) * ∑ j ∈ Icc r m, binPmf m p j := by
  intro i
  induction i with
  | zero =>
    intro r hr
    have hrm : r = m + 1 := by omega
    subst hrm
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    simp [binPmf]
  | succ i ih =>
    intro r hr
    have hrm : r ≤ m := by omega
    have h1 : r + 1 + i = m + 1 := by omega
    rw [sum_Icc_split hrm (fun j => ((j : ℝ) - m * p) ^ 2 * binPmf m p j),
      sum_Icc_split hrm (fun j => binPmf m p j), ih (r + 1) h1]
    have hratio := binPmf_succ_ratio m p hrm
    push_cast
    linear_combination ((r : ℝ) - m * p + (1 - p)) * hratio

/-- Total mass: `∑_{j ≤ m} P_j = (p + (1−p))^m = 1`; this is the full binomial tail. -/
private lemma sum_binPmf_eq_one (m : ℕ) (p : ℝ) : ∑ j ∈ Icc 0 m, binPmf m p j = 1 :=
  binTail_zero m p

/-- `P[Y ≥ k+1] + P[Y = k] ≤ 1`. -/
private lemma tail_add_le_one {m k : ℕ} (hkm : k ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ j ∈ Icc (k + 1) m, binPmf m p j) + binPmf m p k ≤ 1 := by
  have h1 : (∑ j ∈ Icc (k + 1) m, binPmf m p j) + binPmf m p k
      = ∑ j ∈ Icc k m, binPmf m p j := by
    rw [sum_Icc_split hkm (fun j => binPmf m p j)]; ring
  rw [h1, ← sum_binPmf_eq_one m p]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx; simp only [Finset.mem_Icc] at *; omega
  · intro i _ _; exact binPmf_nonneg hp0 hp1 m i

/-- The final elementary step: from `(cu)² ≤ (q(cu) + cT)T`, `q ≤ 1` and `T + u ≤ 1` deduce
`c u² ≤ T`. -/
private lemma final_step {c q u T : ℝ} (hc : 0 < c) (_hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hu : 0 ≤ u) (hT : 0 ≤ T) (hle : T + u ≤ 1)
    (hCS : (c * u) ^ 2 ≤ (q * (c * u) + c * T) * T) : c * u ^ 2 ≤ T := by
  have h1 : q * u + T ≤ 1 := by nlinarith
  have h2 : (q * (c * u) + c * T) * T ≤ c * T := by
    nlinarith [mul_nonneg (mul_nonneg hc.le hT) (by linarith : (0:ℝ) ≤ 1 - (q * u + T))]
  have h3 : c * (c * u ^ 2) ≤ c * T := by
    calc c * (c * u ^ 2) = (c * u) ^ 2 := by ring
      _ ≤ (q * (c * u) + c * T) * T := hCS
      _ ≤ c * T := h2
  exact le_of_mul_le_mul_left h3 hc

/-- `P[Bin(m,k/m) ≥ k+1] ≥ (k(m−k)/m) · P[Bin(m,k/m) = k]²` for `1 ≤ k < m`. -/
theorem binTail_succ_ge_sq (m k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    (k * (m - k) / m : ℝ) * ((m.choose k : ℝ) * (k / m) ^ k * (1 - k / m) ^ (m - k)) ^ 2
      ≤ binTail m (k + 1) (k / m) := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le k) hkm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkmR : (k : ℝ) < m := by exact_mod_cast hkm
  set p : ℝ := (k : ℝ) / m with hpdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hp1 : p < 1 := by rw [hpdef, div_lt_one hmR]; exact hkmR
  have hmp : (m : ℝ) * p = k := by rw [hpdef]; field_simp
  have hcg : (k : ℝ) * ((m : ℝ) - k) / m = ((m : ℝ) - k) * p := by rw [hpdef]; ring
  have hqk : (1 - p) * (k : ℝ) = ((m : ℝ) - k) * p := by rw [hpdef]; field_simp
  have hratio := binPmf_succ_ratio m p hkm.le
  have hgoal : binTail m (k + 1) p = ∑ j ∈ Icc (k + 1) m, binPmf m p j := rfl
  have hu' : ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) = binPmf m p k := rfl
  rw [hgoal, hu', hcg]
  -- First moment: `∑_{j ≥ k+1} (j − k) P_j = (m−k) p P_k`.
  have hS1 : ∑ j ∈ Icc (k + 1) m, ((j : ℝ) - k) * binPmf m p j
      = ((m : ℝ) - k) * p * binPmf m p k := by
    have h := sum_centered m p (m - k) (k + 1) (by omega)
    rw [hmp] at h
    rw [h]; push_cast; linear_combination hratio
  -- Second moment: `∑_{j ≥ k+1} (j − k)² P_j = q (m−k) p P_k + (m−k) p · T`.
  have hS2 : ∑ j ∈ Icc (k + 1) m, ((j : ℝ) - k) ^ 2 * binPmf m p j
      = (1 - p) * (((m : ℝ) - k) * p * binPmf m p k)
        + ((m : ℝ) - k) * p * ∑ j ∈ Icc (k + 1) m, binPmf m p j := by
    have h := sum_centered_sq m p (m - k) (k + 1) (by omega)
    rw [hmp] at h
    rw [h]; push_cast
    linear_combination (1 - p) * hratio + (∑ j ∈ Icc (k + 1) m, binPmf m p j) * hqk
  -- Cauchy–Schwarz.
  have hCS : (∑ j ∈ Icc (k + 1) m, ((j : ℝ) - k) * binPmf m p j) ^ 2
      ≤ (∑ j ∈ Icc (k + 1) m, ((j : ℝ) - k) ^ 2 * binPmf m p j)
        * (∑ j ∈ Icc (k + 1) m, binPmf m p j) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun i _ => mul_nonneg (sq_nonneg _) (binPmf_nonneg hp0.le hp1.le m i))
      (fun i _ => binPmf_nonneg hp0.le hp1.le m i) (fun i _ => le_of_eq (by ring))
  rw [hS1, hS2] at hCS
  refine final_step (c := ((m : ℝ) - k) * p) (q := 1 - p) ?_ (by linarith) (by linarith)
    (binPmf_nonneg hp0.le hp1.le m k)
    (Finset.sum_nonneg fun i _ => binPmf_nonneg hp0.le hp1.le m i)
    (tail_add_le_one hkm.le hp0.le hp1.le) hCS
  have hmk : (0:ℝ) < (m : ℝ) - k := by linarith
  positivity

end VCInequality
