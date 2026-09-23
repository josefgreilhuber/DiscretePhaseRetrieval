/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Basic

/-!
# Elementary real estimates used in the tail bound

These are the purely real-analytic ingredients of the tail-bound lemma; none of them
mentions the polyanalytic Fock space.
-/

namespace PolyFock

open Finset

noncomputable section

/-- Numeric upper bound for `exp n` (`n : ℕ`); the hypothesis is a `norm_num` goal. -/
lemma exp_nat_le {n : ℕ} {c : ℝ} (h : (2.7182818286 : ℝ) ^ n ≤ c) : Real.exp n ≤ c := by
  rw [← Real.exp_one_pow]
  exact (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n).trans h

/-- Numeric lower bound for `exp n` (`n : ℕ`); the hypothesis is a `norm_num` goal. -/
lemma le_exp_nat {n : ℕ} {c : ℝ} (h : c ≤ (2.7182818283 : ℝ) ^ n) : c ≤ Real.exp n := by
  rw [← Real.exp_one_pow]
  exact h.trans (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n)

/-- The Stirling-type step `m^{2L} t^{m-L} / m! ≤ e^{2L} t^L (e t / m)^{m-2L}`. -/
lemma pow_div_factorial_le (L m : ℕ) (hm : 1 ≤ m) (hLm : 2 * L ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    (m : ℝ) ^ (2 * L) * t ^ (m - L) / m.factorial ≤
      Real.exp (2 * L) * t ^ L * (Real.exp 1 * t / m) ^ (m - 2 * L) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have hexp : ((m : ℝ) ^ m) / m.factorial ≤ Real.exp m :=
    Real.pow_div_factorial_le_exp _ hm0.le m
  set k := m - 2 * L with hkdef
  have hmk : 2 * L + k = m := by omega
  have e1 : (Real.exp 1 : ℝ) ^ k = Real.exp (k : ℝ) := Real.exp_one_pow k
  have e2 : Real.exp (2 * (L : ℝ)) * Real.exp (k : ℝ) = Real.exp (m : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    have h : ((2 * L + k : ℕ) : ℝ) = (m : ℝ) := by rw [hmk]
    push_cast at h
    linarith
  have e3 : t ^ L * t ^ k = t ^ (m - L) := by rw [← pow_add]; congr 1; omega
  have e4 : (m : ℝ) ^ k * (m : ℝ) ^ (2 * L) = (m : ℝ) ^ m := by rw [← pow_add]; congr 1; omega
  have key : Real.exp (2 * L) * t ^ L * (Real.exp 1 * t / (m : ℝ)) ^ k
      = (m : ℝ) ^ (2 * L) * t ^ (m - L) * (Real.exp m / (m : ℝ) ^ m) := by
    calc Real.exp (2 * (L : ℝ)) * t ^ L * (Real.exp 1 * t / (m : ℝ)) ^ k
        = Real.exp (2 * (L : ℝ)) * Real.exp (k : ℝ) * (t ^ L * t ^ k) / (m : ℝ) ^ k := by
          rw [div_pow, mul_pow, e1]; ring
      _ = Real.exp (m : ℝ) * t ^ (m - L) / (m : ℝ) ^ k := by rw [e2, e3]
      _ = (m : ℝ) ^ (2 * L) * t ^ (m - L) * (Real.exp m / (m : ℝ) ^ m) := by
          rw [← e4]
          have : ((m : ℝ) ^ k) ≠ 0 := by positivity
          field_simp
  rw [key]
  have h1 : ((m.factorial : ℝ))⁻¹ ≤ Real.exp m / (m : ℝ) ^ m := by
    have hmm : (0 : ℝ) < (m : ℝ) ^ m := by positivity
    rw [le_div_iff₀ hmm]
    calc ((m.factorial : ℝ))⁻¹ * (m : ℝ) ^ m = (m : ℝ) ^ m / m.factorial := by
          field_simp
      _ ≤ Real.exp m := hexp
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)


/-- `(N/m)^{m-2L} ≤ e^L` for `m ≥ N + 1 - L`. -/
lemma pow_ratio_le (L N m : ℕ) (hLm : 2 * L < m) (hm : N + 1 ≤ m + L) :
    ((N : ℝ) / m) ^ (m - 2 * L) ≤ Real.exp L := by
  have hmpos : 0 < m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hmpos
  rcases le_or_gt (N : ℝ) (m : ℝ) with h | h
  · have h1 : (N : ℝ) / m ≤ 1 := by rw [div_le_one hm0]; exact h
    calc ((N : ℝ) / m) ^ (m - 2 * L) ≤ 1 := pow_le_one₀ (by positivity) h1
      _ ≤ Real.exp L := Real.one_le_exp (by positivity)
  · have hge : (1 : ℝ) ≤ (N : ℝ) / m := by rw [le_div_iff₀ hm0]; linarith
    have step1 : ((N : ℝ) / m) ^ (m - 2 * L) ≤ ((N : ℝ) / m) ^ m :=
      pow_le_pow_right₀ hge (by omega)
    have step2 : ((N : ℝ) / m) ^ m ≤ Real.exp ((N : ℝ) - m) := by
      have hb : (N : ℝ) / m = 1 + ((N : ℝ) - m) / m := by field_simp; ring
      have h2 : (N : ℝ) / m ≤ Real.exp (((N : ℝ) - m) / m) := by
        rw [hb]; linarith [Real.add_one_le_exp (((N : ℝ) - m) / m)]
      calc ((N : ℝ) / m) ^ m ≤ (Real.exp (((N : ℝ) - m) / m)) ^ m :=
            pow_le_pow_left₀ (by positivity) h2 m
        _ = Real.exp ((N : ℝ) - m) := by
            rw [← Real.exp_nat_mul]; congr 1; field_simp
    have step3 : Real.exp ((N : ℝ) - m) ≤ Real.exp (L : ℝ) := by
      apply Real.exp_le_exp.mpr
      have hNle : (N : ℝ) ≤ (m : ℝ) + (L : ℝ) := by exact_mod_cast (by omega : N ≤ m + L)
      linarith
    linarith

/-- The geometric tail `∑_{m ≥ M₀} θ^{m-j}` is summable. -/
lemma summable_geom_tail (M₀ j : ℕ) (hj : j ≤ M₀) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    Summable (fun m : ℕ => if M₀ ≤ m then θ ^ (m - j) else 0) := by
  refine (summable_nat_add_iff M₀).mp ?_
  have hshift : ∀ i : ℕ,
      (if M₀ ≤ i + M₀ then θ ^ (i + M₀ - j) else 0) = θ ^ (M₀ - j) * θ ^ i := by
    intro i
    rw [if_pos (Nat.le_add_left M₀ i), ← pow_add]
    congr 1
    omega
  simp_rw [hshift]
  exact (summable_geometric_of_lt_one hθ0 hθ1).mul_left _

/-- The geometric tail `∑_{m ≥ M₀} θ^{m-j} = θ^{M₀-j}/(1-θ)`. -/
lemma tsum_geom_tail (M₀ j : ℕ) (hj : j ≤ M₀) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∑' m : ℕ, (if M₀ ≤ m then θ ^ (m - j) else 0) = θ ^ (M₀ - j) / (1 - θ) := by
  have hsum := summable_geom_tail M₀ j hj hθ0 hθ1
  have hshift : ∀ i : ℕ,
      (if M₀ ≤ i + M₀ then θ ^ (i + M₀ - j) else 0) = θ ^ (M₀ - j) * θ ^ i := by
    intro i
    rw [if_pos (Nat.le_add_left M₀ i), ← pow_add]
    congr 1
    omega
  have hzero : ∀ i ∈ Finset.range M₀, (if M₀ ≤ i then θ ^ (i - j) else 0) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact if_neg (by omega)
  have := hsum.sum_add_tsum_nat_add M₀
  rw [Finset.sum_congr rfl hzero] at this
  simp only [Finset.sum_const_zero, zero_add] at this
  rw [← this]
  simp_rw [hshift]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1]
  ring

end

end PolyFock
