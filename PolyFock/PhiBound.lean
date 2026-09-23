/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Estimates

/-!
# Pointwise bounds on the complex Hermite functions `φ_{m,n}`

Here `φ_{m,n}` is the comparator's `DiscretePR.HermitePoly m n` of `Definitions.lean`.

Every pointwise estimate of the development runs through the same argument, isolated here as
the core lemma `PolyFock.norm_phi_le_of_term_le`: after the termwise triangle inequality
`norm_phi_le_sum`, if each of the `min m n + 1` terms of the defining sum is bounded by `T`
and `min m n ≤ N`, then

`‖φ_{m,n}(z, z̄)‖ ≤ (N+1) · T · (√(m!))⁻¹`

(the factor `(√(n!))⁻¹ ≤ 1` is thrown away).  `PolyFock.sq_norm_phi_le_of_norm_le` performs the
squaring bookkeeping for such a bound.  There are three instances, differing only in the choice
of the term bound `T`:

* `PolyFock.norm_phi_le` / `PolyFock.sq_norm_phi_le` (below): for `n ≤ L ≤ m` and `‖z‖² ≤ m`,
  `T = 2^L (m^L ‖z‖^{m-L})`, giving
  `‖φ_{m,n}(z, z̄)‖² ≤ ((L+1) 2^L)² · m^{2L} · (‖z‖²)^{m-L} / m!`;
* `DiscretePR.sq_norm_phi_le_gen` (`DiscretePhaseRetrieval/KernelBound.lean`): no hypothesis on
  `‖z‖`, with `T = m^n 2^n (‖z‖^{m-n} (1 + (‖z‖²)^n))`;
* `DiscretePR.sq_norm_phi_le_mid` (ibid.): the crude bound for the finitely many `m ≤ 4n`,
  with `T = (4n)! 2^{4n} 2^n (1 + ‖z‖)^{5n}`.

The first two of these also share the way `T` is reached: `PolyFock.phi_term_le` bounds the
`r`-th term by `a · b · (‖z‖^{m-n} (‖z‖²)^{n-r})` using `r! C(m,r) ≤ m^r`
(`Nat.descFactorial_le_pow`), `C(n,r) ≤ 2^n` and the splitting
`‖z‖^{m-r} ‖z‖^{n-r} = ‖z‖^{m-n} (‖z‖²)^{n-r}`.

This replaces the Cauchy-estimate argument of the paper by a direct estimate of the
defining finite sum; the point is that for `‖z‖² ≤ m` the sum is dominated by its
leading behaviour `m^n ‖z‖^{m-n} / √(m!)`.
-/

namespace PolyFock

open Finset
open DiscretePR (HermitePoly)

noncomputable section

/-- `φ_{m,n}(0,0) = (-1)^m` if `m = n`, and `0` otherwise. -/
lemma phi_zero (m n : ℕ) : HermitePoly m n 0 = if m = n then (-1) ^ m else 0 := by
  rw [HermitePoly]
  simp only [RCLike.star_def]
  by_cases h : m = n
  · subst h
    rw [if_pos rfl]
    have hsum : ∑ r ∈ range (min m m + 1),
        (-1 : ℂ) ^ r * (r.factorial : ℂ) * (m.choose r : ℂ) * (m.choose r : ℂ) *
          (0 : ℂ) ^ (m - r) * (starRingEnd ℂ 0) ^ (m - r)
        = (-1 : ℂ) ^ m * (m.factorial : ℂ) := by
      rw [Finset.sum_eq_single m]
      · simp
      · intro r hr hrne
        rw [Finset.mem_range, Nat.lt_succ_iff, min_self] at hr
        have h1 : m - r ≠ 0 := by omega
        simp [zero_pow h1]
      · intro hmem
        exact absurd (Finset.mem_range.mpr (by simp)) hmem
    have hfac : Real.sqrt ((m.factorial : ℝ) * (m.factorial : ℝ)) = (m.factorial : ℝ) :=
      Real.sqrt_mul_self (by positivity)
    have hc : ((m.factorial : ℝ) : ℂ) = (m.factorial : ℂ) := by push_cast; ring
    have hne : (m.factorial : ℂ) ≠ 0 := by
      simp [Nat.factorial_ne_zero]
    rw [hsum, hfac, hc]
    field_simp
  · rw [if_neg h]
    convert mul_zero _
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff, le_min_iff] at hr
    have key : m - r ≠ 0 ∨ n - r ≠ 0 := by omega
    rcases key with h1 | h1
    · simp [zero_pow h1]
    · simp [zero_pow h1]

lemma phi_zero_of_ne {m n : ℕ} (h : m ≠ n) : HermitePoly m n 0 = 0 := by
  rw [phi_zero, if_neg h]

/-- Termwise triangle inequality for the defining sum of `φ_{m,n}`. -/
lemma norm_phi_le_sum (m n : ℕ) (z : ℂ) :
    ‖HermitePoly m n z‖ ≤ (Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)))⁻¹ *
      ∑ r ∈ range (min m n + 1),
        (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) *
          ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r) := by
  rw [HermitePoly, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  refine (norm_sum_le _ _).trans_eq ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
    norm_star]

/-- The shared termwise step, for `r ≤ n ≤ m`: the `r`-th term of the defining sum of `φ_{m,n}`
factors as `(m)_r · C(n,r) · (‖z‖^{m-n} · (‖z‖²)^{n-r})`, where `(m)_r = r! C(m,r) ≤ m^r` is the
descending factorial.  Bounding the three factors separately by `a`, `b`, `c` gives the term
bounds of `norm_phi_le` (`a = m^r`, `b = 2^L`, `c = m^{n-r}`) and of
`DiscretePR.sq_norm_phi_le_gen` (`a = m^n`, `b = 2^n`, `c = 1 + (‖z‖²)^n`). -/
lemma phi_term_le {m n r : ℕ} {a b c : ℝ} {z : ℂ} (hnm : n ≤ m) (hr : r ≤ n)
    (ha : (m : ℝ) ^ r ≤ a) (hb : (n.choose r : ℝ) ≤ b) (hc : (‖z‖ ^ 2) ^ (n - r) ≤ c)
    (hb0 : 0 ≤ b) :
    (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) * ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r)
      ≤ a * b * (‖z‖ ^ (m - n) * c) := by
  have ha0 : (0 : ℝ) ≤ a := le_trans (by positivity) ha
  have hdesc : ((m.descFactorial r : ℕ) : ℝ) = (r.factorial : ℝ) * (m.choose r : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  have hdle : ((m.descFactorial r : ℕ) : ℝ) ≤ (m : ℝ) ^ r := by
    exact_mod_cast Nat.descFactorial_le_pow m r
  have hxx : ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r) = ‖z‖ ^ (m - n) * (‖z‖ ^ 2) ^ (n - r) := by
    rw [show m - r = (m - n) + (n - r) from by omega, pow_add, sq, mul_pow]
    ring
  calc (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) * ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r)
      = (((m.descFactorial r : ℕ) : ℝ) * (n.choose r : ℝ)) *
          (‖z‖ ^ (m - n) * (‖z‖ ^ 2) ^ (n - r)) := by rw [hdesc, ← hxx]; ring
    _ ≤ a * b * (‖z‖ ^ (m - n) * c) :=
        mul_le_mul (mul_le_mul (hdle.trans ha) hb (by positivity) ha0)
          (mul_le_mul_of_nonneg_left hc (by positivity)) (by positivity) (by positivity)

/-- **The core pointwise estimate.**  If every term of the defining sum of `φ_{m,n}` is bounded
by `T` and the number `min m n + 1` of terms is at most `N + 1`, then

`‖φ_{m,n}(z, z̄)‖ ≤ (N+1) · T · (√(m!))⁻¹`.

Only `norm_phi_le_sum` and the (wasteful, but harmless) estimate `(√(n!))⁻¹ ≤ 1` enter.  All the
pointwise bounds of the development are instances; they differ only in the term bound `T`. -/
lemma norm_phi_le_of_term_le {m n N : ℕ} {T : ℝ} {z : ℂ} (hT : 0 ≤ T) (hN : min m n ≤ N)
    (hterm : ∀ r ≤ min m n, (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) *
      ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r) ≤ T) :
    ‖HermitePoly m n z‖ ≤ ((N : ℝ) + 1) * T * (Real.sqrt (m.factorial : ℝ))⁻¹ := by
  have hfacpos : (0 : ℝ) < Real.sqrt (m.factorial : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos m)
  have hinv : (Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)))⁻¹
      ≤ (Real.sqrt (m.factorial : ℝ))⁻¹ := by
    refine inv_anti₀ hfacpos (Real.sqrt_le_sqrt ?_)
    have hn1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have hm0 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    nlinarith
  have hsum : ∑ r ∈ range (min m n + 1),
      (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) * ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r)
      ≤ ((N : ℝ) + 1) * T := by
    calc ∑ r ∈ range (min m n + 1),
          (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) * ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r)
        ≤ ∑ _r ∈ range (min m n + 1), T :=
          Finset.sum_le_sum fun r hr => hterm r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      _ = ((min m n : ℕ) : ℝ) * T + T := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ ((N : ℝ) + 1) * T := by
          have hmn : ((min m n : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          nlinarith
  calc ‖HermitePoly m n z‖
      ≤ (Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)))⁻¹ *
          ∑ r ∈ range (min m n + 1),
            (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) *
              ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r) := norm_phi_le_sum m n z
    _ ≤ (Real.sqrt (m.factorial : ℝ))⁻¹ * (((N : ℝ) + 1) * T) :=
        mul_le_mul hinv hsum (Finset.sum_nonneg fun r _ => by positivity) (by positivity)
    _ = ((N : ℝ) + 1) * T * (Real.sqrt (m.factorial : ℝ))⁻¹ := by ring

/-- The squaring bookkeeping shared by the squared forms of the core estimate:
`‖φ_{m,n}(z, z̄)‖ ≤ A · (√(m!))⁻¹` gives `‖φ_{m,n}(z, z̄)‖² ≤ A²/m!`. -/
lemma sq_norm_phi_le_of_norm_le {m n : ℕ} {A : ℝ} {z : ℂ}
    (h : ‖HermitePoly m n z‖ ≤ A * (Real.sqrt (m.factorial : ℝ))⁻¹) :
    ‖HermitePoly m n z‖ ^ 2 ≤ A ^ 2 / (m.factorial : ℝ) := by
  have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hs2 : (Real.sqrt (m.factorial : ℝ)) ^ 2 = (m.factorial : ℝ) := Real.sq_sqrt hfacpos.le
  calc ‖HermitePoly m n z‖ ^ 2
      ≤ (A * (Real.sqrt (m.factorial : ℝ))⁻¹) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg (HermitePoly m n z)) h 2
    _ = A ^ 2 / (m.factorial : ℝ) := by rw [mul_pow, inv_pow, hs2, div_eq_mul_inv]

/-- The main pointwise bound:
`‖φ_{m,n}(z, z̄)‖ ≤ (L+1) 2^L m^L ‖z‖^{m-L} / √(m!)` whenever `n ≤ L ≤ m` and `‖z‖² ≤ m`.
The instance of `norm_phi_le_of_term_le` with `T = 2^L (m^L ‖z‖^{m-L})`. -/
lemma norm_phi_le (L m n : ℕ) (hn : n ≤ L) (hLm : L ≤ m) (hm : 1 ≤ m) (z : ℂ)
    (hz : ‖z‖ ^ 2 ≤ (m : ℝ)) :
    ‖HermitePoly m n z‖ ≤ ((L : ℝ) + 1) * 2 ^ L * (m : ℝ) ^ L * ‖z‖ ^ (m - L) *
      (Real.sqrt (m.factorial : ℝ))⁻¹ := by
  have hx : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hxm : ‖z‖ ≤ (m : ℝ) := by nlinarith [sq_nonneg (‖z‖ - 1)]
  have hmin : min m n = n := min_eq_right (hn.trans hLm)
  -- the last step `m^n ‖z‖^{m-n} ≤ m^L ‖z‖^{m-L}`, absorbed into the term bound
  have hlast : (m : ℝ) ^ n * ‖z‖ ^ (m - n) ≤ (m : ℝ) ^ L * ‖z‖ ^ (m - L) := by
    have hLn : (m : ℝ) ^ L = (m : ℝ) ^ n * (m : ℝ) ^ (L - n) := by
      rw [← pow_add]; congr 1; omega
    have hxsplit : ‖z‖ ^ (m - n) = ‖z‖ ^ (m - L) * ‖z‖ ^ (L - n) := by
      rw [← pow_add]; congr 1; omega
    calc (m : ℝ) ^ n * ‖z‖ ^ (m - n) = (m : ℝ) ^ n * ‖z‖ ^ (m - L) * ‖z‖ ^ (L - n) := by
          rw [hxsplit]; ring
      _ ≤ (m : ℝ) ^ n * ‖z‖ ^ (m - L) * (m : ℝ) ^ (L - n) := by gcongr
      _ = (m : ℝ) ^ L * ‖z‖ ^ (m - L) := by rw [hLn]; ring
  have hterm : ∀ r ≤ min m n,
      (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) * ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r)
        ≤ 2 ^ L * ((m : ℝ) ^ L * ‖z‖ ^ (m - L)) := by
    intro r hr
    rw [hmin] at hr
    have hchooseL : (n.choose r : ℝ) ≤ 2 ^ L := by
      have h : (n.choose r : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n r
      exact h.trans (pow_le_pow_right₀ (by norm_num) hn)
    have hmr : (m : ℝ) ^ r * (m : ℝ) ^ (n - r) = (m : ℝ) ^ n := by
      rw [← pow_add]; congr 1; omega
    calc (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) * ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r)
        ≤ (m : ℝ) ^ r * 2 ^ L * (‖z‖ ^ (m - n) * (m : ℝ) ^ (n - r)) :=
          phi_term_le (hn.trans hLm) hr le_rfl hchooseL
            (pow_le_pow_left₀ (by positivity) hz _) (by positivity)
      _ = 2 ^ L * ((m : ℝ) ^ n * ‖z‖ ^ (m - n)) := by rw [← hmr]; ring
      _ ≤ 2 ^ L * ((m : ℝ) ^ L * ‖z‖ ^ (m - L)) :=
          mul_le_mul_of_nonneg_left hlast (by positivity)
  calc ‖HermitePoly m n z‖
      ≤ ((L : ℝ) + 1) * (2 ^ L * ((m : ℝ) ^ L * ‖z‖ ^ (m - L))) *
          (Real.sqrt (m.factorial : ℝ))⁻¹ :=
        norm_phi_le_of_term_le (by positivity) (hmin.le.trans hn) hterm
    _ = ((L : ℝ) + 1) * 2 ^ L * (m : ℝ) ^ L * ‖z‖ ^ (m - L) *
          (Real.sqrt (m.factorial : ℝ))⁻¹ := by ring

/-- The squared form of `norm_phi_le`, in the shape used by the tail estimate. -/
lemma sq_norm_phi_le (L m n : ℕ) (hn : n ≤ L) (hLm : L ≤ m) (hm : 1 ≤ m) (z : ℂ)
    (hz : ‖z‖ ^ 2 ≤ (m : ℝ)) :
    ‖HermitePoly m n z‖ ^ 2 ≤ (((L : ℝ) + 1) * 2 ^ L) ^ 2 *
      ((m : ℝ) ^ (2 * L) * (‖z‖ ^ 2) ^ (m - L) / m.factorial) := by
  have h2L : (m : ℝ) ^ (2 * L) = ((m : ℝ) ^ L) ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  have hzz : (‖z‖ ^ 2) ^ (m - L) = (‖z‖ ^ (m - L)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  calc ‖HermitePoly m n z‖ ^ 2
      ≤ (((L : ℝ) + 1) * 2 ^ L * (m : ℝ) ^ L * ‖z‖ ^ (m - L)) ^ 2 / (m.factorial : ℝ) :=
        sq_norm_phi_le_of_norm_le (norm_phi_le L m n hn hLm hm z hz)
    _ = (((L : ℝ) + 1) * 2 ^ L) ^ 2 *
          ((m : ℝ) ^ (2 * L) * (‖z‖ ^ 2) ^ (m - L) / m.factorial) := by
        rw [h2L, hzz]; ring

end

end PolyFock
