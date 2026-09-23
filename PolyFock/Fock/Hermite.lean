/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Fock.Creation

/-!
# The complex Hermite polynomials as elements of `ℂ[z, z̄]`

`Hpoly i m n` is the polynomial `H_{m,n}(zᵢ, z̄ᵢ) = ∑_r (-1)^r r! C(m,r) C(n,r) zᵢ^{m-r} z̄ᵢ^{n-r}`,
the unnormalised version of the comparator's `DiscretePR.HermitePoly`.  We prove the three
identities that make it the image of `1` under the creation operators:

* `PolyFock.Fock.pderiv_inl_Hpoly` — `∂_{zᵢ} H_{m,n} = m H_{m-1,n}`
* `PolyFock.Fock.pderiv_inr_Hpoly` — `∂_{z̄ᵢ} H_{m,n} = n H_{m,n-1}`
* `PolyFock.Fock.Hpoly_succ_left` — `H_{m+1,n} = Aᵢ H_{m,n}`
* `PolyFock.Fock.Hpoly_succ_right` — `H_{m,n+1} = Bᵢ H_{m,n}`
-/

namespace PolyFock.Fock

open Finset MvPolynomial

noncomputable section

variable {d : ℕ}

/-! ### Two binomial identities -/

lemma choose_mul_sub (m r : ℕ) : m.choose r * (m - r) = m * (m - 1).choose r := by
  cases m with
  | zero => simp
  | succ M =>
      simp only [Nat.add_sub_cancel]
      rw [← Nat.choose_mul_succ_eq M r, Nat.mul_comm]

lemma succ_mul_choose_succ (n s : ℕ) : (s + 1) * n.choose (s + 1) = n * (n - 1).choose s := by
  cases n with
  | zero => simp
  | succ N =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm, Nat.choose_succ_right_eq, Nat.mul_comm (N + 1),
        ← Nat.choose_mul_succ_eq N s]

/-! ### The coefficients -/

/-- The coefficient of `zᵢ^{m-r} z̄ᵢ^{n-r}` in `H_{m,n}`. -/
def cc (m n r : ℕ) : ℂ :=
  (-1 : ℂ) ^ r * (r.factorial : ℂ) * (m.choose r : ℂ) * (n.choose r : ℂ)

lemma cc_eq_zero_of_lt {m n r : ℕ} (h : min m n < r) : cc m n r = 0 := by
  rw [cc]
  rcases Nat.lt_or_ge m r with hm | hm
  · rw [Nat.choose_eq_zero_of_lt hm]; simp
  · have hn : n < r := by omega
    rw [Nat.choose_eq_zero_of_lt hn]; simp

/-- `(m-r) · cc m n r = m · cc (m-1) n r`. -/
lemma sub_mul_cc_inl (m n r : ℕ) :
    ((m - r : ℕ) : ℂ) * cc m n r = (m : ℂ) * cc (m - 1) n r := by
  have h : ((m.choose r : ℂ)) * ((m - r : ℕ) : ℂ) = (m : ℂ) * (((m - 1).choose r : ℕ) : ℂ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, choose_mul_sub]
  rw [cc, cc]
  linear_combination ((-1 : ℂ) ^ r * (r.factorial : ℂ) * (n.choose r : ℂ)) * h

/-- `(n-r) · cc m n r = n · cc m (n-1) r`. -/
lemma sub_mul_cc_inr (m n r : ℕ) :
    ((n - r : ℕ) : ℂ) * cc m n r = (n : ℂ) * cc m (n - 1) r := by
  have h : ((n.choose r : ℂ)) * ((n - r : ℕ) : ℂ) = (n : ℂ) * (((n - 1).choose r : ℕ) : ℂ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, choose_mul_sub]
  rw [cc, cc]
  linear_combination ((-1 : ℂ) ^ r * (r.factorial : ℂ) * (m.choose r : ℂ)) * h

/-- The Pascal-type recursion for the coefficients. -/
lemma cc_succ_left (m n s : ℕ) :
    cc (m + 1) n (s + 1) = cc m n (s + 1) - (n : ℂ) * cc m (n - 1) s := by
  have hpascal : (m + 1).choose (s + 1) = m.choose s + m.choose (s + 1) :=
    Nat.choose_succ_succ m s
  have hkey' : ((s : ℂ) + 1) * (n.choose (s + 1) : ℂ) = (n : ℂ) * ((n - 1).choose s : ℂ) := by
    have h := congrArg (fun k : ℕ => (k : ℂ)) (succ_mul_choose_succ n s)
    push_cast at h
    exact h
  rw [cc, cc, cc, hpascal]
  push_cast [Nat.factorial_succ]
  linear_combination (-((-1 : ℂ) ^ s * (s.factorial : ℂ) * (m.choose s : ℂ))) * hkey'

/-! ### The polynomials -/

/-- The complex Hermite polynomial `H_{m,n}(zᵢ, z̄ᵢ)`. -/
def Hpoly (i : Fin d) (m n : ℕ) : P d :=
  ∑ r ∈ range (min m n + 1), C (cc m n r) * X (Sum.inl i) ^ (m - r) * X (Sum.inr i) ^ (n - r)

/-- `H_{m,n}` may be written as a sum over any range containing `min m n`. -/
lemma Hpoly_eq_sum (i : Fin d) (m n N : ℕ) (h : min m n ≤ N) :
    Hpoly i m n =
      ∑ r ∈ range (N + 1), C (cc m n r) * X (Sum.inl i) ^ (m - r) * X (Sum.inr i) ^ (n - r) := by
  rw [Hpoly]
  refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr ?_) fun r _ hr => ?_
  · rw [Finset.mem_range] at hx; omega
  rw [Finset.mem_range] at hr
  rw [cc_eq_zero_of_lt (by omega), map_zero, zero_mul, zero_mul]

@[simp] lemma Hpoly_zero_zero (i : Fin d) : Hpoly i 0 0 = 1 := by
  rw [Hpoly]
  simp [cc]

/-! ### Derivatives -/

lemma pderiv_inl_term (i : Fin d) (c : ℂ) (a b : ℕ) :
    (pderiv (Sum.inl i)) (C c * X (Sum.inl i) ^ a * X (Sum.inr i) ^ b)
      = C ((a : ℂ) * c) * X (Sum.inl i) ^ (a - 1) * X (Sum.inr i) ^ b := by
  have hne : (Sum.inr i : Idx d) ≠ Sum.inl i := by simp
  rw [pderiv_mul, pderiv_mul]
  simp only [pderiv_C, zero_mul, zero_add, pderiv_pow, pderiv_X_self, mul_one,
    pderiv_X_of_ne hne, mul_zero, add_zero]
  rw [map_mul, map_natCast]
  ring

lemma pderiv_inr_term (i : Fin d) (c : ℂ) (a b : ℕ) :
    (pderiv (Sum.inr i)) (C c * X (Sum.inl i) ^ a * X (Sum.inr i) ^ b)
      = C ((b : ℂ) * c) * X (Sum.inl i) ^ a * X (Sum.inr i) ^ (b - 1) := by
  have hne : (Sum.inl i : Idx d) ≠ Sum.inr i := by simp
  rw [pderiv_mul, pderiv_mul]
  simp only [pderiv_C, zero_mul, zero_add, pderiv_pow, pderiv_X_self, mul_one,
    pderiv_X_of_ne hne, mul_zero, add_zero]
  rw [map_mul, map_natCast]
  ring

/-- `∂_{zᵢ} H_{m,n} = m H_{m-1,n}`. -/
lemma pderiv_inl_Hpoly (i : Fin d) (m n : ℕ) :
    (pderiv (Sum.inl i)) (Hpoly i m n) = (m : ℂ) • Hpoly i (m - 1) n := by
  classical
  rw [Hpoly_eq_sum i m n (m + n) (by omega), Hpoly_eq_sum i (m - 1) n (m + n) (by omega),
    map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pderiv_inl_term]
  rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← map_mul]
  rw [show m - 1 - r = m - r - 1 from by omega]
  rw [sub_mul_cc_inl m n r]

/-- `∂_{z̄ᵢ} H_{m,n} = n H_{m,n-1}`. -/
lemma pderiv_inr_Hpoly (i : Fin d) (m n : ℕ) :
    (pderiv (Sum.inr i)) (Hpoly i m n) = (n : ℂ) • Hpoly i m (n - 1) := by
  classical
  rw [Hpoly_eq_sum i m n (m + n) (by omega), Hpoly_eq_sum i m (n - 1) (m + n) (by omega),
    map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pderiv_inr_term]
  rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← map_mul]
  rw [show n - 1 - r = n - r - 1 from by omega]
  rw [sub_mul_cc_inr m n r]

/-- Derivatives in the other coordinates vanish. -/
lemma pderiv_inl_Hpoly_of_ne (i j : Fin d) (h : j ≠ i) (m n : ℕ) :
    (pderiv (Sum.inl j)) (Hpoly i m n) = 0 := by
  classical
  rw [Hpoly, map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [pderiv_mul, pderiv_mul]
  have h1 : (Sum.inl i : Idx d) ≠ Sum.inl j := by simpa using (Ne.symm h)
  have h2 : (Sum.inr i : Idx d) ≠ Sum.inl j := by simp
  simp [pderiv_X_of_ne h1, pderiv_X_of_ne h2]

lemma pderiv_inr_Hpoly_of_ne (i j : Fin d) (h : j ≠ i) (m n : ℕ) :
    (pderiv (Sum.inr j)) (Hpoly i m n) = 0 := by
  classical
  rw [Hpoly, map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [pderiv_mul, pderiv_mul]
  have h1 : (Sum.inl i : Idx d) ≠ Sum.inr j := by simp
  have h2 : (Sum.inr i : Idx d) ≠ Sum.inr j := by simpa using (Ne.symm h)
  simp [pderiv_X_of_ne h1, pderiv_X_of_ne h2]

/-! ### The creation-operator recursions -/

lemma cc_symm (m n r : ℕ) : cc m n r = cc n m r := by rw [cc, cc]; ring

lemma cc_succ_right (m n s : ℕ) :
    cc m (n + 1) (s + 1) = cc m n (s + 1) - (m : ℂ) * cc (m - 1) n s := by
  rw [cc_symm m (n + 1), cc_symm m n, cc_symm (m - 1) n, cc_succ_left n m s]

@[simp] lemma cc_zero (m n : ℕ) : cc m n 0 = 1 := by simp [cc]

/-- `H_{m+1,n} = Aᵢ H_{m,n}`: the creation operator `Aᵢ` raises the first index. -/
lemma Hpoly_succ_left (i : Fin d) (m n : ℕ) :
    Hpoly i (m + 1) n = A i (Hpoly i m n) := by
  classical
  rw [A, pderiv_inr_Hpoly, Hpoly_eq_sum i (m + 1) n (m + n + 1) (by omega),
    Hpoly_eq_sum i m n (m + n + 1) (by omega), Hpoly_eq_sum i m (n - 1) (m + n) (by omega),
    Finset.mul_sum, Finset.smul_sum,
    Finset.sum_range_succ' (fun r => C (cc (m + 1) n r) * X (Sum.inl i) ^ (m + 1 - r) *
      X (Sum.inr i) ^ (n - r)) (m + n + 1),
    Finset.sum_range_succ' (fun r => X (Sum.inl i) * (C (cc m n r) * X (Sum.inl i) ^ (m - r) *
      X (Sum.inr i) ^ (n - r))) (m + n + 1)]
  have hterm : ∀ s ∈ Finset.range (m + n + 1),
      C (cc (m + 1) n (s + 1)) * X (Sum.inl i) ^ (m + 1 - (s + 1)) *
          X (Sum.inr i) ^ (n - (s + 1))
        = X (Sum.inl i) * (C (cc m n (s + 1)) * X (Sum.inl i) ^ (m - (s + 1)) *
            X (Sum.inr i) ^ (n - (s + 1)))
          - (n : ℂ) • (C (cc m (n - 1) s) * X (Sum.inl i) ^ (m - s) *
              X (Sum.inr i) ^ (n - 1 - s)) := by
    intro s _
    rw [show m + 1 - (s + 1) = m - s from by omega, show n - (s + 1) = n - 1 - s from by omega,
      cc_succ_left m n s, MvPolynomial.smul_eq_C_mul, map_sub, map_mul]
    by_cases hs : s < m
    · obtain ⟨k, hk⟩ : ∃ k, m - s = k + 1 := ⟨m - s - 1, by omega⟩
      rw [show m - (s + 1) = k from by omega, hk, pow_succ]
      ring
    · have hz : cc m n (s + 1) = 0 := by
        rw [cc, Nat.choose_eq_zero_of_lt (by omega : m < s + 1)]
        simp
      rw [hz]
      simp
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have h0 : C (cc (m + 1) n 0) * X (Sum.inl i) ^ (m + 1 - 0) * X (Sum.inr i) ^ (n - 0)
      = X (Sum.inl i) * (C (cc m n 0) * X (Sum.inl i) ^ (m - 0) * X (Sum.inr i) ^ (n - 0)) := by
    simp only [cc_zero, map_one, one_mul, Nat.sub_zero, pow_succ]
    ring
  rw [h0]
  ring

/-- `H_{m,n+1} = Bᵢ H_{m,n}`: the creation operator `Bᵢ` raises the second index. -/
lemma Hpoly_succ_right (i : Fin d) (m n : ℕ) :
    Hpoly i m (n + 1) = B i (Hpoly i m n) := by
  classical
  rw [B, pderiv_inl_Hpoly, Hpoly_eq_sum i m (n + 1) (m + n + 1) (by omega),
    Hpoly_eq_sum i m n (m + n + 1) (by omega), Hpoly_eq_sum i (m - 1) n (m + n) (by omega),
    Finset.mul_sum, Finset.smul_sum,
    Finset.sum_range_succ' (fun r => C (cc m (n + 1) r) * X (Sum.inl i) ^ (m - r) *
      X (Sum.inr i) ^ (n + 1 - r)) (m + n + 1),
    Finset.sum_range_succ' (fun r => X (Sum.inr i) * (C (cc m n r) * X (Sum.inl i) ^ (m - r) *
      X (Sum.inr i) ^ (n - r))) (m + n + 1)]
  have hterm : ∀ s ∈ Finset.range (m + n + 1),
      C (cc m (n + 1) (s + 1)) * X (Sum.inl i) ^ (m - (s + 1)) *
          X (Sum.inr i) ^ (n + 1 - (s + 1))
        = X (Sum.inr i) * (C (cc m n (s + 1)) * X (Sum.inl i) ^ (m - (s + 1)) *
            X (Sum.inr i) ^ (n - (s + 1)))
          - (m : ℂ) • (C (cc (m - 1) n s) * X (Sum.inl i) ^ (m - 1 - s) *
              X (Sum.inr i) ^ (n - s)) := by
    intro s _
    rw [show n + 1 - (s + 1) = n - s from by omega, show m - (s + 1) = m - 1 - s from by omega,
      cc_succ_right m n s, MvPolynomial.smul_eq_C_mul, map_sub, map_mul]
    by_cases hs : s < n
    · obtain ⟨k, hk⟩ : ∃ k, n - s = k + 1 := ⟨n - s - 1, by omega⟩
      rw [show n - (s + 1) = k from by omega, hk, pow_succ]
      ring
    · have hz : cc m n (s + 1) = 0 := by
        rw [cc, Nat.choose_eq_zero_of_lt (by omega : n < s + 1)]
        simp
      rw [hz]
      simp
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have h0 : C (cc m (n + 1) 0) * X (Sum.inl i) ^ (m - 0) * X (Sum.inr i) ^ (n + 1 - 0)
      = X (Sum.inr i) * (C (cc m n 0) * X (Sum.inl i) ^ (m - 0) * X (Sum.inr i) ^ (n - 0)) := by
    simp only [cc_zero, map_one, one_mul, Nat.sub_zero, pow_succ]
    ring
  rw [h0]
  ring


end

end PolyFock.Fock
