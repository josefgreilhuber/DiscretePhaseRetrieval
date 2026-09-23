import Mathlib

/-!
# Auxiliary definitions and lemmas

Small notions and facts used by several, otherwise independent, parts of the development.  The
file imports only Mathlib, so it can sit below every other root of the library.

* `DiscretePR.size` — the size `‖α‖₁ = ∑ i, α i` of a multi-index `α ∈ ℕ^d`, with the scoped
  notation `‖α‖₁`; the total degree used throughout `PolyFock/` and `DiscretePhaseRetrieval/`.
* `DiscretePR.sum_choose_le_exp_pow` — the binomial-tail estimate `∑_{k ≤ V} C(n,k) ≤ (e n / V)^V`,
  used in the Sauer–Shelah step of the VC inequality (`VCInequality/Sauer.lean`) and in Warren's
  sign-pattern bound (`Warren/SignPatterns/SignPatternBound.lean`).
-/

open Finset

namespace DiscretePR

variable {d : ℕ}

/-- The size `‖α‖₁ = ∑ i, α i` of a multi-index `α ∈ ℕ^d` (the paper's `|α|`; for the Landau level
`κ` this is `|κ|`). -/
def size (α : Fin d → ℕ) : ℕ := ∑ i, α i

@[inherit_doc size]
scoped notation:max "‖" q "‖₁" => size q

/-- The classical binomial-tail estimate `∑_{k ≤ V} C(n,k) ≤ (e n / V)^V`, for `1 ≤ V ≤ n`.

Used in the Sauer–Shelah step of the VC inequality (`VCInequality.isGrowthBound_of_vcDimLE`) and
in Warren's sign-pattern bound (`SignPatterns.sign_patterns_warren`). -/
theorem sum_choose_le_exp_pow (n V : ℕ) (hV : 1 ≤ V) (hVn : V ≤ n) :
    (∑ k ∈ Iic V, (n.choose k : ℝ)) ≤ (Real.exp 1 * n / V) ^ V := by
  have hn : 0 < n := lt_of_lt_of_le hV hVn
  have hVR : (0:ℝ) < V := by exact_mod_cast hV
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  set r : ℝ := (V : ℝ) / n with hr
  have hr0 : 0 < r := div_pos hVR hnR
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hnR]
    exact_mod_cast hVn
  -- Multiplying by `r ^ V ≤ r ^ k` for `k ≤ V`.
  have step1 : r ^ V * (∑ k ∈ Iic V, (n.choose k : ℝ))
      ≤ ∑ k ∈ Iic V, r ^ k * (n.choose k : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro k hk
    have hkV : k ≤ V := Finset.mem_Iic.mp hk
    have : r ^ V ≤ r ^ k := pow_le_pow_of_le_one hr0.le hr1 hkV
    exact mul_le_mul_of_nonneg_right this (by positivity)
  -- Extending the sum to all `k ≤ n` (the extra terms are nonnegative).
  have step2 : (∑ k ∈ Iic V, r ^ k * (n.choose k : ℝ))
      ≤ ∑ k ∈ range (n+1), r ^ k * (n.choose k : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ ↦ by positivity)
    rw [Nat.range_succ_eq_Iic]
    exact Finset.Iic_subset_Iic.mpr hVn
  -- The binomial theorem.
  have step3 : (∑ k ∈ range (n+1), r ^ k * (n.choose k : ℝ)) = (r + 1) ^ n := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ ↦ by rw [one_pow, mul_one]
  -- `1 + x ≤ exp x`, and `exp (V / n) ^ n = exp V`.
  have step4 : (r + 1) ^ n ≤ Real.exp V := by
    calc (r + 1) ^ n ≤ (Real.exp r) ^ n :=
          pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp r) n
      _ = Real.exp ((n : ℝ) * r) := (Real.exp_nat_mul r n).symm
      _ = Real.exp V := by
          congr 1
          rw [hr]
          field_simp
  have key : r ^ V * (∑ k ∈ Iic V, (n.choose k : ℝ)) ≤ Real.exp V := by
    calc r ^ V * (∑ k ∈ Iic V, (n.choose k : ℝ))
        ≤ ∑ k ∈ Iic V, r ^ k * (n.choose k : ℝ) := step1
      _ ≤ ∑ k ∈ range (n+1), r ^ k * (n.choose k : ℝ) := step2
      _ = (r + 1) ^ n := step3
      _ ≤ Real.exp V := step4
  -- Divide by `r ^ V`.
  have hrhs : r ^ V * (Real.exp 1 * n / V) ^ V = Real.exp V := by
    rw [← mul_pow]
    have : r * (Real.exp 1 * n / V) = Real.exp 1 := by
      rw [hr]; field_simp
    rw [this, Real.exp_one_pow]
  have hrVpos : (0:ℝ) < r ^ V := by positivity
  rw [← hrhs] at key
  exact le_of_mul_le_mul_left key hrVpos

/-- `sum_choose_le_exp_pow` in the `Finset.range (V+1)` form, with the sum taken in `ℕ`. -/
theorem sum_choose_le_exp_pow_range (n V : ℕ) (hV : 1 ≤ V) (hVn : V ≤ n) :
    ((∑ k ∈ range (V + 1), n.choose k : ℕ) : ℝ) ≤ (Real.exp 1 * n / V) ^ V := by
  rw [Nat.cast_sum, Nat.range_succ_eq_Iic]
  exact sum_choose_le_exp_pow n V hV hVn

end DiscretePR
