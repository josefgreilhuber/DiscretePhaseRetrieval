import VCInequality.Defs

/-!
# Robbins' bounds and the central binomial term

* Robbins' upper bound `n! ≤ √(2πn) (n/e)^n · exp(1/(12n))` for `n ≥ 1`.
  Mathlib has `Stirling.le_factorial_stirling : √(2πn) (n/e)^n ≤ n!`,
  `Stirling.stirlingSeq n = n! / (√(2n) (n/e)^n)`, `Stirling.sqrt_pi_le_stirlingSeq`,
  `Stirling.log_stirlingSeq_diff_hasSum` (the exact series for
  `log (stirlingSeq (n+1)) − log (stirlingSeq (n+2))`), `Stirling.log_stirlingSeq_diff_le_geo_sum`,
  and `Stirling.tendsto_stirlingSeq_sqrt_pi`. From the geometric-sum bound one gets
  `log (stirlingSeq (n+1)) − log (stirlingSeq (n+2)) ≤ 1/(12 (n+1)(n+2))`, which telescopes to
  `log (stirlingSeq (N+1)) − log √π ≤ 1/(12 (N+1))`, i.e. Robbins.
* Consequence for the central-type term with `p = k/m`, `1 ≤ k < m`:

      C(m,k) (k/m)^k (1 − k/m)^{m−k} ≥ √(m / (2π k (m−k))) · exp(−1/(12k) − 1/(12(m−k))).
-/

open Finset Real Filter Topology

namespace VCInequality

/-- The sequence `log (stirlingSeq (M+1)) - 1/(12(M+1))` is monotone increasing. -/
private lemma logStirlingSub_monotone :
    Monotone (fun M : ℕ => Real.log (Stirling.stirlingSeq (M + 1)) - 1 / (12 * (M + 1))) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := Stirling.log_stirlingSeq_diff_le (n + 1)
  push_cast at h ⊢
  have key : 1 / (12 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1))
      = 1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 1 + 1)) := by
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [key] at h
  linarith

private lemma logStirlingSub_tendsto :
    Tendsto (fun M : ℕ => Real.log (Stirling.stirlingSeq (M + 1)) - 1 / (12 * (M + 1)))
      atTop (𝓝 (Real.log (Real.sqrt π))) := by
  have hs : Tendsto (fun M : ℕ => Stirling.stirlingSeq (M + 1)) atTop (𝓝 (Real.sqrt π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun M : ℕ => Real.log (Stirling.stirlingSeq (M + 1))) atTop
      (𝓝 (Real.log (Real.sqrt π))) := hs.log (by positivity)
  have h2 : Tendsto (fun M : ℕ => 1 / (12 * ((M : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 12 : ℝ)
    rw [mul_zero] at h
    refine h.congr fun M => ?_
    field_simp
  simpa using hlog.sub h2

private lemma log_stirlingSeq_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) ≤ Real.log (Real.sqrt π) + 1 / (12 * n) := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  have := logStirlingSub_monotone.ge_of_tendsto logStirlingSub_tendsto M
  push_cast at this ⊢
  linarith

/-- Robbins' upper bound for the factorial. -/
theorem factorial_le_stirling (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.sqrt (2 * π * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsq : (0 : ℝ) < Real.sqrt (2 * (n : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hp : (0 : ℝ) < ((n : ℝ) / Real.exp 1) ^ n := pow_pos (div_pos hn0 hE) n
  have hden : (0 : ℝ) < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n := mul_pos hsq hp
  have hSpos : 0 < Stirling.stirlingSeq n := by
    rw [Stirling.stirlingSeq]
    exact div_pos (by exact_mod_cast n.factorial_pos) hden
  have hfac : (n.factorial : ℝ)
      = Stirling.stirlingSeq n * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
    rw [Stirling.stirlingSeq]
    field_simp
  have hpi : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hS : Stirling.stirlingSeq n ≤ Real.sqrt π * Real.exp (1 / (12 * n)) := by
    have h := Real.exp_le_exp.mpr (log_stirlingSeq_le n hn)
    rwa [Real.exp_log hSpos, Real.exp_add, Real.exp_log hpi] at h
  have hsplit : Real.sqrt (2 * π * (n : ℝ)) = Real.sqrt π * Real.sqrt (2 * (n : ℝ)) := by
    rw [show (2 * π * (n : ℝ)) = π * (2 * n) by ring, Real.sqrt_mul Real.pi_pos.le]
  rw [hfac, hsplit]
  calc Stirling.stirlingSeq n * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n)
      ≤ (Real.sqrt π * Real.exp (1 / (12 * n)))
        * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
        gcongr
    _ = Real.sqrt π * Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n
        * Real.exp (1 / (12 * n)) := by ring

/-- Lower bound for `P[Bin(m, k/m) = k]`, `1 ≤ k < m`. -/
theorem central_term_ge (m k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    Real.sqrt (m / (2 * π * k * (m - k))) * Real.exp (-(1 / (12 * k)) - 1 / (12 * (m - k)))
      ≤ (m.choose k : ℝ) * (k / m) ^ k * (1 - k / m) ^ (m - k) := by
  obtain ⟨j, hjN⟩ : ∃ j, m - k = j := ⟨m - k, rfl⟩
  have hjpos : 1 ≤ j := by omega
  have hnat : k + j = m := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hjne : (j : ℝ) ≠ 0 := ne_of_gt hj0
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπne : π ≠ 0 := ne_of_gt hπ
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hEne : Real.exp 1 ≠ 0 := ne_of_gt hE
  have hjR : ((m : ℝ) - k) = (j : ℝ) := by
    have h : ((m : ℕ) : ℝ) = (k : ℝ) + j := by exact_mod_cast hnat.symm
    rw [h]; ring
  have h1k : (1 : ℝ) - (k : ℝ) / m = (j : ℝ) / m := by
    rw [← hjR]; field_simp
  rw [hjN, hjR, h1k]
  -- positivity facts
  have hsqm : (0 : ℝ) < Real.sqrt (2 * π * (m : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos (by positivity) hm0)
  have hsqk : (0 : ℝ) < Real.sqrt (2 * π * (k : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos (by positivity) hk0)
  have hsqj : (0 : ℝ) < Real.sqrt (2 * π * (j : ℝ)) :=
    Real.sqrt_pos.mpr (mul_pos (by positivity) hj0)
  have hPm : (0 : ℝ) < ((m : ℝ) / Real.exp 1) ^ m := pow_pos (div_pos hm0 hE) m
  have hPk : (0 : ℝ) < ((k : ℝ) / Real.exp 1) ^ k := pow_pos (div_pos hk0 hE) k
  have hPj : (0 : ℝ) < ((j : ℝ) / Real.exp 1) ^ j := pow_pos (div_pos hj0 hE) j
  have hBkpos : (0 : ℝ) < Real.sqrt (2 * π * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k
      * Real.exp (1 / (12 * (k : ℝ))) := mul_pos (mul_pos hsqk hPk) (Real.exp_pos _)
  have hBjpos : (0 : ℝ) < Real.sqrt (2 * π * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j
      * Real.exp (1 / (12 * (j : ℝ))) := mul_pos (mul_pos hsqj hPj) (Real.exp_pos _)
  have hFk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hFj : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  -- the three algebraic identities
  have hexp : Real.exp (-(1 / (12 * (k : ℝ))) - 1 / (12 * (j : ℝ)))
      * (Real.exp (1 / (12 * (k : ℝ))) * Real.exp (1 / (12 * (j : ℝ)))) = 1 := by
    have h : -(1 / (12 * (k : ℝ))) - 1 / (12 * (j : ℝ))
        + (1 / (12 * (k : ℝ)) + 1 / (12 * (j : ℝ))) = 0 := by ring
    rw [← Real.exp_add, ← Real.exp_add, h, Real.exp_zero]
  have hsqrt : Real.sqrt ((m : ℝ) / (2 * π * (k : ℝ) * (j : ℝ)))
      * (Real.sqrt (2 * π * (k : ℝ)) * Real.sqrt (2 * π * (j : ℝ)))
      = Real.sqrt (2 * π * (m : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hpow : ((m : ℝ) / Real.exp 1) ^ m * (((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j)
      = ((k : ℝ) / Real.exp 1) ^ k * ((j : ℝ) / Real.exp 1) ^ j := by
    have e1 : ((m : ℝ) / Real.exp 1) * ((k : ℝ) / m) = (k : ℝ) / Real.exp 1 := by
      field_simp
    have e2 : ((m : ℝ) / Real.exp 1) * ((j : ℝ) / m) = (j : ℝ) / Real.exp 1 := by
      field_simp
    have e3 : ((m : ℝ) / Real.exp 1) ^ m
        = ((m : ℝ) / Real.exp 1) ^ k * ((m : ℝ) / Real.exp 1) ^ j := by
      rw [← pow_add, hnat]
    calc ((m : ℝ) / Real.exp 1) ^ m * (((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j)
        = (((m : ℝ) / Real.exp 1) ^ k * ((k : ℝ) / m) ^ k)
          * (((m : ℝ) / Real.exp 1) ^ j * ((j : ℝ) / m) ^ j) := by rw [e3]; ring
      _ = (((m : ℝ) / Real.exp 1) * ((k : ℝ) / m)) ^ k
          * (((m : ℝ) / Real.exp 1) * ((j : ℝ) / m)) ^ j := by rw [mul_pow, mul_pow]
      _ = ((k : ℝ) / Real.exp 1) ^ k * ((j : ℝ) / Real.exp 1) ^ j := by rw [e1, e2]
  have hkey : Real.sqrt ((m : ℝ) / (2 * π * (k : ℝ) * (j : ℝ)))
        * Real.exp (-(1 / (12 * (k : ℝ))) - 1 / (12 * (j : ℝ)))
        * ((Real.sqrt (2 * π * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k
              * Real.exp (1 / (12 * (k : ℝ))))
          * (Real.sqrt (2 * π * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j
              * Real.exp (1 / (12 * (j : ℝ)))))
      = Real.sqrt (2 * π * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m
        * ((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j := by
    calc Real.sqrt ((m : ℝ) / (2 * π * (k : ℝ) * (j : ℝ)))
          * Real.exp (-(1 / (12 * (k : ℝ))) - 1 / (12 * (j : ℝ)))
          * ((Real.sqrt (2 * π * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k
                * Real.exp (1 / (12 * (k : ℝ))))
            * (Real.sqrt (2 * π * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j
                * Real.exp (1 / (12 * (j : ℝ)))))
        = (Real.sqrt ((m : ℝ) / (2 * π * (k : ℝ) * (j : ℝ)))
            * (Real.sqrt (2 * π * (k : ℝ)) * Real.sqrt (2 * π * (j : ℝ))))
          * (((k : ℝ) / Real.exp 1) ^ k * ((j : ℝ) / Real.exp 1) ^ j)
          * (Real.exp (-(1 / (12 * (k : ℝ))) - 1 / (12 * (j : ℝ)))
            * (Real.exp (1 / (12 * (k : ℝ))) * Real.exp (1 / (12 * (j : ℝ))))) := by ring
      _ = Real.sqrt (2 * π * (m : ℝ))
          * (((k : ℝ) / Real.exp 1) ^ k * ((j : ℝ) / Real.exp 1) ^ j) * 1 := by
          rw [hsqrt, hexp]
      _ = Real.sqrt (2 * π * (m : ℝ))
          * (((m : ℝ) / Real.exp 1) ^ m * (((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j)) := by
          rw [hpow]; ring
      _ = Real.sqrt (2 * π * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m
          * ((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j := by ring
  have hchoose : (m.choose k : ℝ) * ((k.factorial : ℝ) * (j.factorial : ℝ))
      = (m.factorial : ℝ) := by
    have h : m.choose k * k.factorial * (m - k).factorial = m.factorial :=
      Nat.choose_mul_factorial_mul_factorial hkm.le
    rw [hjN] at h
    have h' : ((m.choose k * k.factorial * j.factorial : ℕ) : ℝ) = ((m.factorial : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at h'
    linear_combination h'
  have hFkBk := factorial_le_stirling k hk
  have hFjBj := factorial_le_stirling j hjpos
  have hAm := Stirling.le_factorial_stirling m
  have final : Real.sqrt ((m : ℝ) / (2 * π * (k : ℝ) * (j : ℝ)))
        * Real.exp (-(1 / (12 * (k : ℝ))) - 1 / (12 * (j : ℝ)))
        * ((k.factorial : ℝ) * (j.factorial : ℝ))
      ≤ ((m.choose k : ℝ) * ((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j)
        * ((k.factorial : ℝ) * (j.factorial : ℝ)) := by
    calc Real.sqrt ((m : ℝ) / (2 * π * (k : ℝ) * (j : ℝ)))
          * Real.exp (-(1 / (12 * (k : ℝ))) - 1 / (12 * (j : ℝ)))
          * ((k.factorial : ℝ) * (j.factorial : ℝ))
        ≤ Real.sqrt ((m : ℝ) / (2 * π * (k : ℝ) * (j : ℝ)))
          * Real.exp (-(1 / (12 * (k : ℝ))) - 1 / (12 * (j : ℝ)))
          * ((Real.sqrt (2 * π * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k
                * Real.exp (1 / (12 * (k : ℝ))))
            * (Real.sqrt (2 * π * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j
                * Real.exp (1 / (12 * (j : ℝ))))) := by
          gcongr
      _ = Real.sqrt (2 * π * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m
          * ((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j := hkey
      _ ≤ (m.factorial : ℝ) * ((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j := by
          gcongr
      _ = ((m.choose k : ℝ) * ((k : ℝ) / m) ^ k * ((j : ℝ) / m) ^ j)
          * ((k.factorial : ℝ) * (j.factorial : ℝ)) := by
          rw [← hchoose]; ring
  exact le_of_mul_le_mul_right final (mul_pos hFk hFj)

end VCInequality
