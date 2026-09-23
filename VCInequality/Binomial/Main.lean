import VCInequality.Binomial.Law
import VCInequality.Binomial.Domination
import VCInequality.Binomial.DeMoivre
import VCInequality.Binomial.Stirling

/-!
# The binomial lemma with constant `1/8`

`P[Bin(m,p) ≥ m p] ≥ 1/8` for `m ≥ 1` and `1/m < p ≤ 1`.

Proof.
* `p = 1`: the tail is `1`.
* `p < 1`: let `k = ⌊m p⌋`, so `1 ≤ k ≤ m − 1` and `⌈m p⌉₊ ≤ k + 1`. Then
  `binTail m ⌈mp⌉₊ p ≥ binTail m (k+1) p ≥ binTail m (k+1) (k/m)` (`binTail_succ_le` iterated /
  `Finset.sum_le_sum_of_subset`, then `binTail_mono` since `k/m ≤ p`).
* `binTail m (k+1) (k/m) ≥ 1/8` for `1 ≤ k ≤ m−1` (this is `binTail_succ_div_ge`):
  - `k = 1`: `binTail m 2 (1/m) = 1 − (1 − 1/m)^{m−1} (2 − 1/m)`; for `m ≥ 4` use
    `(1−1/m)^{m−1} ≤ exp(−(m−1)/m)` (`Real.add_one_le_exp`) and
    `exp x ≥ 1 + x + x²/2` (`Real.quadratic_le_exp_of_nonneg`), which gives
    `(1 + x)/(1 + x + x²/2) ≤ 7/8` for `x = 1 − 1/m ≥ 3/4`; `m = 2, 3` by `norm_num`.
  - `k = m − 1`: `binTail m m ((m−1)/m) = (1 − 1/m)^m ≥ 1/(2e) > 1/8`, from
    `(1 + 1/(m−1))^{m−1} ≤ e` and `(1 + 1/(m−1)) ≤ 2`.
  - `2 ≤ k ≤ m − 2`: `binTail_succ_ge_sq` and `central_term_ge` give
    `≥ (k(m−k)/m) · (m/(2π k (m−k))) · exp(−1/(6k) − 1/(6(m−k))) ≥ exp(−1/6)/(2π) ≥ 1/8`,
    using `π < 3.15` (`Real.pi_lt_d2`) and `exp(−1/6) ≥ 5/6` (`Real.add_one_le_exp`).
-/

open Finset Real MeasureTheory ProbabilityTheory

namespace VCInequality

variable {X : Type*} [MeasurableSpace X]

/-- Peeling the two bottom terms (`j = 0` and `j = 1`) off the full binomial sum. -/
theorem binTail_two_eq (m : ℕ) (hm : 1 ≤ m) (p : ℝ) :
    binTail m 2 p = 1 - (1 - p) ^ m - m * p * (1 - p) ^ (m - 1) := by
  have h := binTail_zero m p
  unfold binTail binPmf at h ⊢
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc] at h
  norm_num at h
  rw [Finset.Icc_eq_cons_Ioc hm, Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc] at h
  norm_num at h
  linarith

/-- The elementary inequality behind the case `k = 1`: if `A ≥ 0` satisfies `A · exp q ≤ 1`
and `3/4 ≤ q ≤ 1`, then `A (1 + q) ≤ 7/8`. -/
theorem aux_pow_mul_le {A q : ℝ} (hA0 : 0 ≤ A) (hq : 3 / 4 ≤ q) (_hq1 : q ≤ 1)
    (hAE : A * Real.exp q ≤ 1) : A * (1 + q) ≤ 7 / 8 := by
  have h1 := Real.quadratic_le_exp_of_nonneg (by linarith : (0:ℝ) ≤ q)
  nlinarith [mul_nonneg hA0 (by nlinarith : (0:ℝ) ≤ 7 * q ^ 2 - 2 * q - 2),
    mul_nonneg hA0 (by linarith : (0:ℝ) ≤ Real.exp q - (1 + q + q ^ 2 / 2))]

/-- The case `k = 1` of `binTail_succ_div_ge`. -/
theorem binTail_two_ge (m : ℕ) (hm : 2 ≤ m) : 1 / 8 ≤ binTail m 2 (1 / (m : ℝ)) := by
  have hm0 : (0:ℝ) < m := by
    have : (0:ℕ) < m := by omega
    exact_mod_cast this
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm.trans' (by norm_num)
  rw [binTail_two_eq m (by omega)]
  have hmp : (m : ℝ) * (1 / (m:ℝ)) = 1 := by field_simp
  have hsucc : m - 1 + 1 = m := by omega
  have hpow : (1 - 1 / (m:ℝ)) ^ m = (1 - 1 / (m:ℝ)) ^ (m - 1) * (1 - 1 / (m:ℝ)) := by
    rw [← pow_succ, hsucc]
  rw [hpow, hmp]
  have key : (1 - 1 / (m:ℝ)) ^ (m - 1) * (1 + (1 - 1 / (m:ℝ))) ≤ 7 / 8 := by
    rcases lt_or_ge m 4 with hlt | hge
    · interval_cases m <;> norm_num
    · have hm4 : (4:ℝ) ≤ m := by exact_mod_cast hge
      have hinv : 1 / (m:ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hm4
      have hinv0 : 0 < 1 / (m:ℝ) := by positivity
      have hq0 : (0:ℝ) ≤ 1 - 1 / (m:ℝ) := by linarith
      have hq34 : (3:ℝ) / 4 ≤ 1 - 1 / (m:ℝ) := by linarith
      have hq1 : 1 - 1 / (m:ℝ) ≤ 1 := by linarith
      have hstep : (1 - 1 / (m:ℝ)) ≤ Real.exp (-(1 / (m:ℝ))) := by
        have := Real.add_one_le_exp (-(1 / (m:ℝ)))
        linarith
      have hpw : (1 - 1 / (m:ℝ)) ^ (m - 1) ≤ Real.exp (-(1 / (m:ℝ))) ^ (m - 1) :=
        pow_le_pow_left₀ hq0 hstep _
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ m)]; ring
      have hexp : Real.exp (-(1 / (m:ℝ))) ^ (m - 1) = Real.exp (-(1 - 1 / (m:ℝ))) := by
        rw [← Real.exp_nat_mul, hcast]
        congr 1
        field_simp
      rw [hexp] at hpw
      have hAE : (1 - 1 / (m:ℝ)) ^ (m - 1) * Real.exp (1 - 1 / (m:ℝ)) ≤ 1 := by
        have hpos : (0:ℝ) < Real.exp (1 - 1 / (m:ℝ)) := Real.exp_pos _
        calc (1 - 1 / (m:ℝ)) ^ (m - 1) * Real.exp (1 - 1 / (m:ℝ))
            ≤ Real.exp (-(1 - 1 / (m:ℝ))) * Real.exp (1 - 1 / (m:ℝ)) :=
              mul_le_mul_of_nonneg_right hpw hpos.le
          _ = 1 := by rw [← Real.exp_add]; simp
      exact aux_pow_mul_le (pow_nonneg hq0 _) hq34 hq1 hAE
  linarith

/-- The case `k = m − 1` of `binTail_succ_div_ge`. -/
theorem binTail_top_ge (m k : ℕ) (hk : 1 ≤ k) (hkm : k + 1 = m) :
    1 / 8 ≤ binTail m (k + 1) ((k : ℝ) / m) := by
  subst hkm
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hkk : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hm0 : (0:ℝ) < (k:ℝ) + 1 := by linarith
  have hsingle :
      binTail (k + 1) (k + 1) ((k : ℝ) / ((k:ℝ) + 1)) = ((k : ℝ) / ((k:ℝ) + 1)) ^ (k + 1) := by
    unfold binTail binPmf
    rw [Finset.Icc_self, Finset.sum_singleton]
    simp
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring] at *
  rw [hsingle]
  have hstep : ((k:ℝ) + 1) / k ≤ Real.exp (1 / k) := by
    have h : ((k:ℝ) + 1) / k = 1 / k + 1 := by field_simp; ring
    rw [h]
    exact Real.add_one_le_exp _
  have hcastpow : Real.exp (1 / (k:ℝ)) ^ k = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hBk : (((k:ℝ) + 1) / k) ^ k ≤ Real.exp 1 := by
    have h0 : (0:ℝ) ≤ ((k:ℝ) + 1) / k := by positivity
    calc (((k:ℝ) + 1) / k) ^ k ≤ Real.exp (1 / (k:ℝ)) ^ k := pow_le_pow_left₀ h0 hstep _
      _ = Real.exp 1 := hcastpow
  have hB2 : ((k:ℝ) + 1) / k ≤ 2 := by
    rw [div_le_iff₀ hk0]; linarith
  have hB : (((k:ℝ) + 1) / k) ^ (k + 1) ≤ 8 := by
    rw [pow_succ]
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h0 : (0:ℝ) ≤ (((k:ℝ) + 1) / k) ^ k := by positivity
    nlinarith [hBk, hB2, h0]
  have hprod : ((k:ℝ) / ((k:ℝ) + 1)) ^ (k + 1) * ((((k:ℝ) + 1) / k) ^ (k + 1)) = 1 := by
    rw [← mul_pow, show (k:ℝ) / ((k:ℝ) + 1) * (((k:ℝ) + 1) / k) = 1 by field_simp]
    simp
  have hnn : (0:ℝ) ≤ ((k:ℝ) / ((k:ℝ) + 1)) ^ (k + 1) := by positivity
  nlinarith [hprod, hB, hnn]

/-- The case `2 ≤ k ≤ m − 2` of `binTail_succ_div_ge`. -/
theorem binTail_mid_ge (m k : ℕ) (hk2 : 2 ≤ k) (hkm2 : k + 2 ≤ m) :
    1 / 8 ≤ binTail m (k + 1) ((k : ℝ) / m) := by
  have hk : 1 ≤ k := by omega
  have hkm : k < m := by omega
  have h1 := binTail_succ_ge_sq m k hk hkm
  have h2 := central_term_ge m k hk hkm
  have hK2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  have hMKc : ((k:ℝ) + 2) ≤ (m:ℝ) := by exact_mod_cast hkm2
  have hK0 : (0:ℝ) < (k:ℝ) := by linarith
  have hMK0 : (0:ℝ) < (m:ℝ) - (k:ℝ) := by linarith
  have hM0 : (0:ℝ) < (m:ℝ) := by linarith
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hden : (0:ℝ) < 2 * π * (k:ℝ) * ((m:ℝ) - (k:ℝ)) :=
    mul_pos (mul_pos (by positivity) hK0) hMK0
  have hu : (0:ℝ) ≤ (m:ℝ) / (2 * π * (k:ℝ) * ((m:ℝ) - (k:ℝ))) := (div_pos hM0 hden).le
  have hL : (0:ℝ) ≤ Real.sqrt ((m:ℝ) / (2 * π * (k:ℝ) * ((m:ℝ) - (k:ℝ)))) *
      Real.exp (-(1 / (12 * (k:ℝ))) - 1 / (12 * ((m:ℝ) - (k:ℝ)))) := by positivity
  have hsq := pow_le_pow_left₀ hL h2 2
  have hlhs : (Real.sqrt ((m:ℝ) / (2 * π * (k:ℝ) * ((m:ℝ) - (k:ℝ)))) *
      Real.exp (-(1 / (12 * (k:ℝ))) - 1 / (12 * ((m:ℝ) - (k:ℝ))))) ^ 2
      = (m:ℝ) / (2 * π * (k:ℝ) * ((m:ℝ) - (k:ℝ))) *
        Real.exp (2 * (-(1 / (12 * (k:ℝ))) - 1 / (12 * ((m:ℝ) - (k:ℝ))))) := by
    rw [mul_pow, Real.sq_sqrt hu, sq, ← Real.exp_add]
    ring_nf
  have hcoef : (0:ℝ) ≤ (k:ℝ) * ((m:ℝ) - (k:ℝ)) / (m:ℝ) :=
    div_nonneg (mul_nonneg hK0.le hMK0.le) hM0.le
  have hstep := mul_le_mul_of_nonneg_left hsq hcoef
  rw [hlhs] at hstep
  refine le_trans ?_ (le_trans hstep h1)
  have heq : ((k:ℝ) * ((m:ℝ) - (k:ℝ)) / (m:ℝ)) *
      ((m:ℝ) / (2 * π * (k:ℝ) * ((m:ℝ) - (k:ℝ))) *
        Real.exp (2 * (-(1 / (12 * (k:ℝ))) - 1 / (12 * ((m:ℝ) - (k:ℝ))))))
      = Real.exp (2 * (-(1 / (12 * (k:ℝ))) - 1 / (12 * ((m:ℝ) - (k:ℝ))))) / (2 * π) := by
    field_simp
  rw [heq]
  have hb1 : 1 / (12 * (k:ℝ)) ≤ 1 / 24 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hb2 : 1 / (12 * ((m:ℝ) - (k:ℝ))) ≤ 1 / 24 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hE : -(1/6 : ℝ) ≤ 2 * (-(1 / (12 * (k:ℝ))) - 1 / (12 * ((m:ℝ) - (k:ℝ)))) := by
    linarith
  have hexp : Real.exp (-(1/6:ℝ))
      ≤ Real.exp (2 * (-(1 / (12 * (k:ℝ))) - 1 / (12 * ((m:ℝ) - (k:ℝ))))) :=
    Real.exp_le_exp.2 hE
  have h56 : (5:ℝ)/6 ≤ Real.exp (-(1/6:ℝ)) := by
    have := Real.add_one_le_exp (-(1/6:ℝ)); linarith
  have hpi2 : π < 3.15 := Real.pi_lt_d2
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- `P[Bin(m,k/m) ≥ k+1] ≥ 1/8` for `1 ≤ k ≤ m − 1`. -/
theorem binTail_succ_div_ge (m k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    1 / 8 ≤ binTail m (k + 1) (k / m) := by
  by_cases hk1 : k = 1
  · subst hk1
    rw [show ((1:ℕ) : ℝ) / (m:ℝ) = 1 / (m:ℝ) by norm_num, show (1:ℕ) + 1 = 2 from rfl]
    exact binTail_two_ge m (by omega)
  · by_cases hkm1 : k + 1 = m
    · exact binTail_top_ge m k hk hkm1
    · exact binTail_mid_ge m k (by omega) (by omega)

/-- The binomial lemma: `P[Bin(m,p) ≥ m p] ≥ 1/8` for `1/m < p ≤ 1`. -/
theorem binTail_ceil_ge (m : ℕ) (hm : 1 ≤ m) {p : ℝ} (hp : 1 / m < p) (hp1 : p ≤ 1) :
    1 / 8 ≤ binTail m ⌈(m : ℝ) * p⌉₊ p := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hp0 : (0:ℝ) < p := lt_trans (by positivity) hp
  rcases eq_or_lt_of_le hp1 with rfl | hplt
  · rw [mul_one, Nat.ceil_natCast]
    unfold binTail binPmf
    rw [Finset.Icc_self, Finset.sum_singleton]
    simp
    norm_num
  · set k := ⌊(m : ℝ) * p⌋₊ with hkdef
    have hmp : (1:ℝ) < (m:ℝ) * p := by
      rw [div_lt_iff₀ hm0] at hp
      linarith [hp]
    have hmpm : (m:ℝ) * p < m := by nlinarith
    have hk1 : 1 ≤ k := Nat.le_floor (by push_cast; linarith)
    have hkm : k < m := by
      rw [hkdef, Nat.floor_lt (by positivity)]
      exact hmpm
    have hceil : ⌈(m : ℝ) * p⌉₊ ≤ k + 1 := Nat.ceil_le_floor_add_one _
    have hkp : (k:ℝ) / m ≤ p := by
      have := Nat.floor_le (by positivity : (0:ℝ) ≤ (m:ℝ) * p)
      rw [← hkdef] at this
      rw [div_le_iff₀ hm0]
      linarith
    have hk0 : (0:ℝ) ≤ (k:ℝ) / m := by positivity
    have hk1' : (k:ℝ) / m ≤ 1 := by
      rw [div_le_one hm0]
      exact_mod_cast hkm.le
    calc (1:ℝ) / 8 ≤ binTail m (k + 1) ((k:ℝ) / m) := binTail_succ_div_ge m k hk1 hkm
      _ ≤ binTail m (k + 1) p :=
          binTail_mono m (k + 1) (Set.mem_Icc.2 ⟨hk0, hk1'⟩)
            (Set.mem_Icc.2 ⟨hp0.le, hp1⟩) hkp
      _ ≤ binTail m ⌈(m : ℝ) * p⌉₊ p := by
          unfold binTail binPmf
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc_left hceil) ?_
          intro i _ _
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0.le _))
            (pow_nonneg (by linarith) _)

/-- The form used by the symmetrization lemma. -/
theorem binomial_bound (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ) (hm : 1 ≤ m)
    {B : Set X} (hB : MeasurableSet B) (hpB : 1 / m < μ.real B) :
    1 / 8 ≤ (sampleMeasure μ m).real {y | m * μ.real B ≤ count y B} := by
  rw [sampleMeasure_real_count_ge μ m hB ((m : ℝ) * μ.real B)]
  exact binTail_ceil_ge m hm hpB measureReal_le_one

end VCInequality
