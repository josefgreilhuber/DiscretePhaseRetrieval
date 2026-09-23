import DiscreteNorming.Defs
import DiscreteNorming.ComplexPoly
import VCInequality.RelativeVCInequality

/-!
# Claims C6, C7, C7': the random sample

* `sample_size_bound`: with `ε = √t/2`, `V = 36N` and `M = ⌊(3000 + 1200|log t|)N/t⌋`, the
  right-hand side of the VC inequality, `8 (2eM/V)^V exp(−Mε²/4)`, is at most `1/100`,
  provided `0 < t ≤ 1/8` (paper, p. 3–4; the hypothesis `t ≤ 1/8` is needed).
* `count_ge_of_not_bad`: off the bad event, every family set of measure `≥ t` contains at least
  `(t/2) M` sample points (paper: "ensures each set in `ℱ` contains at least `(t/2)M` points").
* the countable subfamily `ratFamily`: countable index, measurable sets, contained in the family
  of Lemma 2.2; `unif Ω` is a probability measure supported on `Ω`.
-/

open MeasureTheory Metric

namespace DiscreteNorming

/-! ### Numerical estimates used in `sample_size_bound` -/

/-- `log 3000 ≤ 8.01`. -/
private theorem log_3000_le : Real.log 3000 ≤ 8.01 := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he8 : (2980 : ℝ) ≤ Real.exp 8 := by
    have h : Real.exp 8 = Real.exp 1 ^ (8 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (2980 : ℝ) ≤ (2.7182818283 : ℝ) ^ (8 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (8 : ℕ) := by gcongr
  have he001 : (1.01 : ℝ) ≤ Real.exp 0.01 := by
    have := Real.add_one_le_exp (0.01 : ℝ); linarith
  have hmul : (3000 : ℝ) ≤ Real.exp 8.01 := by
    have h : Real.exp (8.01 : ℝ) = Real.exp 8 * Real.exp 0.01 := by
      rw [← Real.exp_add]; norm_num
    rw [h]; nlinarith [he8, he001]
  have := Real.log_le_log (by norm_num : (0:ℝ) < 3000) hmul
  rwa [Real.log_exp] at this

/-- `log 800 ≤ 6.94`. -/
private theorem log_800_le : Real.log 800 ≤ 6.94 := by
  have h1 : Real.log 800 ≤ Real.log 1024 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024:ℝ) = 2 ^ (10:ℕ) by norm_num, Real.log_pow]; norm_num
  have h3 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- `2.0794 ≤ log 8`. -/
private theorem log_8_ge : (2.0794 : ℝ) ≤ Real.log 8 := by
  have h2 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]; norm_num
  have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  linarith

/-- `4 log 2 ≤ log 18`. -/
private theorem log_18_ge : 4 * Real.log 2 ≤ Real.log 18 := by
  have h1 : Real.log 16 ≤ Real.log 18 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ (4:ℕ) by norm_num, Real.log_pow]; norm_num
  linarith

/-- The sample size is at least `y - 1` where `y = (3000 + 1200|log t|)N/t`. -/
private theorem sampleSize_ge {t : ℝ} (N : ℕ) :
    (3000 + 1200 * |Real.log t|) * N / t - 1 ≤ (sampleSize t N : ℝ) := by
  have h : (3000 + 1200 * |Real.log t|) * (N : ℝ) / t < (sampleSize t N : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- **Choice of the sample size** (arithmetic): for `0 < t ≤ 1/8`, `N ≥ 1`. -/
theorem sample_size_bound {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 8) {N : ℕ} (hN : 1 ≤ N) :
    8 * (Real.exp 1 * (2 * (sampleSize t N : ℝ)) / (36 * N : ℕ)) ^ (36 * N)
        * Real.exp (-((sampleSize t N : ℝ) * (Real.sqrt t / 2) ^ 2) / 4) ≤ 1 / 100 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ht1 : t < 1 := by linarith
  -- `L = |log t| = -log t ≥ log 8`
  have hL0 : (0 : ℝ) ≤ |Real.log t| := abs_nonneg _
  have hlogt : Real.log t < 0 := Real.log_neg ht0 ht1
  have hLeq : Real.log t = -|Real.log t| := by rw [abs_of_neg hlogt]; ring
  have hL : (2.0794 : ℝ) ≤ |Real.log t| := by
    have h1 : Real.log t ≤ Real.log (1 / 8) := Real.log_le_log ht0 ht
    have h2 : Real.log (1 / 8 : ℝ) = -Real.log 8 := by
      rw [Real.log_div one_ne_zero (by norm_num), Real.log_one]; ring
    have := log_8_ge
    rw [h2, hLeq] at h1
    linarith
  set L : ℝ := |Real.log t| with hLdef
  -- bounds on the sample size
  set M : ℕ := sampleSize t N with hMdef
  have hMub : (M : ℝ) ≤ (3000 + 1200 * L) * N / t :=
    Nat.floor_le (div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg N)) ht0.le)
  have hMlb : (3000 + 1200 * L) * N / t - 1 ≤ (M : ℝ) := sampleSize_ge N
  have hM18 : 18 * N ≤ M := by
    apply Nat.le_floor
    rw [le_div_iff₀ ht0]
    push_cast
    nlinarith [hL0, hNR, ht0, ht]
  have hMR : (18 : ℝ) * N ≤ (M : ℝ) := by exact_mod_cast hM18
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by linarith
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  -- key products
  have hMt : (M : ℝ) * t ≤ (3000 + 1200 * L) * (N : ℝ) := by
    rw [le_div_iff₀ ht0] at hMub; exact hMub
  have hMt2 : (3000 + 1200 * L) * (N : ℝ) - t ≤ (M : ℝ) * t := by
    have h : (3000 + 1200 * L) * (N : ℝ) / t ≤ (M : ℝ) + 1 := by linarith
    rw [div_le_iff₀ ht0] at h
    linarith
  have hMt3 : (2999 + 1200 * L) * (N : ℝ) ≤ (M : ℝ) * t := by nlinarith [hMt2, hNR, ht, ht0]
  -- rewrite the goal in exponential form
  have hcast : ((36 * N : ℕ) : ℝ) = 36 * (N : ℝ) := by push_cast; ring
  have hsq : (Real.sqrt t / 2) ^ 2 = t / 4 := by
    rw [div_pow, Real.sq_sqrt ht0.le]; norm_num
  rw [hcast, hsq]
  set B : ℝ := Real.exp 1 * (2 * (M : ℝ)) / (36 * (N : ℝ)) with hBdef
  have hB0 : 0 < B := by
    rw [hBdef]
    exact div_pos (mul_pos (Real.exp_pos 1) (by linarith)) (by linarith)
  have hpow : B ^ (36 * N) = Real.exp (((36 * N : ℕ) : ℝ) * Real.log B) := by
    rw [Real.exp_nat_mul, Real.exp_log hB0]
  rw [hpow, hcast, mul_assoc, ← Real.exp_add]
  -- bound `log B`
  have hn3 : (0 : ℝ) < 3000 + 1200 * L := by linarith
  have hn1 : (0 : ℝ) < Real.exp 1 * (3000 + 1200 * L) := mul_pos (Real.exp_pos 1) hn3
  have hn2 : (0 : ℝ) < 18 * t := by linarith
  have hB' : B ≤ Real.exp 1 * (3000 + 1200 * L) / (18 * t) := by
    rw [hBdef, div_le_div_iff₀ (by linarith : (0:ℝ) < 36 * (N:ℝ)) hn2]
    nlinarith [mul_le_mul_of_nonneg_left hMt (Real.exp_pos 1).le, Real.exp_pos 1]
  have hlogB'eq : Real.log (Real.exp 1 * (3000 + 1200 * L) / (18 * t))
      = 1 + Real.log (3000 + 1200 * L) - Real.log 18 - Real.log t := by
    rw [Real.log_div hn1.ne' hn2.ne', Real.log_mul (Real.exp_ne_zero 1) hn3.ne',
      Real.log_mul (by norm_num : (18:ℝ) ≠ 0) ht0.ne', Real.log_exp]
    ring
  have hlog3000L : Real.log (3000 + 1200 * L) ≤ 8.01 + 0.4 * L := by
    have hfac : (3000 : ℝ) + 1200 * L = 3000 * (1 + 0.4 * L) := by ring
    have hpos : (0 : ℝ) < 1 + 0.4 * L := by linarith
    have h1 : Real.log (1 + 0.4 * L) ≤ 0.4 * L := by
      have := Real.log_le_sub_one_of_pos hpos; linarith
    rw [hfac, Real.log_mul (by norm_num : (3000:ℝ) ≠ 0) hpos.ne']
    linarith [log_3000_le]
  have hlogB : Real.log B ≤ 6.2375 + 1.4 * L := by
    have h1 : Real.log B ≤ Real.log (Real.exp 1 * (3000 + 1200 * L) / (18 * t)) :=
      Real.log_le_log hB0 hB'
    rw [hlogB'eq] at h1
    have h2 := log_18_ge
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [hLeq] at h1
    linarith [hlog3000L]
  -- assemble
  have hA : 36 * (N : ℝ) * Real.log B ≤ 36 * (N : ℝ) * (6.2375 + 1.4 * L) :=
    mul_le_mul_of_nonneg_left hlogB (by positivity)
  have hbr : (N : ℝ) * (37.1125 - 24.6 * L) ≤ -14.04 := by
    nlinarith [hL, hNR]
  have harg : 36 * (N : ℝ) * Real.log B + -((M : ℝ) * (t / 4)) / 4 ≤ -Real.log 800 := by
    have h1 : 36 * (N : ℝ) * Real.log B + -((M : ℝ) * (t / 4)) / 4
        ≤ (N : ℝ) * (37.1125 - 24.6 * L) := by linarith [hA, hMt3]
    linarith [hbr, log_800_le]
  have hexp := Real.exp_le_exp.mpr harg
  have h800 : Real.exp (-Real.log 800) = 1 / 800 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 800)]; norm_num
  linarith [hexp, h800]

theorem sampleSize_pos {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 8) {N : ℕ} (hN : 1 ≤ N) :
    36 * N ≤ 2 * sampleSize t N := by
  have hL : (0 : ℝ) ≤ |Real.log t| := abs_nonneg _
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have key : 18 * N ≤ sampleSize t N := by
    apply Nat.le_floor
    rw [le_div_iff₀ ht0]
    push_cast
    nlinarith [hL, hNR, ht0, ht]
  omega

theorem sampleSize_le {t : ℝ} (ht0 : 0 < t) (N : ℕ) :
    (sampleSize t N : ℝ) ≤ (3000 + 1200 * |Real.log t|) * N / t := by
  apply Nat.floor_le
  have : (0 : ℝ) ≤ |Real.log t| := abs_nonneg _
  positivity

/-- Off the bad event of the VC inequality with `ε = √t/2`, a set of probability `≥ t` receives
at least `(t/2) M` sample points. -/
theorem count_ge_of_not_bad {X : Type*} [MeasurableSpace X] (μ : Measure X) {ι : Type*}
    (A : ι → Set X) {M : ℕ} {t : ℝ} (ht0 : 0 < t) {x : Fin M → X}
    (hx : x ∉ VCInequality.badEvent μ A M (Real.sqrt t / 2)) (i : ι) (hA : t ≤ μ.real (A i)) :
    t / 2 * M ≤ VCInequality.count x (A i) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp
  -- from `hx`, the relative deviation of `A i` is at most `√t / 2`
  have hdev : VCInequality.relDev μ x (A i) ≤ Real.sqrt t / 2 := by
    simp only [VCInequality.badEvent, Set.mem_setOf_eq, not_exists, not_lt] at hx
    exact hx i
  set P : ℝ := μ.real (A i) with hP
  have hP0 : 0 < P := lt_of_lt_of_le ht0 hA
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP0
  have hsPsq : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0.le
  have hst : Real.sqrt t ≤ Real.sqrt P := Real.sqrt_le_sqrt hA
  -- unfold the relative deviation
  have h1 : (P - VCInequality.empFreq x (A i)) / Real.sqrt P ≤ Real.sqrt t / 2 := hdev
  have h2 : P - VCInequality.empFreq x (A i) ≤ Real.sqrt t / 2 * Real.sqrt P := by
    rw [div_le_iff₀ hsP] at h1
    linarith
  have h3 : P / 2 ≤ VCInequality.empFreq x (A i) := by
    nlinarith [hst, hsP, hsPsq]
  have h4 : t / 2 ≤ VCInequality.empFreq x (A i) := by linarith
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [VCInequality.empFreq, le_div_iff₀ hMR] at h4
  exact h4

instance instCountableRatIndex (N : ℕ) : Countable (RatIndex N) := by
  infer_instance

theorem isProbabilityMeasure_unif {d : ℕ} {Ω : Set (Pt d)} (hb : Bornology.IsBounded Ω)
    (hpos : 0 < volume Ω) : IsProbabilityMeasure (unif Ω) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite hpos.ne' hb.measure_lt_top.ne

/-- `unif Ω` is supported on `Ω`: `unif Ω (Ωᶜ) = 0`. -/
theorem unif_compl {d : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω) : unif Ω Ωᶜ = 0 := by
  rw [unif, ProbabilityTheory.cond_apply hΩ, Set.inter_compl_self, measure_empty, mul_zero]

/-- `unif Ω A = |A ∩ Ω| / |Ω|`. -/
theorem unif_real_apply {d : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) (A : Set (Pt d)) :
    (unif Ω).real A = vol (Ω ∩ A) / vol Ω := by
  rw [measureReal_def, unif, ProbabilityTheory.cond_apply hΩ, ENNReal.toReal_mul,
    ENNReal.toReal_inv, vol, vol, measureReal_def, measureReal_def, div_eq_inv_mul]

theorem measurableSet_ratFamily {d N : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (φ : Fin N → PolyFock.Fock.P d) (i : RatIndex N) :
    MeasurableSet (ratFamily Ω φ i) := by
  change MeasurableSet (Ω ∩ {x | ((i.2.2 : ℚ) : ℝ) ≤ |diff (ratComb φ i.1) (ratComb φ i.2.1) x|})
  exact hΩ.inter (measurableSet_le measurable_const
    ((continuous_diff _ _).measurable.abs))

theorem ratFamily_mem_superlevelFamily {d N : ℕ} (Ω : Set (Pt d))
    {𝒱 : Submodule ℂ (PolyFock.Fock.P d)} {φ : Fin N → PolyFock.Fock.P d}
    (hφ : ∀ j, φ j ∈ 𝒱) (i : RatIndex N) : ratFamily Ω φ i ∈ superlevelFamily Ω 𝒱 :=
  ⟨ratComb φ i.1, comb_mem hφ _, ratComb φ i.2.1, comb_mem hφ _, ((i.2.2 : ℚ) : ℝ),
    by exact_mod_cast i.2.2.2, rfl⟩

end DiscreteNorming
