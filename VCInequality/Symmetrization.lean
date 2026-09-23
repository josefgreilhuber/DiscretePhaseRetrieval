import VCInequality.Defs
import VCInequality.Swap

/-!
# Symmetrization (ghost sample)

Let `E = badEvent μ A m ε` and `E' = symEvent A m ε`. Assume `m ε² ≥ 1` and the binomial
lower bound `hbin`: for every measurable `B` with `μ B > 1/m`, the count of an `m`-sample in `B`
is at least `m · μ B` with probability at least `c`. Then `μ^{⊗m} E ≤ c⁻¹ · (μ⊗μ)^{⊗m} E'`.

Proof sketch (Cortes–Greenberg–Mohri Lemma 2, simplified because no `τ`, no `1/m` regulariser):
work on `(Fin m → X) × (Fin m → X)` with the product measure and the intermediate event
`Ẽ = {(x,y) | ∃ i, ε < relDev μ x (A i) ∧ μ (A i) ≤ empFreq y (A i)}`.
* `Ẽ ⊆ (E' pulled back)`: with `R = μ (A i)`, `a = empFreq x`, `b = empFreq y`, we have
  `a < R − ε√R` and `b ≥ R`. The function `F(u,v) = (u − v)/√((u+v)/2)` is increasing in `u` and
  decreasing in `v` on `u, v ≥ 0`, `u + v > 0`, hence
  `F(b,a) ≥ F(R, R − ε√R) = ε√R / √(R − ε√R/2) > ε`.
* `(ν.prod ν) Ẽ ≥ c · ν E` by `Measure.prod_apply` and `lintegral_mono`: for `x ∈ E` with
  witness `i`, `R > ε√R` forces `R > ε² ≥ 1/m`, so the section `Ẽ_x ⊇ {y | m R ≤ count y (A i)}`
  has measure `≥ c` by `hbin`. The witness need not be chosen measurably.
* Transport to `doubleMeasure` via `prod_sampleMeasure_eq_map`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace VCInequality

variable {X : Type*} [MeasurableSpace X]

theorem measurable_count {m : ℕ} {A : Set X} (hA : MeasurableSet A) :
    Measurable fun x : Fin m → X ↦ count x A := by
  classical
  have h : (fun x : Fin m → X ↦ count x A)
      = fun x ↦ ∑ i : Fin m, if x i ∈ A then 1 else 0 := by
    funext x
    simp only [count, Finset.card_filter]
  rw [h]
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  exact Measurable.ite (hA.preimage (measurable_pi_apply i)) measurable_const measurable_const

/-- The empirical frequency of a measurable set is a measurable function of the sample. -/
theorem measurable_empFreq {m : ℕ} {A : Set X} (hA : MeasurableSet A) :
    Measurable fun x : Fin m → X ↦ empFreq x A := by
  unfold empFreq
  exact (measurable_from_top.comp (measurable_count hA)).div measurable_const

/-- The relative deviation of a measurable set is a measurable function of the sample. -/
theorem measurable_relDev (μ : Measure X) {m : ℕ} {A : Set X} (hA : MeasurableSet A) :
    Measurable fun x : Fin m → X ↦ relDev μ x A := by
  unfold relDev
  exact (measurable_const.sub (measurable_empFreq hA)).div measurable_const

theorem measurable_fstSample {m : ℕ} : Measurable (fstSample (X := X) (m := m)) :=
  measurable_pi_iff.2 fun i ↦ measurable_fst.comp (measurable_pi_apply i)

theorem measurable_sndSample {m : ℕ} : Measurable (sndSample (X := X) (m := m)) :=
  measurable_pi_iff.2 fun i ↦ measurable_snd.comp (measurable_pi_apply i)

/-- The symmetrized deviation of a measurable set is measurable in the double sample. -/
theorem measurable_symDev {m : ℕ} {A : Set X} (hA : MeasurableSet A) :
    Measurable fun z : Fin m → X × X ↦ symDev z A := by
  unfold symDev
  have h1 : Measurable fun z : Fin m → X × X ↦ empFreq (fstSample z) A :=
    (measurable_empFreq hA).comp measurable_fstSample
  have h2 : Measurable fun z : Fin m → X × X ↦ empFreq (sndSample z) A :=
    (measurable_empFreq hA).comp measurable_sndSample
  exact (h2.sub h1).div ((h1.add h2).div measurable_const).sqrt

theorem measurableSet_badEvent (μ : Measure X) {ι : Type*} [Countable ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (m : ℕ) (ε : ℝ) :
    MeasurableSet (badEvent μ A m ε) := by
  rw [badEvent, Set.setOf_exists]
  exact MeasurableSet.iUnion fun i ↦
    measurableSet_lt measurable_const (measurable_relDev μ (hA i))

theorem measurableSet_symEvent {ι : Type*} [Countable ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (m : ℕ) (ε : ℝ) :
    MeasurableSet (symEvent A m ε) := by
  rw [symEvent, Set.setOf_exists]
  exact MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const (measurable_symDev (hA i))

/-- Key deterministic step of the symmetrization argument: if the relative deviation of the
empirical frequency `a` from `R` exceeds `ε` and the ghost frequency `b` is at least `R`, then
the symmetrized deviation of the pair `(a, b)` exceeds `ε`. -/
theorem key_step {R a b ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (h1 : ε < (R - a) / Real.sqrt R) (h2 : R ≤ b) :
    ε < (b - a) / Real.sqrt ((a + b) / 2) := by
  -- Lean's conventions `x / 0 = 0`, `√x = 0` for `x ≤ 0` force `R > 0`.
  have hR : 0 < R := by
    rcases lt_trichotomy R 0 with h | h | h
    · rw [Real.sqrt_eq_zero_of_nonpos h.le, div_zero] at h1; linarith
    · rw [h, Real.sqrt_zero, div_zero] at h1; linarith
    · exact h
  set s := Real.sqrt R with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hR
  have hsq : s ^ 2 = R := Real.sq_sqrt hR.le
  have ha' : ε * s < R - a := (lt_div_iff₀ hs0).1 h1
  have hεs : ε < s := by nlinarith
  have hb0 : 0 < b := by nlinarith
  have hq : 0 < (a + b) / 2 := by linarith
  have hsq2 : 0 < Real.sqrt ((a + b) / 2) := Real.sqrt_pos.2 hq
  have hba : 0 < b - a := by nlinarith
  -- the squared inequality `ε² (a+b)/2 < (b-a)²`
  have hkey : ε ^ 2 * ((a + b) / 2) < (b - a) ^ 2 := by
    have ht : (0 : ℝ) ≤ b - s ^ 2 := by rw [hsq]; linarith
    have hr : (0 : ℝ) < s ^ 2 - ε * s - a := by rw [hsq]; linarith
    have hs2 : (0 : ℝ) < 2 * s - ε / 2 := by linarith
    have hexp : (b - a) ^ 2 - ε ^ 2 * ((a + b) / 2)
        = (s ^ 2 - ε * s - a) ^ 2 + (b - s ^ 2) ^ 2
          + 2 * (ε * s) * (s ^ 2 - ε * s - a) + 2 * (s ^ 2 - ε * s - a) * (b - s ^ 2)
          + ε * (b - s ^ 2) * (2 * s - ε / 2) + ε ^ 3 * s / 2
          + ε ^ 2 * (s ^ 2 - ε * s - a) / 2 := by ring
    have t1 : (0 : ℝ) ≤ (s ^ 2 - ε * s - a) ^ 2 := sq_nonneg _
    have t2 : (0 : ℝ) ≤ (b - s ^ 2) ^ 2 := sq_nonneg _
    have t3 : (0 : ℝ) < 2 * (ε * s) * (s ^ 2 - ε * s - a) := by positivity
    have t4 : (0 : ℝ) ≤ 2 * (s ^ 2 - ε * s - a) * (b - s ^ 2) := by positivity
    have t5 : (0 : ℝ) ≤ ε * (b - s ^ 2) * (2 * s - ε / 2) := by positivity
    have t6 : (0 : ℝ) < ε ^ 3 * s / 2 := by positivity
    have t7 : (0 : ℝ) < ε ^ 2 * (s ^ 2 - ε * s - a) / 2 := by positivity
    linarith
  rw [lt_div_iff₀ hsq2]
  have hrw : ε * Real.sqrt ((a + b) / 2) = Real.sqrt (ε ^ 2 * ((a + b) / 2)) := by
    rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]
  rw [hrw]
  calc Real.sqrt (ε ^ 2 * ((a + b) / 2)) < Real.sqrt ((b - a) ^ 2) :=
        Real.sqrt_lt_sqrt (by positivity) hkey
    _ = b - a := Real.sqrt_sq hba.le

/-- Symmetrization lemma, parametric in the binomial constant `c`. -/
theorem symmetrization (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Countable ι]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hmε : 1 ≤ m * ε ^ 2) {c : ℝ} (hc : 0 < c)
    (hbin : ∀ B : Set X, MeasurableSet B → 1 / m < μ.real B →
      c ≤ (sampleMeasure μ m).real {y | m * μ.real B ≤ count y B}) :
    (sampleMeasure μ m).real (badEvent μ A m ε)
      ≤ c⁻¹ * (doubleMeasure μ m).real (symEvent A m ε) := by
  classical
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; norm_num at hmε
    · exact h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfreq_nonneg : ∀ (x : Fin m → X) (B : Set X), 0 ≤ empFreq x B := fun _ _ ↦
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- measurable building blocks on the product space `(Fin m → X) × (Fin m → X)`
  have hf1 : ∀ i, Measurable fun p : (Fin m → X) × (Fin m → X) ↦ relDev μ p.1 (A i) :=
    fun i ↦ (measurable_relDev μ (hA i)).comp measurable_fst
  have hf2 : ∀ i, Measurable fun p : (Fin m → X) × (Fin m → X) ↦ empFreq p.1 (A i) :=
    fun i ↦ (measurable_empFreq (hA i)).comp measurable_fst
  have hf3 : ∀ i, Measurable fun p : (Fin m → X) × (Fin m → X) ↦ empFreq p.2 (A i) :=
    fun i ↦ (measurable_empFreq (hA i)).comp measurable_snd
  -- the symmetrized event, seen on the product space
  have hE2meas : MeasurableSet {p : (Fin m → X) × (Fin m → X) | ∃ i,
      ε < (empFreq p.2 (A i) - empFreq p.1 (A i)) /
        Real.sqrt ((empFreq p.1 (A i) + empFreq p.2 (A i)) / 2)} := by
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const
      (((hf3 i).sub (hf2 i)).div (((hf2 i).add (hf3 i)).div measurable_const).sqrt)
  -- the intermediate event `Ẽ`
  have hEtmeas : MeasurableSet {p : (Fin m → X) × (Fin m → X) | ∃ i,
      ε < relDev μ p.1 (A i) ∧ μ.real (A i) ≤ empFreq p.2 (A i)} := by
    rw [Set.setOf_exists]
    refine MeasurableSet.iUnion fun i ↦ ?_
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const (hf1 i)).inter
      (measurableSet_le measurable_const (hf3 i))
  have hsub : {p : (Fin m → X) × (Fin m → X) | ∃ i,
      ε < relDev μ p.1 (A i) ∧ μ.real (A i) ≤ empFreq p.2 (A i)}
      ⊆ {p : (Fin m → X) × (Fin m → X) | ∃ i,
      ε < (empFreq p.2 (A i) - empFreq p.1 (A i)) /
        Real.sqrt ((empFreq p.1 (A i) + empFreq p.2 (A i)) / 2)} := by
    rintro ⟨x, y⟩ ⟨i, hi, hb⟩
    exact ⟨i, key_step (hfreq_nonneg x (A i)) hε hi hb⟩
  -- transport the symmetrized event to the double-sample measure
  have hg : Measurable (fun z : Fin m → X × X ↦ (fstSample z, sndSample z)) :=
    measurable_fstSample.prodMk measurable_sndSample
  have hmapeq : ((sampleMeasure μ m).prod (sampleMeasure μ m))
      {p : (Fin m → X) × (Fin m → X) | ∃ i,
        ε < (empFreq p.2 (A i) - empFreq p.1 (A i)) /
          Real.sqrt ((empFreq p.1 (A i) + empFreq p.2 (A i)) / 2)}
      = (doubleMeasure μ m) (symEvent A m ε) := by
    rw [prod_sampleMeasure_eq_map μ, Measure.map_apply hg hE2meas]
    rfl
  -- lower bound `(ν ⊗ ν) Ẽ ≥ c · ν E`
  have hEmeas : MeasurableSet (badEvent μ A m ε) := measurableSet_badEvent μ hA m ε
  have hlow : ENNReal.ofReal c * (sampleMeasure μ m) (badEvent μ A m ε)
      ≤ ((sampleMeasure μ m).prod (sampleMeasure μ m))
        {p : (Fin m → X) × (Fin m → X) | ∃ i,
          ε < relDev μ p.1 (A i) ∧ μ.real (A i) ≤ empFreq p.2 (A i)} := by
    rw [Measure.prod_apply hEtmeas, ← lintegral_indicator_const hEmeas (ENNReal.ofReal c)]
    refine lintegral_mono fun x ↦ ?_
    by_cases hx : x ∈ badEvent μ A m ε
    · rw [Set.indicator_of_mem hx]
      obtain ⟨i, hi⟩ := hx
      set R := μ.real (A i) with hRdef
      have hR0 : 0 ≤ R := measureReal_nonneg
      have hR : 0 < R := by
        rcases hR0.lt_or_eq with h | h
        · exact h
        · exfalso
          rw [relDev, ← hRdef, ← h, Real.sqrt_zero, div_zero] at hi
          linarith
      have hs0 : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
      have hsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0
      have hlt : ε * Real.sqrt R < R - empFreq x (A i) := by
        rw [relDev, ← hRdef] at hi
        exact (lt_div_iff₀ hs0).1 hi
      have hεs : ε < Real.sqrt R := by nlinarith [hfreq_nonneg x (A i)]
      have hε2 : ε ^ 2 < R := by nlinarith
      have hinvm : 1 / (m : ℝ) ≤ ε ^ 2 := by
        rw [div_le_iff₀ hmR]; nlinarith
      have hbnd := hbin (A i) (hA i) (by rw [← hRdef]; linarith)
      -- the section of `Ẽ` over `x` contains the binomial event
      have hsubsec : {y : Fin m → X | (m : ℝ) * R ≤ (count y (A i) : ℝ)}
          ⊆ Prod.mk x ⁻¹' {p : (Fin m → X) × (Fin m → X) | ∃ i,
            ε < relDev μ p.1 (A i) ∧ μ.real (A i) ≤ empFreq p.2 (A i)} := by
        intro y hy
        refine ⟨i, ?_, ?_⟩
        · rw [relDev, ← hRdef]; exact (lt_div_iff₀ hs0).2 hlt
        · rw [← hRdef, empFreq, le_div_iff₀ hmR, mul_comm]
          exact hy
      calc ENNReal.ofReal c
          ≤ (sampleMeasure μ m) {y : Fin m → X | (m : ℝ) * R ≤ (count y (A i) : ℝ)} :=
            ENNReal.ofReal_le_of_le_toReal hbnd
        _ ≤ _ := measure_mono hsubsec
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  -- conclude
  have hfinal : ENNReal.ofReal c * (sampleMeasure μ m) (badEvent μ A m ε)
      ≤ (doubleMeasure μ m) (symEvent A m ε) := by
    rw [← hmapeq]
    exact hlow.trans (measure_mono hsub)
  rw [le_inv_mul_iff₀ hc]
  have h := ENNReal.toReal_mono (measure_ne_top (doubleMeasure μ m) (symEvent A m ε)) hfinal
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at h

end VCInequality
