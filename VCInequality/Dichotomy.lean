import VCInequality.Defs
import VCInequality.Rademacher

/-!
# Union bound over dichotomies

For a fixed double sample `z`, the symmetrized deviation of `swap σ z` on a set `A` depends on `A`
only through the trace of `A` on the `2m` points of `z`, and equals
`(∑ i, ± d i) / (m √(T / (2m)))` with `d i = 1[(z i).2 ∈ A] − 1[(z i).1 ∈ A]` and
`T = ∑ i, (1[(z i).1 ∈ A] + 1[(z i).2 ∈ A])`, so `ε < symDev (swap σ z) A` iff
`ε √(m T / 2) < ∑ i, ± d i`. There are at most `G` traces (growth bound on `2m` points, transported
along `Fin m ⊕ Fin m ≃ Fin (2m)`), each contributing at most `exp(−m ε²/4)` by `rademacher_tail`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace VCInequality

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
open scoped Classical in
/-- The empirical count, written as a sum of indicators. -/
private lemma empFreq_eq_sum {m : ℕ} (x : Fin m → X) (A : Set X) :
    empFreq x A = (∑ i, if x i ∈ A then (1 : ℝ) else 0) / m := by
  rw [empFreq, count]
  congr 1
  rw [← Finset.natCast_card_filter]

open scoped Classical in
/-- The trace of a set `A` on the double sample `z`: at each index it records membership of the
first and of the second point. -/
private noncomputable def traceOf {m : ℕ} (z : Fin m → X × X) (A : Set X) : Fin m → Bool × Bool :=
  fun i ↦ (decide ((z i).1 ∈ A), decide ((z i).2 ∈ A))

/-- The signed difference vector attached to a trace. -/
private def dvec {m : ℕ} (v : Fin m → Bool × Bool) (i : Fin m) : ℝ :=
  (if (v i).2 then 1 else 0) - (if (v i).1 then 1 else 0)

/-- The total mass attached to a trace. -/
private def tTot {m : ℕ} (v : Fin m → Bool × Bool) : ℝ :=
  ∑ i, ((if (v i).1 then (1 : ℝ) else 0) + (if (v i).2 then 1 else 0))

private lemma tTot_nonneg {m : ℕ} (v : Fin m → Bool × Bool) : 0 ≤ tTot v := by
  apply Finset.sum_nonneg
  intro i _
  positivity

private lemma sq_dvec_le {m : ℕ} (v : Fin m → Bool × Bool) : ∑ i, (dvec v i) ^ 2 ≤ tTot v := by
  apply Finset.sum_le_sum
  intro i _
  rw [dvec]
  cases h1 : (v i).1 <;> cases h2 : (v i).2 <;> norm_num

omit [MeasurableSpace X] in
open scoped Classical in
private lemma dvec_traceOf {m : ℕ} (z : Fin m → X × X) (A : Set X) (i : Fin m) :
    dvec (traceOf z A) i =
      (if (z i).2 ∈ A then (1 : ℝ) else 0) - (if (z i).1 ∈ A then 1 else 0) := by
  simp [dvec, traceOf]

omit [MeasurableSpace X] in
open scoped Classical in
private lemma tTot_traceOf {m : ℕ} (z : Fin m → X × X) (A : Set X) :
    tTot (traceOf z A) =
      ∑ i, ((if (z i).1 ∈ A then (1 : ℝ) else 0) + (if (z i).2 ∈ A then 1 else 0)) := by
  simp [tTot, traceOf]

omit [MeasurableSpace X] in
open scoped Classical in
private lemma empFreq_fst_swap {m : ℕ} (z : Fin m → X × X) (A : Set X) (σ : Fin m → Bool) :
    empFreq (fstSample (swap σ z)) A
      = (∑ i, if σ i then (if (z i).2 ∈ A then (1 : ℝ) else 0)
          else (if (z i).1 ∈ A then (1 : ℝ) else 0)) / m := by
  rw [empFreq_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases h : σ i <;> simp [fstSample, swap, h]

omit [MeasurableSpace X] in
open scoped Classical in
private lemma empFreq_snd_swap {m : ℕ} (z : Fin m → X × X) (A : Set X) (σ : Fin m → Bool) :
    empFreq (sndSample (swap σ z)) A
      = (∑ i, if σ i then (if (z i).1 ∈ A then (1 : ℝ) else 0)
          else (if (z i).2 ∈ A then (1 : ℝ) else 0)) / m := by
  rw [empFreq_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases h : σ i <;> simp [sndSample, swap, h]

omit [MeasurableSpace X] in
/-- The symmetrized deviation of `swap σ z` on `A` only depends on the trace of `A`. -/
private lemma symDev_swap_eq {m : ℕ} (z : Fin m → X × X) (A : Set X) (σ : Fin m → Bool) :
    symDev (swap σ z) A
      = ((∑ i, if σ i then -(dvec (traceOf z A) i) else dvec (traceOf z A) i) / m)
        / Real.sqrt (tTot (traceOf z A) / m / 2) := by
  classical
  have hnum : empFreq (sndSample (swap σ z)) A - empFreq (fstSample (swap σ z)) A
      = (∑ i, if σ i then -(dvec (traceOf z A) i) else dvec (traceOf z A) i) / m := by
    rw [empFreq_fst_swap, empFreq_snd_swap, ← sub_div]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [dvec_traceOf]
    cases h : σ i <;> simp
  have hden : empFreq (fstSample (swap σ z)) A + empFreq (sndSample (swap σ z)) A
      = tTot (traceOf z A) / m := by
    rw [empFreq_fst_swap, empFreq_snd_swap, ← add_div, tTot_traceOf]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    cases h : σ i <;> simp [add_comm]
  rw [symDev, hnum, hden]

private lemma dvec_eq_zero_of_tTot_eq_zero {m : ℕ} {v : Fin m → Bool × Bool} (h : tTot v = 0)
    (i : Fin m) : dvec v i = 0 := by
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      ((if (v j).1 then (1 : ℝ) else 0) + (if (v j).2 then 1 else 0)) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 h
    intro j _
    positivity
  have hi := hz i (Finset.mem_univ i)
  revert hi
  rw [dvec]
  cases h1 : (v i).1 <;> cases h2 : (v i).2 <;> norm_num

omit [MeasurableSpace X] in
/-- The bad event for a single set, rewritten as a Rademacher tail event. -/
private lemma symDev_lt_iff {m : ℕ} (hm : 0 < m) (z : Fin m → X × X) (A : Set X)
    {ε : ℝ} (hε : 0 < ε) (σ : Fin m → Bool) :
    ε < symDev (swap σ z) A ↔
      ε * Real.sqrt (m * tTot (traceOf z A) / 2)
        < ∑ i, if σ i then -(dvec (traceOf z A) i) else dvec (traceOf z A) i := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set v := traceOf z A with hv
  rcases eq_or_lt_of_le (tTot_nonneg v) with hT | hT
  · -- degenerate case `T = 0`: both sides are false
    have hd : ∀ i, dvec v i = 0 := fun i ↦ dvec_eq_zero_of_tTot_eq_zero hT.symm i
    have hsum : (∑ i, if σ i then -(dvec v i) else dvec v i) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [hd i]
      simp
    rw [symDev_swap_eq, ← hv, hsum, ← hT]
    simp only [zero_div, Real.sqrt_zero, div_zero, mul_zero, lt_self_iff_false, iff_false,
      not_lt, ge_iff_le]
    exact hε.le
  · have hc : 0 < Real.sqrt (tTot v / m / 2) := Real.sqrt_pos.2 (by positivity)
    have hcm : Real.sqrt (tTot v / m / 2) * m = Real.sqrt (m * tTot v / 2) := by
      rw [show (m : ℝ) * tTot v / 2 = (tTot v / m / 2) * ((m : ℝ)) ^ 2 by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hm0.le]
    rw [symDev_swap_eq, ← hv, lt_div_iff₀ hc, lt_div_iff₀ hm0, mul_assoc, hcm]

omit [MeasurableSpace X] in
open scoped Classical in
/-- The number of traces realised on the double sample `z` is at most the growth bound on the
`2m` points of `z`. -/
private lemma ncard_traceOf_image_le {ι : Type*} {m : ℕ} (A : ι → Set X) {G : ℝ}
    (hG : IsGrowthBound (Set.range A) (2 * m) G) (z : Fin m → X × X) :
    ((traceOf z '' Set.range A).ncard : ℝ) ≤ G := by
  set j1 : Fin m → Fin (2 * m) := fun i ↦ ⟨(i : ℕ), by have := i.isLt; omega⟩ with hj1
  set j2 : Fin m → Fin (2 * m) := fun i ↦ ⟨(i : ℕ) + m, by have := i.isLt; omega⟩ with hj2
  set x : Fin (2 * m) → X := fun j ↦ if h : (j : ℕ) < m then (z ⟨j, h⟩).1
      else (z ⟨(j : ℕ) - m, by have := j.isLt; omega⟩).2 with hxd
  have hx1 : ∀ i, x (j1 i) = (z i).1 := by
    intro i
    simp [hxd, hj1, i.isLt]
  have hx2 : ∀ i, x (j2 i) = (z i).2 := by
    intro i
    have h : ¬ ((i : ℕ) + m < m) := by omega
    simp [hxd, hj2, h]
  set F : Set (Fin (2 * m)) → (Fin m → Bool × Bool) :=
    fun S ↦ fun i ↦ (decide (j1 i ∈ S), decide (j2 i ∈ S)) with hFd
  have hcomp : (fun A' : Set X ↦ F {j | x j ∈ A'}) = traceOf z := by
    funext A' i
    simp [hFd, traceOf, hx1, hx2]
  have himg : traceOf z '' Set.range A
      = F '' ((fun A' ↦ {j | x j ∈ A'}) '' Set.range A) := by
    rw [Set.image_image, hcomp]
  have hle : (traceOf z '' Set.range A).ncard
      ≤ ((fun A' ↦ {j | x j ∈ A'}) '' Set.range A).ncard := by
    rw [himg]
    exact Set.ncard_image_le (Set.toFinite _)
  exact le_trans (by exact_mod_cast hle) (hG x)

/-- For every double sample `z`, the fraction of swaps `σ` for which `swap σ z` lies in the
symmetrized bad event is at most `G · exp(−m ε² / 4)`. -/
theorem swap_avg_le {ι : Type*} (A : ι → Set X) (m : ℕ) {G : ℝ}
    (hG : IsGrowthBound (Set.range A) (2 * m) G) {ε : ℝ} (hε : 0 < ε) (z : Fin m → X × X) :
    (∑ σ : Fin m → Bool, (symEvent A m ε).indicator (fun _ ↦ (1 : ℝ)) (swap σ z)) / 2 ^ m
      ≤ G * Real.exp (-(m * ε ^ 2) / 4) := by
  classical
  have hG0 : (0 : ℝ) ≤ G :=
    le_trans (Nat.cast_nonneg _) (ncard_traceOf_image_le A hG z)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- with no sample points every empirical frequency, hence every deviation, vanishes
    have h0 : ∀ σ : Fin 0 → Bool,
        (symEvent A 0 ε).indicator (fun _ ↦ (1 : ℝ)) (swap σ z) = 0 := by
      intro σ
      apply Set.indicator_of_notMem
      rintro ⟨i, hi⟩
      rw [symDev] at hi
      simp [empFreq] at hi
      linarith
    simp only [h0, Finset.sum_const_zero, zero_div]
    exact mul_nonneg hG0 (Real.exp_pos _).le
  · -- the realised traces
    set Tr : Finset (Fin m → Bool × Bool) :=
      (Set.toFinite (traceOf z '' Set.range A)).toFinset with hTr
    -- the Rademacher tail event attached to a trace
    set E : (Fin m → Bool × Bool) → Set (Fin m → Bool) := fun v ↦
      {σ | ε * Real.sqrt (m * tTot v / 2) < ∑ i, if σ i then -(dvec v i) else dvec v i} with hE
    have hnn : ∀ (v : Fin m → Bool × Bool) (σ : Fin m → Bool),
        0 ≤ (E v).indicator (fun _ ↦ (1 : ℝ)) σ := fun v σ ↦
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one) σ
    have key : ∀ σ : Fin m → Bool,
        (symEvent A m ε).indicator (fun _ ↦ (1 : ℝ)) (swap σ z)
          ≤ ∑ v ∈ Tr, (E v).indicator (fun _ ↦ (1 : ℝ)) σ := by
      intro σ
      by_cases hσ : swap σ z ∈ symEvent A m ε
      · rw [Set.indicator_of_mem hσ]
        obtain ⟨i, hi⟩ := hσ
        have hmem : traceOf z (A i) ∈ Tr := by
          rw [hTr, Set.Finite.mem_toFinset]
          exact ⟨A i, ⟨i, rfl⟩, rfl⟩
        have hσE : σ ∈ E (traceOf z (A i)) := (symDev_lt_iff hm z (A i) hε σ).1 hi
        calc (1 : ℝ) = (E (traceOf z (A i))).indicator (fun _ ↦ (1 : ℝ)) σ := by
              rw [Set.indicator_of_mem hσE]
          _ ≤ ∑ v ∈ Tr, (E v).indicator (fun _ ↦ (1 : ℝ)) σ :=
              Finset.single_le_sum (fun v _ ↦ hnn v σ) hmem
      · rw [Set.indicator_of_notMem hσ]
        exact Finset.sum_nonneg fun v _ ↦ hnn v σ
    have step1 :
        (∑ σ : Fin m → Bool, (symEvent A m ε).indicator (fun _ ↦ (1 : ℝ)) (swap σ z)) / 2 ^ m
          ≤ (∑ σ : Fin m → Bool, ∑ v ∈ Tr, (E v).indicator (fun _ ↦ (1 : ℝ)) σ) / 2 ^ m := by
      gcongr with σ
      exact key σ
    have step2 : (∑ σ : Fin m → Bool, ∑ v ∈ Tr, (E v).indicator (fun _ ↦ (1 : ℝ)) σ) / 2 ^ m
        = ∑ v ∈ Tr, (signMeasure m).real (E v) := by
      rw [Finset.sum_comm, Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ ↦ (signMeasure_real_eq m (E v)).symm
    have step3 : ∑ v ∈ Tr, (signMeasure m).real (E v)
        ≤ ∑ v ∈ Tr, Real.exp (-(m * ε ^ 2) / 4) :=
      Finset.sum_le_sum fun v _ ↦ rademacher_tail m (dvec v) (sq_dvec_le v) hε
    have step4 : (Tr.card : ℝ) ≤ G := by
      rw [hTr, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
      exact ncard_traceOf_image_le A hG z
    calc (∑ σ : Fin m → Bool, (symEvent A m ε).indicator (fun _ ↦ (1 : ℝ)) (swap σ z)) / 2 ^ m
        ≤ (∑ σ : Fin m → Bool, ∑ v ∈ Tr, (E v).indicator (fun _ ↦ (1 : ℝ)) σ) / 2 ^ m := step1
      _ = ∑ v ∈ Tr, (signMeasure m).real (E v) := step2
      _ ≤ ∑ v ∈ Tr, Real.exp (-(m * ε ^ 2) / 4) := step3
      _ = Tr.card * Real.exp (-(m * ε ^ 2) / 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ G * Real.exp (-(m * ε ^ 2) / 4) :=
          mul_le_mul_of_nonneg_right step4 (Real.exp_pos _).le

end VCInequality
