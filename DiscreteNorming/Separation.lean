import DiscreteNorming.Defs
import DiscreteNorming.Sampling

/-!
# Claims C8–C11: separation of the sample

* `expected_closePairs_le`: for `M` i.i.d. uniform points of `Ω`, the expected number of
  `r`-close pairs is at most `(M(M−1)/2) · r^{2d} |B^{2d}| / |Ω|` (two independent uniform points
  are `r`-close with probability `≤ |B_r|/|Ω|`).
* `closePairs_markov`: if the expectation is `≤ (t/4) M` then, by Markov's inequality, the number
  of close pairs is `≤ (t/3) M` with probability `≥ 1/4`.
* `exists_good_sample`: since the bad event has probability `≤ 1/100 < 1/4`, some sample lies in
  `Ω`, avoids the bad event and has `≤ (t/3) M` close pairs.
* `exists_separated_subsample`: deleting one point of each close pair leaves an `r`-separated
  nonempty set which still meets every set containing `≥ (t/2) M > (t/3) M` sample points.
-/

open MeasureTheory Metric

namespace DiscreteNorming

/-- Two independent uniform points of `Ω` are `r`-close with probability at most
`r^{2d} |B^{2d}| / |Ω|`. -/
theorem prob_close_le {d : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {r : ℝ} (hr : 0 ≤ r) :
    ((unif Ω).prod (unif Ω)).real {p | dist p.1 p.2 < r} ≤ r ^ (2 * d) * unitBallVol d / vol Ω := by
  haveI := isProbabilityMeasure_unif hb hpos
  have hΩtop : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  have hΩ0 : volume Ω ≠ 0 := hpos.ne'
  have hvolpos : 0 < vol Ω := ENNReal.toReal_pos hΩ0 hΩtop
  have hS : MeasurableSet {p : Pt d × Pt d | dist p.1 p.2 < r} :=
    (isOpen_lt continuous_dist continuous_const).measurableSet
  have hRHS : 0 ≤ r ^ (2 * d) * unitBallVol d / vol Ω :=
    div_nonneg (mul_nonneg (pow_nonneg hr _) ENNReal.toReal_nonneg) hvolpos.le
  rcases eq_or_lt_of_le hr with h0 | hrpos
  · have hempty : {p : Pt d × Pt d | dist p.1 p.2 < r} = ∅ := by
      ext p; simp [← h0, not_lt, dist_nonneg]
    rw [hempty]
    simpa using hRHS
  set C : ENNReal := (volume Ω)⁻¹ * (ENNReal.ofReal (r ^ (2 * d)) * volume (ball (0 : Pt d) 1))
    with hC
  have hballtop : volume (ball (0 : Pt d) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hCtop : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hΩ0)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hballtop)
  have hmain : ((unif Ω).prod (unif Ω)) {p | dist p.1 p.2 < r} ≤ C := by
    rw [Measure.prod_apply hS]
    calc ∫⁻ x, (unif Ω) (Prod.mk x ⁻¹' {p : Pt d × Pt d | dist p.1 p.2 < r}) ∂(unif Ω)
        ≤ ∫⁻ _, C ∂(unif Ω) := by
          refine lintegral_mono fun x => ?_
          have hpre : (Prod.mk x ⁻¹' {p : Pt d × Pt d | dist p.1 p.2 < r}) = ball x r := by
            ext y; simp [dist_comm x y]
          rw [hpre, hC]
          calc unif Ω (ball x r) = (volume Ω)⁻¹ * volume (Ω ∩ ball x r) :=
                ProbabilityTheory.cond_apply hΩ _ _
            _ ≤ (volume Ω)⁻¹ * volume (ball x r) := by
                gcongr
                exact Set.inter_subset_right
            _ = _ := by
                rw [Measure.addHaar_ball_of_pos volume x hrpos, finrank_euclideanSpace_fin]
      _ = C := by rw [lintegral_const, measure_univ, mul_one]
  rw [measureReal_def]
  refine (ENNReal.toReal_mono hCtop hmain).trans_eq ?_
  rw [hC, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (pow_nonneg hr _), vol, measureReal_def, unitBallVol]
  ring

open scoped Classical in
/-- The number of `r`-close pairs written as a sum of indicators. -/
theorem closePairs_eq_sum {d M : ℕ} (r : ℝ) (x : Fin M → Pt d) :
    (closePairs r x : ℝ)
      = ∑ p ∈ Finset.univ.filter (fun p : Fin M × Fin M ↦ p.1 < p.2),
          Set.indicator {y : Fin M → Pt d | dist (y p.1) (y p.2) < r} (fun _ ↦ (1 : ℝ)) x := by
  classical
  rw [closePairs, show (Finset.univ.filter fun p : Fin M × Fin M ↦
      p.1 < p.2 ∧ dist (x p.1) (x p.2) < r)
      = (Finset.univ.filter fun p : Fin M × Fin M ↦ p.1 < p.2).filter
        (fun p ↦ dist (x p.1) (x p.2) < r) from by rw [Finset.filter_filter],
    Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : dist (x p.1) (x p.2) < r <;> simp [h]

/-- The number of ordered pairs `i < j` in `Fin M` is `M.choose 2`. -/
theorem card_pairs_lt (M : ℕ) :
    (Finset.univ.filter fun p : Fin M × Fin M ↦ p.1 < p.2).card = M.choose 2 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have key : ∀ j : Fin M, (∑ _i ∈ Finset.univ.filter (fun i : Fin M ↦ i < j), 1) = (j : ℕ) := by
    intro j
    rw [Finset.sum_const, smul_eq_mul, mul_one,
      show (Finset.univ.filter fun i : Fin M ↦ i < j) = Finset.Iio j from by ext i; simp,
      Fin.card_Iio]
  have key2 : ∀ j : Fin M, (∑ i : Fin M, if i < j then 1 else 0) = (j : ℕ) := by
    intro j; rw [← key j, Finset.sum_filter]
  simp_rw [key2]
  rw [Fin.sum_univ_eq_sum_range (fun k => k) M, Finset.sum_range_id, Nat.choose_two_right]

/-- The pushforward of the sample measure under a pair of distinct coordinates is the product
measure. -/
theorem map_pi_pair {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {M : ℕ} {i j : Fin M} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin M ↦ μ).map (fun x ↦ (x i, x j)) = μ.prod μ := by
  classical
  have hmeas : Measurable (fun x : Fin M → X ↦ (x i, x j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [Measure.map_apply hmeas (hs.prod ht)]
  have hpre : (fun x : Fin M → X ↦ (x i, x j)) ⁻¹' (s ×ˢ t)
      = Set.pi Set.univ (fun k ↦ if k = i then s else if k = j then t else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · by_cases hk2 : k = j
        · subst hk2; simp [hk, h2]
        · simp [hk, hk2]
    · intro h
      exact ⟨by simpa using h i, by simpa [Ne.symm hij] using h j⟩
  rw [hpre, Measure.pi_pi,
    Fintype.prod_eq_mul i j hij (by rintro k ⟨hk1, hk2⟩; simp [hk1, hk2])]
  simp [Ne.symm hij]

/-- Measurability of the set of samples whose `p.1`-th and `p.2`-th points are `r`-close. -/
theorem measurableSet_closeAt {d M : ℕ} (r : ℝ) (p : Fin M × Fin M) :
    MeasurableSet {y : Fin M → Pt d | dist (y p.1) (y p.2) < r} := by
  have h : Measurable fun y : Fin M → Pt d ↦ dist (y p.1) (y p.2) :=
    continuous_dist.measurable.comp ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2))
  exact measurableSet_lt h measurable_const

/-- `x ↦ closePairs r x` is integrable for any probability measure on samples. -/
theorem integrable_closePairs {d M : ℕ} (μ : Measure (Fin M → Pt d)) [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun x ↦ (closePairs r x : ℝ)) μ := by
  classical
  simp_rw [closePairs_eq_sum r]
  exact integrable_finsetSum _ fun p _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_closeAt r p)

/-- Expected number of `r`-close pairs. -/
theorem expected_closePairs_le {d M : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x, (closePairs r x : ℝ) ∂(VCInequality.sampleMeasure (unif Ω) M)
      ≤ (M : ℝ) * (M - 1) / 2 * (r ^ (2 * d) * unitBallVol d / vol Ω) := by
  classical
  haveI := isProbabilityMeasure_unif hb hpos
  have hS : MeasurableSet {p : Pt d × Pt d | dist p.1 p.2 < r} :=
    (isOpen_lt continuous_dist continuous_const).measurableSet
  have hmeas : ∀ p : Fin M × Fin M, Measurable (fun x : Fin M → Pt d ↦ (x p.1, x p.2)) :=
    fun p => (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
  have hT := measurableSet_closeAt (d := d) (M := M) r
  rw [funext (closePairs_eq_sum (M := M) r),
    integral_finsetSum _ (fun p _ => (integrable_const (1 : ℝ)).indicator (hT p))]
  have hbnd : ∀ p ∈ Finset.univ.filter (fun p : Fin M × Fin M ↦ p.1 < p.2),
      ∫ x, Set.indicator {y : Fin M → Pt d | dist (y p.1) (y p.2) < r}
        (fun _ ↦ (1 : ℝ)) x ∂(VCInequality.sampleMeasure (unif Ω) M)
      ≤ r ^ (2 * d) * unitBallVol d / vol Ω := by
    intro p hp
    rw [integral_indicator_const (1 : ℝ) (hT p), smul_eq_mul, mul_one]
    have hne : p.1 ≠ p.2 := ne_of_lt (by simpa using hp)
    have hmap : (VCInequality.sampleMeasure (unif Ω) M)
          {y : Fin M → Pt d | dist (y p.1) (y p.2) < r}
        = ((unif Ω).prod (unif Ω)) {q : Pt d × Pt d | dist q.1 q.2 < r} := by
      rw [← map_pi_pair (unif Ω) hne, Measure.map_apply (hmeas p) hS]
      rfl
    rw [measureReal_def, hmap, ← measureReal_def]
    exact prob_close_le hΩ hb hpos hr
  refine (Finset.sum_le_card_nsmul _ _ _ hbnd).trans ?_
  rw [card_pairs_lt, nsmul_eq_mul, Nat.cast_choose_two]

/-- The volume of the unit ball is positive. -/
theorem unitBallVol_pos (d : ℕ) : 0 < unitBallVol d :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

/-- With `r = sepRadius`, the expected number of close pairs is at most `(t/4) M`. -/
theorem expected_closePairs_le_sepRadius {d N : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) (hd : 1 ≤ d) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ 1 / 8) (hN : 1 ≤ N) :
    ∫ x, (closePairs (sepRadius d Ω t N) x : ℝ)
        ∂(VCInequality.sampleMeasure (unif Ω) (sampleSize t N))
      ≤ t / 4 * sampleSize t N := by
  have hvolpos : 0 < vol Ω := ENNReal.toReal_pos hpos.ne' hb.measure_lt_top.ne
  have hBpos : 0 < unitBallVol d := unitBallVol_pos d
  have hMnat : 0 < sampleSize t N := by
    have := sampleSize_pos ht0 ht hN
    omega
  have hm : 0 < (sampleSize t N : ℝ) := by exact_mod_cast hMnat
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by positivity
  have ha : 0 < t * vol Ω / (2 * (sampleSize t N : ℝ) * unitBallVol d) :=
    div_pos (mul_pos ht0 hvolpos) (mul_pos (by linarith) hBpos)
  have hrnn : 0 ≤ sepRadius d Ω t N := Real.rpow_nonneg ha.le _
  have hrpow : sepRadius d Ω t N ^ (2 * d)
      = t * vol Ω / (2 * (sampleSize t N : ℝ) * unitBallVol d) := by
    rw [sepRadius, ← Real.rpow_natCast _ (2 * d), ← Real.rpow_mul ha.le]
    push_cast
    rw [one_div, inv_mul_cancel₀ hd0, Real.rpow_one]
  refine (expected_closePairs_le hΩ hb hpos hrnn).trans ?_
  rw [hrpow]
  set m : ℝ := (sampleSize t N : ℝ)
  have e1 : t * vol Ω / (2 * m * unitBallVol d) * unitBallVol d / vol Ω = t / (2 * m) := by
    field_simp
  rw [e1]
  have e2 : m * (m - 1) / 2 * (t / (2 * m)) = t * (m - 1) / 4 := by
    field_simp
    ring
  rw [e2]
  nlinarith [ht0.le]

/-- Markov: the number of close pairs exceeds `(t/3) M` with probability at most `3/4`. -/
theorem closePairs_markov {d M : ℕ} (μ : Measure (Pt d)) [IsProbabilityMeasure μ] {r t : ℝ}
    (ht0 : 0 < t) (hM : 1 ≤ M)
    (hE : ∫ x, (closePairs r x : ℝ) ∂(VCInequality.sampleMeasure μ M) ≤ t / 4 * M) :
    (VCInequality.sampleMeasure μ M).real {x | t / 3 * M < closePairs r x} ≤ 3 / 4 := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hint : Integrable (fun x ↦ (closePairs r x : ℝ)) (VCInequality.sampleMeasure μ M) :=
    integrable_closePairs _ r
  have hnn : 0 ≤ᵐ[VCInequality.sampleMeasure μ M] fun x ↦ (closePairs r x : ℝ) :=
    Filter.Eventually.of_forall fun x => by positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnn hint (t / 3 * M)
  have hsub : (VCInequality.sampleMeasure μ M).real {x | t / 3 * M < (closePairs r x : ℝ)}
      ≤ (VCInequality.sampleMeasure μ M).real {x | t / 3 * M ≤ (closePairs r x : ℝ)} :=
    measureReal_mono (by
      intro y hy
      simp only [Set.mem_setOf_eq] at hy ⊢
      exact le_of_lt hy)
  nlinarith [hsub, hmarkov, hE, measureReal_nonneg (μ := VCInequality.sampleMeasure μ M)
    (s := {x | t / 3 * (M : ℝ) ≤ (closePairs r x : ℝ)}), mul_pos ht0 (lt_of_lt_of_le one_pos hMR)]

/-- A good sample exists: all points in `Ω`, not in the bad event `B`, few close pairs. -/
theorem exists_good_sample {d M : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {B : Set (Fin M → Pt d)}
    (hBm : MeasurableSet B) (hB : (VCInequality.sampleMeasure (unif Ω) M).real B ≤ 1 / 100)
    {r t : ℝ}
    (hpairs : (VCInequality.sampleMeasure (unif Ω) M).real {x | t / 3 * M < closePairs r x}
      ≤ 3 / 4) :
    ∃ x : Fin M → Pt d, (∀ i, x i ∈ Ω) ∧ x ∉ B ∧ (closePairs r x : ℝ) ≤ t / 3 * M := by
  haveI := isProbabilityMeasure_unif hb hpos
  set ν := VCInequality.sampleMeasure (unif Ω) M with hν
  set Z : Set (Fin M → Pt d) := ⋃ i : Fin M, (fun x : Fin M → Pt d ↦ x i) ⁻¹' Ωᶜ with hZ
  have hZ0 : ν Z = 0 := by
    refine measure_iUnion_null fun i => ?_
    rw [hν, (measurePreserving_eval (fun _ : Fin M ↦ unif Ω) i).measure_preimage
      hΩ.compl.nullMeasurableSet]
    exact unif_compl hΩ
  set U : Set (Fin M → Pt d) := B ∪ {x | t / 3 * M < (closePairs r x : ℝ)} ∪ Z with hU
  have hUle : ν.real U ≤ 1 / 100 + 3 / 4 + 0 := by
    refine (measureReal_union_le _ _).trans ?_
    gcongr
    · exact (measureReal_union_le _ _).trans (by gcongr)
    · simp [measureReal_def, hZ0]
  rcases Set.eq_empty_or_nonempty Uᶜ with hemp | ⟨x, hx⟩
  · exfalso
    have : U = Set.univ := by
      rwa [Set.compl_empty_iff] at hemp
    rw [this] at hUle
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hUle
    linarith
  · rw [hU] at hx
    simp only [Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_setOf_eq] at hx
    obtain ⟨⟨hxB, hxP⟩, hxZ⟩ := hx
    refine ⟨x, fun i => ?_, hxB, not_lt.1 hxP⟩
    by_contra hi
    exact hxZ (Set.mem_iUnion.2 ⟨i, hi⟩)

/-- Deleting one point of each close pair: an `r`-separated nonempty subsample which meets every
set containing at least `(t/2) M` of the sample points. -/
theorem exists_separated_subsample {d M : ℕ} {x : Fin M → Pt d} {r t : ℝ} (ht0 : 0 < t)
    (hM : 1 ≤ M) (hpairs : (closePairs r x : ℝ) ≤ t / 3 * M) :
    ∃ S : Finset (Pt d), S.Nonempty ∧ (↑S : Set (Pt d)) ⊆ Set.range x ∧
      (∀ p ∈ S, ∀ q ∈ S, p ≠ q → r ≤ dist p q) ∧
      ∀ A : Set (Pt d), t / 2 * M ≤ VCInequality.count x A → ∃ p ∈ S, p ∈ A := by
  classical
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set F := Finset.univ.filter (fun p : Fin M × Fin M ↦ p.1 < p.2 ∧ dist (x p.1) (x p.2) < r)
    with hF
  set D : Finset (Fin M) := F.image Prod.snd with hD
  have hDcard : D.card ≤ closePairs r x := Finset.card_image_le
  have hDmem : ∀ j : Fin M, j ∈ D ↔ ∃ i, i < j ∧ dist (x i) (x j) < r := by
    intro j
    rw [hD, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hF, Finset.mem_filter] at hp
      exact ⟨p.1, hp.2.1, hp.2.2⟩
    · rintro ⟨i, hij, hdist⟩
      exact ⟨(i, j), by rw [hF, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij, hdist⟩, rfl⟩
  set K : Finset (Fin M) := Finset.univ \ D with hK
  have hKmem : ∀ j : Fin M, j ∈ K ↔ j ∉ D := by
    intro j; rw [hK, Finset.mem_sdiff]; simp
  refine ⟨K.image x, ?_, ?_, ?_, ?_⟩
  · refine ⟨x ⟨0, hM⟩, Finset.mem_image_of_mem _ ?_⟩
    rw [hKmem]
    intro hmem
    obtain ⟨i, hi, -⟩ := (hDmem _).1 hmem
    exact absurd hi (by simp [Fin.lt_def])
  · intro p hp
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp
    obtain ⟨i, -, rfl⟩ := hp
    exact ⟨i, rfl⟩
  · intro p hp q hq hpq
    simp only [Finset.mem_image] at hp hq
    obtain ⟨i, hi, rfl⟩ := hp
    obtain ⟨j, hj, rfl⟩ := hq
    have hij : i ≠ j := fun h => hpq (by rw [h])
    have key : ∀ a b : Fin M, b ∈ K → a < b → r ≤ dist (x a) (x b) := by
      intro a b hb hab
      by_contra hlt
      exact (hKmem b).1 hb ((hDmem b).2 ⟨a, hab, not_le.1 hlt⟩)
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j hj h
    · rw [dist_comm]; exact key j i hi h
  · intro A hA
    set C : Finset (Fin M) := Finset.univ.filter (fun i ↦ x i ∈ A) with hC
    have hcount : VCInequality.count x A = C.card := by rw [hC, VCInequality.count]
    have hcard : C.card ≤ (C \ D).card + D.card := Finset.card_le_card_sdiff_add_card
    have hcardR : (C.card : ℝ) ≤ ((C \ D).card : ℝ) + (D.card : ℝ) := by exact_mod_cast hcard
    have hDR : (D.card : ℝ) ≤ t / 3 * M := le_trans (by exact_mod_cast hDcard) hpairs
    have hCR : t / 2 * M ≤ (C.card : ℝ) := by rw [← hcount]; exact_mod_cast hA
    have hpos : 0 < ((C \ D).card : ℝ) := by nlinarith [mul_pos ht0 (lt_of_lt_of_le one_pos hMR)]
    have hne : (C \ D).Nonempty := Finset.card_pos.1 (by exact_mod_cast hpos)
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_sdiff, hC, Finset.mem_filter] at hi
    exact ⟨x i, Finset.mem_image_of_mem _ ((hKmem i).2 hi.2), hi.1.2⟩

end DiscreteNorming
