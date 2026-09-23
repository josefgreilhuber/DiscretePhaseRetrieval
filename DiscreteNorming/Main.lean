import DiscreteNorming.Defs
import DiscreteNorming.Chebyshev
import DiscreteNorming.ComplexPoly
import DiscreteNorming.Superlevel
import DiscreteNorming.VCBound
import DiscreteNorming.Sampling
import DiscreteNorming.Separation
import DiscreteNorming.Density
import VCInequality.RelativeVCInequality

/-!
# Proposition 2.1: the discrete norming inequality

* `discrete_norming_core` (C13): the proof of the paper, parametric in `0 < t ≤ 1/8`, with the
  Remez constant in Chebyshev form `T_{2n}((1+β)/(1−β))`, `β = θ^{1/(2d)}`.
* `discrete_norming_explicit` (C14): `t = 2^{−4d−1}` and the hypothesis
  `|Ω̂ \ Ω| ≤ 2^{−4d−2}|Ω̂|` give `θ ≤ 2^{−4d}`, hence `T_{2n} ≤ e^{4n}` (`C_norm = 4`) and the
  separation `deltaPaper d Ω · N^{−1/(2d)}`.
* `discrete_norming` (C15): general constants (`t = 1/8`; `θ < 1` always holds since
  `θ = 1 − (1−t)|Ω|/|Ω̂|`), `C_norm = 2 arcosh((1+β)/(1−β))`.

Assembly of the core: spanning family `φ` of `𝒱` (`exists_spanning`); the countable family
`A = ratFamily Ω φ` (measurable, in `superlevelFamily`, VC dimension `≤ 36N` by Lemma 2.2);
`μ = unif Ω`, `M = sampleSize t N`, `ε = √t/2`; the VC inequality with Sauer–Shelah and
`sample_size_bound` make the bad event have probability `≤ 1/100`; `exists_good_sample` and
`exists_separated_subsample` produce a `sepRadius`-separated `S ⊆ Ω` meeting every rational-family
set of measure `≥ t|Ω|` (`count_ge_of_not_bad`, `unif_real_apply`); finally, for `F, G ∈ 𝒱` write
`F = comb φ a`, `G = comb φ b`, take a maximum point `x₀` of `|P|` on `Ω̂`, apply
`superlevel_measure_ge_T` and `norming_of_hits` with `c = 1/T_{2n}(…)`.
-/

open MeasureTheory Metric Polynomial Polynomial.Chebyshev

namespace DiscreteNorming

/-! ### Helper lemmas -/

/-- VC dimension is monotone under passing to a subfamily. -/
theorem VCDimLE_mono {X : Type*} {ℱ 𝒢 : Set (Set X)} {V : ℕ} (h : ℱ ⊆ 𝒢)
    (hG : VCInequality.VCDimLE 𝒢 V) : VCInequality.VCDimLE ℱ V := by
  intro s hs
  refine hG s fun u hu ↦ ?_
  obtain ⟨A, hA, hA'⟩ := hs u hu
  exact ⟨A, h hA, hA'⟩

theorem vol_nonneg {d : ℕ} (Ω : Set (Pt d)) : 0 ≤ vol Ω := ENNReal.toReal_nonneg

theorem vol_pos_of {d : ℕ} {Ω : Set (Pt d)} (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) :
    0 < vol Ω :=
  ENNReal.toReal_pos hpos.ne' hb.measure_lt_top.ne

theorem vol_hull_pos {d : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) : 0 < vol (hull Ω) := by
  rw [vol_hull_eq hΩ hb]
  have h1 := vol_pos_of hb hpos
  have h2 := vol_nonneg (hull Ω \ Ω)
  linarith

theorem theta_nonneg {d : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {t : ℝ} (ht0 : 0 < t) :
    0 ≤ theta Ω t := by
  have h1 := vol_pos_of hb hpos
  have h2 := vol_nonneg (hull Ω \ Ω)
  have h3 := vol_hull_pos hΩ hb hpos
  rw [theta]
  positivity

theorem theta_lt_one {d : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {t : ℝ} (ht1 : t < 1) :
    theta Ω t < 1 := by
  have h1 := vol_pos_of hb hpos
  have h3 := vol_hull_pos hΩ hb hpos
  have he := vol_hull_eq hΩ hb
  rw [theta, div_lt_one h3]
  nlinarith

theorem inv_two_d_pos {d : ℕ} (hd : 1 ≤ d) : (0:ℝ) < 1 / (2 * d : ℝ) := by
  have : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  exact div_pos one_pos (by linarith)

theorem beta_nonneg {d : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {t : ℝ} (ht0 : 0 < t) :
    0 ≤ theta Ω t ^ (1 / (2 * d : ℝ)) :=
  Real.rpow_nonneg (theta_nonneg hΩ hb hpos ht0) _

theorem beta_lt_one {d : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    theta Ω t ^ (1 / (2 * d : ℝ)) < 1 :=
  Real.rpow_lt_one (theta_nonneg hΩ hb hpos ht0) (theta_lt_one hΩ hb hpos ht1) (inv_two_d_pos hd)

/-- The Remez constant `T_{2n}((1+β)/(1−β))` is at least `1`. -/
theorem one_le_T_theta {d n : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    1 ≤ (T ℝ (2 * n)).eval
      ((1 + theta Ω t ^ (1 / (2 * d : ℝ))) / (1 - theta Ω t ^ (1 / (2 * d : ℝ)))) := by
  have hβ0 := beta_nonneg (d := d) hΩ hb hpos ht0
  have hβ1 := beta_lt_one hd hΩ hb hpos ht0 ht1
  set β := theta Ω t ^ (1 / (2 * d : ℝ)) with hβ
  have hy : (1:ℝ) ≤ (1 + β) / (1 - β) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  calc (1:ℝ) = (T ℝ (2 * n)).eval (1 : ℝ) := (T_eval_one ℝ _).symm
    _ ≤ _ := Remez.monotoneOn_eval_T (2 * n) Set.self_mem_Ici (Set.mem_Ici.2 hy) hy

/-- The separation radius is at least `(t²|Ω|/(2(3000+1200|log t|)|B|))^{1/(2d)} N^{-1/(2d)}`. -/
theorem sepRadius_ge {d N : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)} (hvol : 0 < vol Ω) {t : ℝ}
    (ht0 : 0 < t) (ht : t ≤ 1 / 8) (hN : 1 ≤ N) :
    (t ^ 2 * vol Ω / (2 * (3000 + 1200 * |Real.log t|) * unitBallVol d)) ^ (1 / (2 * d : ℝ))
        * (N : ℝ) ^ (-(1 / (2 * d : ℝ))) ≤ sepRadius d Ω t N := by
  have hp : (0:ℝ) < 1 / (2 * d : ℝ) := inv_two_d_pos hd
  have hB := unitBallVol_pos d
  have hC : (0:ℝ) < 3000 + 1200 * |Real.log t| := by
    have := abs_nonneg (Real.log t); linarith
  have hMn : 1 ≤ sampleSize t N := by have := sampleSize_pos ht0 ht hN; omega
  have hMR : (0:ℝ) < (sampleSize t N : ℝ) := by exact_mod_cast hMn
  have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- `t · M ≤ (3000 + 1200|log t|) N`
  have htM : t * (sampleSize t N : ℝ) ≤ (3000 + 1200 * |Real.log t|) * N := by
    have h := sampleSize_le ht0 N
    rw [le_div_iff₀ ht0] at h
    linarith
  -- rewrite `N ^ (-p)` as `(N⁻¹) ^ p`
  have hNrw : (N : ℝ) ^ (-(1 / (2 * d : ℝ))) = ((N : ℝ)⁻¹) ^ (1 / (2 * d : ℝ)) := by
    rw [Real.inv_rpow hNR.le, Real.rpow_neg hNR.le]
  have hden : (0:ℝ) < 2 * (3000 + 1200 * |Real.log t|) * unitBallVol d :=
    mul_pos (mul_pos two_pos hC) hB
  have hbase0 : (0:ℝ) ≤ t ^ 2 * vol Ω / (2 * (3000 + 1200 * |Real.log t|) * unitBallVol d) :=
    le_of_lt (div_pos (mul_pos (pow_pos ht0 2) hvol) hden)
  rw [hNrw, ← Real.mul_rpow hbase0 (by positivity)]
  rw [sepRadius]
  refine Real.rpow_le_rpow ?_ ?_ hp.le
  · exact mul_nonneg hbase0 (by positivity)
  · -- the base inequality
    have e : t ^ 2 * vol Ω / (2 * (3000 + 1200 * |Real.log t|) * unitBallVol d) * ((N:ℝ)⁻¹)
        = t ^ 2 * vol Ω / (2 * (3000 + 1200 * |Real.log t|) * unitBallVol d * (N:ℝ)) := by
      rw [← div_eq_mul_inv, div_div]
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpp : (0:ℝ) < 2 * vol Ω * unitBallVol d * t :=
      mul_pos (mul_pos (mul_pos two_pos hvol) hB) ht0
    nlinarith [mul_le_mul_of_nonneg_left htM hpp.le]

/-! ### The four theorems -/

/-- **Core theorem** (the proof of Proposition 2.1, parametric in `t`). -/
theorem discrete_norming_core {d n N : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 8)
    {𝒱 : Submodule ℂ (PolyFock.Fock.P d)} (h𝒱deg : ∀ F ∈ 𝒱, F.totalDegree ≤ n)
    (h𝒱dim : Module.finrank ℂ 𝒱 = N) (hN : 1 ≤ N) :
    ∃ S : Finset (Pt d), S.Nonempty ∧ (↑S : Set (Pt d)) ⊆ Ω ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → sepRadius d Ω t N ≤ dist x y) ∧
      ∀ F ∈ 𝒱, ∀ G ∈ 𝒱, ∀ x ∈ hull Ω, ∃ y ∈ S,
        |diff F G x| ≤ (T ℝ (2 * n)).eval
          ((1 + theta Ω t ^ (1 / (2 * d : ℝ))) / (1 - theta Ω t ^ (1 / (2 * d : ℝ))))
          * |diff F G y| := by
  classical
  have ht1 : t < 1 := by linarith
  have hvol : 0 < vol Ω := vol_pos_of hb hpos
  haveI : IsProbabilityMeasure (unif Ω) := isProbabilityMeasure_unif hb hpos
  have hε : (0:ℝ) < Real.sqrt t / 2 := by
    have := Real.sqrt_pos.mpr ht0; linarith
  -- spanning family and the countable subfamily
  obtain ⟨φ, hφ𝒱, hφspan⟩ :
      ∃ φ : Fin N → PolyFock.Fock.P d, (∀ j, φ j ∈ 𝒱) ∧
        ∀ F ∈ 𝒱, ∃ a : Fin N → ℂ, F = comb φ a := by
    exact exists_spanning 𝒱 h𝒱dim hN
  have hA : ∀ i, MeasurableSet (ratFamily Ω φ i) := measurableSet_ratFamily hΩ φ
  have hrange : Set.range (ratFamily Ω φ) ⊆ superlevelFamily Ω 𝒱 := by
    rintro B ⟨i, rfl⟩
    exact ratFamily_mem_superlevelFamily Ω hφ𝒱 i
  have hvc : VCInequality.VCDimLE (Set.range (ratFamily Ω φ)) (36 * N) :=
    VCDimLE_mono hrange (vcDim_superlevel_family hN Ω 𝒱 h𝒱dim)
  have hM2 : 36 * N ≤ 2 * sampleSize t N := sampleSize_pos ht0 ht hN
  have hMn : 1 ≤ sampleSize t N := by omega
  -- the bad event has small probability
  have hbad : (VCInequality.sampleMeasure (unif Ω) (sampleSize t N)).real
      (VCInequality.badEvent (unif Ω) (ratFamily Ω φ) (sampleSize t N) (Real.sqrt t / 2))
      ≤ 1 / 100 := by
    refine le_trans (VCInequality.relative_deviation_vc (unif Ω) (ratFamily Ω φ) hA
      (sampleSize t N) (36 * N) (by omega) hM2 hvc hε) ?_
    exact sample_size_bound ht0 ht hN
  -- Markov bound for the number of close pairs
  have hmarkov := closePairs_markov (unif Ω) ht0 hMn
    (expected_closePairs_le_sepRadius hΩ hb hpos hd ht0 ht hN)
  obtain ⟨x, hxΩ, hxbad, hxpairs⟩ := exists_good_sample hΩ hb hpos
    (VCInequality.measurableSet_badEvent (unif Ω) hA (sampleSize t N) (Real.sqrt t / 2))
    hbad hmarkov
  obtain ⟨S, hSne, hSsub, hSsep, hShit⟩ :
      ∃ S : Finset (Pt d), S.Nonempty ∧ (↑S : Set (Pt d)) ⊆ Set.range x ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q → sepRadius d Ω t N ≤ dist p q) ∧
        ∀ A : Set (Pt d), t / 2 * (sampleSize t N : ℝ) ≤ VCInequality.count x A →
          ∃ p ∈ S, p ∈ A := by
    exact exists_separated_subsample ht0 hMn hxpairs
  have hSΩ : (↑S : Set (Pt d)) ⊆ Ω := by
    intro p hp
    obtain ⟨i, rfl⟩ := hSsub hp
    exact hxΩ i
  -- `S` meets every rational-family set of measure at least `t |Ω|`
  have hhit : ∀ i : RatIndex N, t * vol Ω ≤ vol (ratFamily Ω φ i) →
      ∃ p ∈ S, p ∈ ratFamily Ω φ i := by
    intro i hi
    have hsub : ratFamily Ω φ i ⊆ Ω := fun z hz ↦ hz.1
    have hmeas : (unif Ω).real (ratFamily Ω φ i) = vol (ratFamily Ω φ i) / vol Ω := by
      rw [unif_real_apply hΩ hb hpos, Set.inter_eq_self_of_subset_right hsub]
    have hti : t ≤ (unif Ω).real (ratFamily Ω φ i) := by
      rw [hmeas, le_div_iff₀ hvol]; exact hi
    exact hShit _ (count_ge_of_not_bad (unif Ω) (ratFamily Ω φ) ht0 hxbad i hti)
  refine ⟨S, hSne, hSΩ, hSsep, ?_⟩
  -- the norming inequality
  intro F hF𝒱 G hG𝒱 z hz
  obtain ⟨a, rfl⟩ := hφspan F hF𝒱
  obtain ⟨b, rfl⟩ := hφspan G hG𝒱
  have hΩne : Ω.Nonempty := nonempty_of_measure_ne_zero hpos.ne'
  obtain ⟨x₀, hx₀, hmax⟩ := exists_max_on_hull hb hΩne (comb φ a) (comb φ b)
  set Cθ := (T ℝ (2 * n)).eval
    ((1 + theta Ω t ^ (1 / (2 * d : ℝ))) / (1 - theta Ω t ^ (1 / (2 * d : ℝ)))) with hCθ
  have hC1 : 1 ≤ Cθ := one_le_T_theta hd hΩ hb hpos ht0 ht1
  have hC0 : 0 < Cθ := by linarith
  set K := |diff (comb φ a) (comb φ b) x₀| with hKdef
  have hK : 0 ≤ K := abs_nonneg _
  have hsup : t * vol Ω ≤ vol {y ∈ Ω | Cθ⁻¹ * K ≤ |diff (comb φ a) (comb φ b) y|} := by
    have hset : {y ∈ Ω | Cθ⁻¹ * K ≤ |diff (comb φ a) (comb φ b) y|}
        = {y ∈ Ω | K / Cθ ≤ |diff (comb φ a) (comb φ b) y|} := by
      rw [show Cθ⁻¹ * K = K / Cθ by ring]
    rw [hset, hKdef, hCθ]
    exact superlevel_measure_ge_T hd hΩ hb hvol (h𝒱deg _ hF𝒱) (h𝒱deg _ hG𝒱) ht0 ht1 hx₀ hmax
  obtain ⟨y, hyS, hy⟩ := norming_of_hits hb φ hhit a b hK (by positivity)
    (by rw [inv_le_one_iff₀]; right; exact hC1) hsup hSne
  refine ⟨y, hyS, ?_⟩
  have h1 : |diff (comb φ a) (comb φ b) z| ≤ K := hmax z hz
  have h2 : K ≤ Cθ * |diff (comb φ a) (comb φ b) y| := by
    rw [show Cθ⁻¹ * K = K / Cθ by ring, div_le_iff₀ hC0] at hy
    linarith
  linarith

/-- `sepRadius` is at least the paper's `δ · N^{−1/(2d)}` when `t = 2^{−4d−1}`. -/
theorem deltaPaper_le_sepRadius {d N : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)} (hpos : 0 < vol Ω)
    (hN : 1 ≤ N) :
    deltaPaper d Ω * (N : ℝ) ^ (-(1 / (2 * d : ℝ))) ≤ sepRadius d Ω ((1 / 2) ^ (4 * d + 1)) N := by
  have hdR : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp : (0:ℝ) < 1 / (2 * d : ℝ) := inv_two_d_pos hd
  have hB := unitBallVol_pos d
  set t : ℝ := (1 / 2) ^ (4 * d + 1) with htdef
  have ht0 : (0:ℝ) < t := by rw [htdef]; positivity
  have ht : t ≤ 1 / 8 := by
    rw [htdef]
    calc ((1:ℝ)/2) ^ (4 * d + 1) ≤ (1/2) ^ 5 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ 1 / 8 := by norm_num
  -- `|log t| = (4d+1) log 2`
  have hlog : |Real.log t| = (4 * d + 1 : ℕ) * Real.log 2 := by
    have h1 : Real.log t = -((4 * d + 1 : ℕ) * Real.log 2) := by
      rw [htdef, Real.log_pow, one_div, Real.log_inv]; ring
    rw [h1, abs_neg, abs_of_nonneg]
    positivity
  have hlogle : |Real.log t| ≤ (4 * d + 1 : ℕ) * 0.6931471808 := by
    rw [hlog]
    have := Real.log_two_lt_d9
    have hc : (0:ℝ) ≤ (4 * d + 1 : ℕ) := by positivity
    nlinarith
  refine le_trans ?_ (sepRadius_ge hd hpos ht0 ht hN)
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
  -- `deltaPaper = ((1/2)^{8d} · |Ω|/(|B| · 3·10⁵(1+d)))^{1/(2d)}`
  have hpow : ((1:ℝ) / 2) ^ (8 * d) = ((1:ℝ) / 16) ^ (2 * d : ℕ) := by
    rw [show 8 * d = 4 * (2 * d) by ring, pow_mul]
    norm_num
  have h16 : ((1:ℝ) / 16) = (((1:ℝ) / 2) ^ (8 * d)) ^ (1 / (2 * d : ℝ)) := by
    rw [hpow, ← Real.rpow_natCast ((1:ℝ)/16) (2 * d), ← Real.rpow_mul (by norm_num)]
    rw [show ((2 * d : ℕ) : ℝ) * (1 / (2 * d : ℝ)) = 1 by push_cast; field_simp]
    rw [Real.rpow_one]
  have hdelta : deltaPaper d Ω
      = (((1:ℝ) / 2) ^ (8 * d) * (vol Ω / unitBallVol d / (3 * 10 ^ 5 * (1 + d))))
        ^ (1 / (2 * d : ℝ)) := by
    rw [deltaPaper, h16, ← Real.mul_rpow (by positivity) (by positivity)]
  rw [hdelta]
  refine Real.rpow_le_rpow (by positivity) ?_ hp.le
  -- the base inequality
  have ht2 : t ^ 2 = ((1:ℝ) / 2) ^ (8 * d) / 4 := by
    rw [htdef, ← pow_mul, show (4 * d + 1) * 2 = 8 * d + 2 by ring, pow_add]
    norm_num
    ring
  have e1 : ((1:ℝ) / 2) ^ (8 * d) * (vol Ω / unitBallVol d / (3 * 10 ^ 5 * (1 + d)))
      = ((1:ℝ) / 2) ^ (8 * d) * vol Ω / (unitBallVol d * (3 * 10 ^ 5 * (1 + (d:ℝ)))) := by
    field_simp
  have e2 : t ^ 2 * vol Ω / (2 * (3000 + 1200 * |Real.log t|) * unitBallVol d)
      = ((1:ℝ) / 2) ^ (8 * d) * vol Ω
        / (8 * (3000 + 1200 * |Real.log t|) * unitBallVol d) := by
    rw [ht2]
    have hC : (0:ℝ) < 3000 + 1200 * |Real.log t| := by
      have := abs_nonneg (Real.log t); linarith
    field_simp
    ring
  rw [e1, e2]
  have hnum : (0:ℝ) ≤ ((1:ℝ) / 2) ^ (8 * d) * vol Ω := by positivity
  have hd1 : (0:ℝ) < 8 * (3000 + 1200 * |Real.log t|) * unitBallVol d := by
    have := abs_nonneg (Real.log t)
    have h8 : (0:ℝ) < 8 * (3000 + 1200 * |Real.log t|) := by linarith
    exact mul_pos h8 hB
  have hd2 : (0:ℝ) < unitBallVol d * (3 * 10 ^ 5 * (1 + (d:ℝ))) :=
    mul_pos hB (by positivity)
  have hkey : 8 * (3000 + 1200 * |Real.log t|) ≤ 3 * 10 ^ 5 * (1 + (d:ℝ)) := by
    have hc : ((4 * d + 1 : ℕ) : ℝ) = 4 * (d:ℝ) + 1 := by push_cast; ring
    rw [hc] at hlogle
    nlinarith
  refine div_le_div_of_nonneg_left hnum hd1 ?_
  nlinarith [hB, hkey]

/-- **Proposition 2.1 (discrete norming inequality), explicit constants.** Let `Ω ⊆ ℂ^d` be a
bounded measurable set of positive measure with `|Ω̂ \ Ω| ≤ 2^{−4d−2} |Ω̂|`, and `𝒱` an
`N`-dimensional space of polynomials of degree `≤ n`. Then there is a
`δ N^{−1/(2d)}`-separated set `S ⊆ Ω`, `δ = (1/16)(|Ω|/|B^{2d}| / (3·10⁵(1+d)))^{1/(2d)}`, with
`‖|F|² − |G|²‖_{L∞(Ω̂)} ≤ e^{4n} ‖|F|² − |G|²‖_{L∞(S)}` for all `F, G ∈ 𝒱`. -/
theorem discrete_norming_explicit {d n N : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω)
    (hhull : vol (hull Ω \ Ω) ≤ (1 / 2) ^ (4 * d + 2) * vol (hull Ω))
    {𝒱 : Submodule ℂ (PolyFock.Fock.P d)} (h𝒱deg : ∀ F ∈ 𝒱, F.totalDegree ≤ n)
    (h𝒱dim : Module.finrank ℂ 𝒱 = N) (hN : 1 ≤ N) :
    ∃ S : Finset (Pt d), (↑S : Set (Pt d)) ⊆ Ω ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → deltaPaper d Ω * (N : ℝ) ^ (-(1 / (2 * d : ℝ))) ≤ dist x y) ∧
      ∀ F ∈ 𝒱, ∀ G ∈ 𝒱, ∀ x ∈ hull Ω, ∃ y ∈ S,
        |diff F G x| ≤ Real.exp (4 * n) * |diff F G y| := by
  have hdR : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hvol : 0 < vol Ω := vol_pos_of hb hpos
  have hhullpos : 0 < vol (hull Ω) := vol_hull_pos hΩ hb hpos
  set t : ℝ := (1 / 2) ^ (4 * d + 1) with htdef
  have ht0 : (0:ℝ) < t := by rw [htdef]; positivity
  have ht : t ≤ 1 / 8 := by
    rw [htdef]
    calc ((1:ℝ)/2) ^ (4 * d + 1) ≤ (1/2) ^ 5 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ 1 / 8 := by norm_num
  obtain ⟨S, hSne, hSΩ, hSsep, hSnorm⟩ :=
    discrete_norming_core hd hΩ hb hpos ht0 ht h𝒱deg h𝒱dim hN
  refine ⟨S, hSΩ, ?_, ?_⟩
  · intro p hp q hq hpq
    exact le_trans (deltaPaper_le_sepRadius hd hvol hN) (hSsep p hp q hq hpq)
  · -- the Remez constant is at most `exp (4 n)`
    have hθ : theta Ω t ≤ (1 / 2) ^ (4 * d) := by
      have hle : vol Ω ≤ vol (hull Ω) := by
        have := vol_hull_eq hΩ hb
        have := vol_nonneg (hull Ω \ Ω)
        linarith
      rw [theta, div_le_iff₀ hhullpos]
      have h1 : t * vol Ω ≤ t * vol (hull Ω) := by nlinarith
      have h2 : ((1:ℝ)/2) ^ (4 * d + 1) + (1/2) ^ (4 * d + 2) ≤ (1/2) ^ (4 * d) := by
        rw [pow_succ, pow_succ, pow_succ]
        nlinarith [pow_pos (show (0:ℝ) < 1/2 by norm_num) (4 * d)]
      nlinarith
    have hθ0 : 0 ≤ theta Ω t := theta_nonneg hΩ hb hpos ht0
    have hβ0 : 0 ≤ theta Ω t ^ (1 / (2 * d : ℝ)) := Real.rpow_nonneg hθ0 _
    have hβ : theta Ω t ^ (1 / (2 * d : ℝ)) ≤ 1 / 4 := by
      have h1 : theta Ω t ^ (1 / (2 * d : ℝ))
          ≤ (((1:ℝ) / 2) ^ (4 * d)) ^ (1 / (2 * d : ℝ)) :=
        Real.rpow_le_rpow hθ0 hθ (inv_two_d_pos hd).le
      have h2 : (((1:ℝ) / 2) ^ (4 * d)) ^ (1 / (2 * d : ℝ)) = 1 / 4 := by
        rw [← Real.rpow_natCast ((1:ℝ)/2) (4 * d), ← Real.rpow_mul (by norm_num)]
        rw [show ((4 * d : ℕ) : ℝ) * (1 / (2 * d : ℝ)) = 2 by push_cast; field_simp; ring]
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      linarith [h2 ▸ h1]
    have hTle : (T ℝ (2 * n)).eval
        ((1 + theta Ω t ^ (1 / (2 * d : ℝ))) / (1 - theta Ω t ^ (1 / (2 * d : ℝ))))
        ≤ Real.exp (4 * n) := by
      refine le_trans (T_eval_le_exp (2 * n) hβ0 hβ) ?_
      refine Real.exp_le_exp.2 ?_
      have hs : Real.sqrt (theta Ω t ^ (1 / (2 * d : ℝ))) ≤ 1 / 2 := by
        have h1 : Real.sqrt (theta Ω t ^ (1 / (2 * d : ℝ))) ≤ Real.sqrt (1 / 4) :=
          Real.sqrt_le_sqrt hβ
        have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
          rw [show (1/4 : ℝ) = (1/2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        linarith [h2 ▸ h1]
      have hs0 : 0 ≤ Real.sqrt (theta Ω t ^ (1 / (2 * d : ℝ))) := Real.sqrt_nonneg _
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith
    intro F hF G hG z hz
    obtain ⟨y, hyS, hy⟩ := hSnorm F hF G hG z hz
    refine ⟨y, hyS, ?_⟩
    refine le_trans hy (mul_le_mul_of_nonneg_right hTle (abs_nonneg _))

/-- **Proposition 2.1, general form.** For every bounded measurable `Ω ⊆ ℂ^d` of positive measure
there are constants `C_norm, δ > 0` such that for every `N`-dimensional space `𝒱` of polynomials
of degree `≤ n` there is a `δ N^{−1/(2d)}`-separated set `S ⊆ Ω` with
`‖|F|² − |G|²‖_{L∞(Ω̂)} ≤ e^{C_norm n} ‖|F|² − |G|²‖_{L∞(S)}` for all `F, G ∈ 𝒱`. -/
theorem discrete_norming {d : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < volume Ω) :
    ∃ Cnorm δ : ℝ, 0 < δ ∧ ∀ (n N : ℕ) (𝒱 : Submodule ℂ (PolyFock.Fock.P d)),
      (∀ F ∈ 𝒱, F.totalDegree ≤ n) → Module.finrank ℂ 𝒱 = N → 1 ≤ N →
      ∃ S : Finset (Pt d), (↑S : Set (Pt d)) ⊆ Ω ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ * (N : ℝ) ^ (-(1 / (2 * d : ℝ))) ≤ dist x y) ∧
        ∀ F ∈ 𝒱, ∀ G ∈ 𝒱, ∀ x ∈ hull Ω, ∃ y ∈ S,
          |diff F G x| ≤ Real.exp (Cnorm * n) * |diff F G y| := by
  have hvol : 0 < vol Ω := vol_pos_of hb hpos
  have hB := unitBallVol_pos d
  set t : ℝ := 1 / 8 with htdef
  have ht0 : (0:ℝ) < t := by rw [htdef]; norm_num
  have ht : t ≤ 1 / 8 := by rw [htdef]
  have ht1 : t < 1 := by rw [htdef]; norm_num
  set β : ℝ := theta Ω t ^ (1 / (2 * d : ℝ)) with hβdef
  have hβ0 : 0 ≤ β := beta_nonneg hΩ hb hpos ht0
  have hβ1 : β < 1 := beta_lt_one hd hΩ hb hpos ht0 ht1
  set y : ℝ := (1 + β) / (1 - β) with hydef
  have hy1 : (1:ℝ) ≤ y := by rw [hydef, le_div_iff₀ (by linarith)]; linarith
  set w : ℝ := y + Real.sqrt (y ^ 2 - 1) with hwdef
  have hw1 : (1:ℝ) ≤ w := by
    rw [hwdef]; have := Real.sqrt_nonneg (y ^ 2 - 1); linarith
  have hw0 : (0:ℝ) < w := by linarith
  have hC : (0:ℝ) < 3000 + 1200 * |Real.log t| := by
    have := abs_nonneg (Real.log t); linarith
  refine ⟨2 * Real.log w,
    (t ^ 2 * vol Ω / (2 * (3000 + 1200 * |Real.log t|) * unitBallVol d)) ^ (1 / (2 * d : ℝ)),
    ?_, ?_⟩
  · exact Real.rpow_pos_of_pos
      (div_pos (mul_pos (pow_pos ht0 2) hvol) (mul_pos (mul_pos two_pos hC) hB)) _
  · intro n N 𝒱 h𝒱deg h𝒱dim hN
    obtain ⟨S, hSne, hSΩ, hSsep, hSnorm⟩ :=
      discrete_norming_core hd hΩ hb hpos ht0 ht h𝒱deg h𝒱dim hN
    refine ⟨S, hSΩ, ?_, ?_⟩
    · intro p hp q hq hpq
      exact le_trans (sepRadius_ge hd hvol ht0 ht hN) (hSsep p hp q hq hpq)
    · have hTle : (T ℝ (2 * n)).eval y ≤ Real.exp (2 * Real.log w * n) := by
        refine le_trans (T_eval_le_pow (2 * n) hy1) ?_
        have : w ^ (2 * n) = Real.exp (((2 * n : ℕ) : ℝ) * Real.log w) := by
          rw [Real.exp_nat_mul, Real.exp_log hw0]
        rw [hwdef] at this ⊢
        rw [this]
        refine Real.exp_le_exp.2 (le_of_eq ?_)
        push_cast; ring
      intro F hF G hG z hz
      obtain ⟨p, hpS, hp⟩ := hSnorm F hF G hG z hz
      refine ⟨p, hpS, ?_⟩
      refine le_trans hp (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      exact hTle

end DiscreteNorming
