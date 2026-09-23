import DiscretePhaseRetrieval.Defs
import DiscreteNorming.Superlevel
import DiscreteNorming.Separation

/-!
# Claims A1–A3: the sampling block `A_{N,μ} = B_{μ√N}(0) \ B_{μ√N/8}(0)`

* A1: bounded, measurable, positive measure; its closed convex hull is the closed ball
  `B̄_{μ√N}` (a point of the inner ball is the midpoint of two points `x ± t u` of the annulus,
  `u ⟂ x` a unit vector; this uses `2d ≥ 2`).
* A2: `|Ω̂ \ Ω| = 2^{−6d} |Ω̂| ≤ 2^{−4d−2} |Ω̂|` (spheres are null).
* A3: `|Ω| / |B^{2d}| ≥ (63/64) μ^{2d} N^d`.
-/

open MeasureTheory Metric DiscreteNorming RealInnerProductSpace

namespace DiscretePR

variable {d : ℕ} {μ : ℝ} {N : ℕ}

theorem annulus_measurable (d : ℕ) (μ : ℝ) (N : ℕ) : MeasurableSet (annulus d μ N) :=
  measurableSet_ball.diff measurableSet_ball

theorem annulus_bounded (d : ℕ) (μ : ℝ) (N : ℕ) : Bornology.IsBounded (annulus d μ N) :=
  Metric.isBounded_ball.subset Set.diff_subset

/-- `ℝ^{2d}` is nontrivial when `d ≥ 1`. -/
lemma nontrivial_Pt (hd : 0 < d) : Nontrivial (Pt d) := by
  refine Module.nontrivial_of_finrank_pos (R := ℝ) ?_
  rw [finrank_euclideanSpace_fin]
  omega

/-- Volume of a ball in `ℝ^{2d}`. -/
lemma volume_ball_Pt (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) :
    volume (ball (0 : Pt d) s) = ENNReal.ofReal (s ^ (2 * d)) * volume (ball (0 : Pt d) 1) := by
  haveI := nontrivial_Pt hd
  rw [Measure.addHaar_ball volume 0 hs, finrank_euclideanSpace_fin]

lemma vol_ball_Pt (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) :
    (volume (ball (0 : Pt d) s)).toReal = s ^ (2 * d) * unitBallVol d := by
  rw [volume_ball_Pt hd hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rfl

lemma vol_annulus (hd : 0 < d) (hμ : 0 < μ) (hN : 0 < N) :
    vol (annulus d μ N)
      = ((μ * Real.sqrt N) ^ (2 * d) - (μ * Real.sqrt N / 8) ^ (2 * d)) * unitBallVol d := by
  have hr : 0 < μ * Real.sqrt N := by
    have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    positivity
  have hsub : ball (0 : Pt d) (μ * Real.sqrt N / 8) ⊆ ball 0 (μ * Real.sqrt N) :=
    ball_subset_ball (by linarith)
  rw [vol, measureReal_def, annulus,
    measure_diff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
    ENNReal.toReal_sub_of_le (measure_mono hsub) measure_ball_lt_top.ne,
    vol_ball_Pt hd hr.le, vol_ball_Pt hd (by linarith)]
  ring

lemma vol_annulus_pos (hd : 0 < d) (hμ : 0 < μ) (hN : 0 < N) : 0 < vol (annulus d μ N) := by
  have hr : 0 < μ * Real.sqrt N := by
    have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    positivity
  rw [vol_annulus hd hμ hN]
  have hlt : (μ * Real.sqrt N / 8) ^ (2 * d) < (μ * Real.sqrt N) ^ (2 * d) := by
    apply pow_lt_pow_left₀ (by linarith) (by linarith)
    omega
  have := unitBallVol_pos d
  nlinarith

theorem annulus_vol_pos (hd : 0 < d) (hμ : 0 < μ) (hN : 0 < N) : 0 < volume (annulus d μ N) := by
  have h := vol_annulus_pos hd hμ hN
  rw [vol, measureReal_def, ENNReal.toReal_pos_iff] at h
  exact h.1

theorem hull_annulus_subset_closedBall (d : ℕ) (μ : ℝ) (N : ℕ) :
    hull (annulus d μ N) ⊆ closedBall 0 (μ * Real.sqrt N) :=
  closure_minimal
    (convexHull_min (fun _ hx => ball_subset_closedBall hx.1) (convex_closedBall _ _))
    isClosed_closedBall

/-- In `ℝ^{2d}` with `d ≥ 1` every vector admits an orthogonal unit vector. -/
lemma exists_unit_orthogonal (hd : 0 < d) (x : Pt d) :
    ∃ u : Pt d, ‖u‖ = 1 ∧ ⟪x, u⟫ = 0 := by
  have hfr : Module.finrank ℝ (Pt d) = 2 * d := finrank_euclideanSpace_fin
  have h1 : Module.finrank ℝ (ℝ ∙ x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [Submodule.span_zero_singleton]; simp
    · rw [finrank_span_singleton hx]
  have hadd := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ x))
  rw [hfr] at hadd
  have hKpos : 0 < Module.finrank ℝ ((ℝ ∙ x)ᗮ) := by omega
  have hKne : ((ℝ ∙ x)ᗮ : Submodule ℝ (Pt d)) ≠ ⊥ := by
    intro h
    rw [h] at hKpos
    simp at hKpos
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKne
  have hxv : ⟪x, v⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).1 hv x (Submodule.mem_span_singleton_self x)
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn]
  · rw [real_inner_smul_right, hxv, mul_zero]

/-- The convex hull of the annulus contains the ball. -/
theorem ball_subset_hull_annulus (hd : 0 < d) (hμ : 0 < μ) (hN : 0 < N) :
    ball (0 : Pt d) (μ * Real.sqrt N) ⊆ hull (annulus d μ N) := by
  have hr : 0 < μ * Real.sqrt N := by
    have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    positivity
  set r := μ * Real.sqrt N with hr_def
  intro x hx
  rw [mem_ball_zero_iff] at hx
  by_cases h8 : r / 8 ≤ ‖x‖
  · refine subset_hull _ ⟨mem_ball_zero_iff.2 hx, ?_⟩
    simp only [mem_ball_zero_iff, not_lt]
    exact h8
  push Not at h8
  obtain ⟨u, hu1, hxu⟩ := exists_unit_orthogonal hd x
  set c : ℝ := ((r / 8) ^ 2 + r ^ 2) / 2 with hc_def
  have hxn : 0 ≤ ‖x‖ := norm_nonneg x
  have h88 : (r / 8) ^ 2 < r ^ 2 := by nlinarith
  have hclow : (r / 8) ^ 2 < c := by rw [hc_def]; linarith
  have hchigh : c < r ^ 2 := by rw [hc_def]; linarith
  have hcx : ‖x‖ ^ 2 < c := by nlinarith
  set t : ℝ := Real.sqrt (c - ‖x‖ ^ 2) with ht_def
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = c - ‖x‖ ^ 2 := Real.sq_sqrt (by linarith)
  have hnu : ‖t • u‖ = t := by
    rw [norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hip : ⟪x, t • u⟫ = 0 := by rw [real_inner_smul_right, hxu, mul_zero]
  have hp : ‖x + t • u‖ ^ 2 = c := by rw [norm_add_sq_real, hip, hnu]; linarith
  have hq : ‖x - t • u‖ ^ 2 = c := by rw [norm_sub_sq_real, hip, hnu]; linarith
  have key : ∀ y : Pt d, ‖y‖ ^ 2 = c → y ∈ annulus d μ N := by
    intro y hy
    have hyn : 0 ≤ ‖y‖ := norm_nonneg y
    refine ⟨mem_ball_zero_iff.2 ?_, ?_⟩
    · nlinarith
    · simp only [mem_ball_zero_iff, not_lt]
      nlinarith
  have hpm := subset_convexHull ℝ (annulus d μ N) (key _ hp)
  have hqm := subset_convexHull ℝ (annulus d μ N) (key _ hq)
  have hmid : x = (1 / 2 : ℝ) • (x + t • u) + (1 / 2 : ℝ) • (x - t • u) := by module
  refine subset_closure ?_
  rw [hmid]
  exact (convex_convexHull ℝ _) hpm hqm (by norm_num) (by norm_num) (by norm_num)

/-- A2: `|Ω̂ \ Ω| ≤ 2^{−4d−2} |Ω̂|`. -/
theorem annulus_hull_defect (hd : 0 < d) (hμ : 0 < μ) (hN : 0 < N) :
    vol (hull (annulus d μ N) \ annulus d μ N)
      ≤ (1 / 2) ^ (4 * d + 2) * vol (hull (annulus d μ N)) := by
  haveI := nontrivial_Pt hd
  have hr : 0 < μ * Real.sqrt N := by
    have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    positivity
  set r := μ * Real.sqrt N with hr_def
  set Ω := annulus d μ N with hΩ_def
  have hsub : hull Ω \ Ω ⊆ sphere (0 : Pt d) r ∪ ball (0 : Pt d) (r / 8) := by
    intro y hy
    have h1 : y ∈ closedBall (0 : Pt d) r := hull_annulus_subset_closedBall d μ N hy.1
    by_cases h2 : y ∈ ball (0 : Pt d) (r / 8)
    · exact Or.inr h2
    · refine Or.inl ?_
      have h3 : y ∉ ball (0 : Pt d) r := fun h => hy.2 ⟨h, h2⟩
      rw [mem_closedBall_zero_iff] at h1
      rw [mem_ball_zero_iff, not_lt] at h3
      rw [mem_sphere_zero_iff_norm]
      linarith
  have hmeas1 : volume (hull Ω \ Ω) ≤ volume (ball (0 : Pt d) (r / 8)) := by
    calc volume (hull Ω \ Ω)
        ≤ volume (sphere (0 : Pt d) r ∪ ball (0 : Pt d) (r / 8)) := measure_mono hsub
      _ ≤ volume (sphere (0 : Pt d) r) + volume (ball (0 : Pt d) (r / 8)) := measure_union_le _ _
      _ = volume (ball (0 : Pt d) (r / 8)) := by
          rw [Measure.addHaar_sphere volume 0 r, zero_add]
  have hA : vol (hull Ω \ Ω) ≤ (r / 8) ^ (2 * d) * unitBallVol d := by
    have h := ENNReal.toReal_mono measure_ball_lt_top.ne hmeas1
    rwa [vol_ball_Pt hd (by linarith)] at h
  have hB : r ^ (2 * d) * unitBallVol d ≤ vol (hull Ω) := by
    have hfin : volume (hull Ω) ≠ ⊤ := (isCompact_hull (annulus_bounded d μ N)).measure_lt_top.ne
    have h := ENNReal.toReal_mono hfin (measure_mono (ball_subset_hull_annulus hd hμ hN))
    rwa [vol_ball_Pt hd hr.le] at h
  have hpow : ((1 : ℝ) / 8) ^ (2 * d) ≤ ((1 : ℝ) / 2) ^ (4 * d + 2) := by
    have h1 : ((1 : ℝ) / 8) ^ (2 * d) = ((1 : ℝ) / 2) ^ (6 * d) := by
      rw [show ((1 : ℝ) / 8) = ((1 : ℝ) / 2) ^ 3 by norm_num, ← pow_mul]
      ring_nf
    rw [h1]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hV := unitBallVol_pos d
  have hrp : (0 : ℝ) ≤ r ^ (2 * d) := by positivity
  have hsplit : (r / 8) ^ (2 * d) = ((1 : ℝ) / 8) ^ (2 * d) * r ^ (2 * d) := by
    rw [div_pow, div_pow]; ring
  have hc : (0 : ℝ) < ((1 : ℝ) / 2) ^ (4 * d + 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hrp hV.le),
    mul_le_mul_of_nonneg_left hB hc.le]

/-- A3: `|Ω| ≥ (63/64) μ^{2d} N^d |B^{2d}|`. -/
theorem annulus_vol_ge (hd : 0 < d) (hμ : 0 < μ) (hN : 0 < N) :
    63 / 64 * μ ^ (2 * d) * (N : ℝ) ^ d * unitBallVol d ≤ vol (annulus d μ N) := by
  have hsq : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [vol_annulus hd hμ hN]
  have hrpow : (μ * Real.sqrt N) ^ (2 * d) = μ ^ (2 * d) * (N : ℝ) ^ d := by
    rw [mul_pow, pow_mul (Real.sqrt N) 2 d, Real.sq_sqrt hsq]
  have hsplit : (μ * Real.sqrt N / 8) ^ (2 * d)
      = ((1 : ℝ) / 8) ^ (2 * d) * (μ * Real.sqrt N) ^ (2 * d) := by
    rw [div_pow, div_pow]; ring
  have hle : ((1 : ℝ) / 8) ^ (2 * d) ≤ 1 / 64 := by
    have : ((1 : ℝ) / 8) ^ (2 * d) ≤ ((1 : ℝ) / 8) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [this]
  have hApos : (0 : ℝ) ≤ μ ^ (2 * d) * (N : ℝ) ^ d := by positivity
  have hV := unitBallVol_pos d
  rw [hsplit, hrpow]
  nlinarith [mul_le_mul_of_nonneg_right hle hApos]

end DiscretePR
