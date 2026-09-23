import DiscretePhaseRetrieval.Polynomials
import DiscretePhaseRetrieval.Annulus
import DiscreteNorming.Main

/-!
# Claims B1, B2: Proposition 2.1 on one block (paper p. 5–6)

* B1: `discrete_norming_explicit` applied to `Ω = A_{N,μ}` (A1–A3) and `𝒱 = V_h^N`
  (P2, P3) gives a `blockSep d h N`-separated `S_{N,μ} ⊆ A_{N,μ}` with
  `‖|F|² − |G|²‖_{L∞(B_{μ√N})} ≤ e^{4(N+L)} ‖|F|² − |G|²‖_{L∞(S_{N,μ})}` for `F, G ∈ V_h^N`,
  `L = levelBound h` (the ball lies in the hull, A1).  The sample set is returned as a
  `Finset (Fin d → ℂ)` (`S.image toC`), separated in the comparator's `euclideanDist`;
  membership in the block is `ofC z ∈ annulus d mu N`, i.e.
  `mu √N / 8 ≤ euclideanDist z 0 < mu √N` (`mem_annulus_ofC`).
* B2: `blockSep d h N ≥ (μ√N/16)(63/64 / (3·10⁵(1+d)))^{1/(2d)} C(N+d,d)^{−1/(2d)} ≥ 4μ√d/10⁵`
  (A3, P3, P4) for `N ≥ 16 d` (the paper's "sufficiently large `N`"; `d = 1` is the binding case).

Both need `h ≠ 0`: it is what makes `V_h^N` nonzero (`one_le_finrank_VhN`), and the
`finrank`-factor of `blockSep` is a *lower* bound only for a nonzero dimension.
-/

open MeasureTheory Metric DiscreteNorming PolyFock PolyFock.Fock

namespace DiscretePR

variable {d : ℕ}

/-! ### rpow helpers -/

private lemma rpow_two_mul_inv (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 * d)) ^ (1 / (2 * (d : ℝ))) = x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [← Real.rpow_natCast x (2 * d), ← Real.rpow_mul hx]
  push_cast
  rw [show (2 * (d : ℝ)) * (1 / (2 * (d : ℝ))) = 1 by field_simp]
  exact Real.rpow_one x

private lemma rpow_pow_half (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ d) ^ (1 / (2 * (d : ℝ))) = Real.sqrt x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [← Real.rpow_natCast x d, ← Real.rpow_mul hx,
    show (d : ℝ) * (1 / (2 * (d : ℝ))) = 1 / 2 by field_simp, ← Real.sqrt_eq_rpow]

/-! ### the numeric core -/

private lemma log_610000_le : Real.log (61 * 10 ^ 4 : ℝ) ≤ 13.4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have hA : (442413 : ℝ) ≤ Real.exp 13 := by
    simpa using le_exp_nat (n := 13) (by norm_num)
  have hB : (1.4 : ℝ) ≤ Real.exp 0.4 := by
    have := Real.add_one_le_exp (0.4 : ℝ)
    linarith
  have hsplit : Real.exp (13.4 : ℝ) = Real.exp 13 * Real.exp 0.4 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [hA, hB, Real.exp_pos 13, Real.exp_pos 0.4]

private lemma base_rpow_ge (d : ℕ) (hd : 0 < d) :
    (12 / 10 ^ 4 : ℝ) ≤ (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) ^ (1 / (2 * (d : ℝ))) := by
  rcases Nat.lt_or_ge d 2 with h2 | h2
  · -- `d = 1`
    have hd1 : d = 1 := by omega
    subst hd1
    rw [show (63 : ℝ) / 64 / (3 * 10 ^ 5 * (1 + ((1 : ℕ) : ℝ))) = 63 / 38400000 by norm_num,
      show (1 : ℝ) / (2 * ((1 : ℕ) : ℝ)) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    norm_num
  · -- `d ≥ 2`
    have hd0 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2
    have hbpos : (0 : ℝ) < 63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ))) := by positivity
    rw [Real.rpow_def_of_pos hbpos]
    -- a lower bound on `exp (-4)`
    have he4 : Real.exp 4 ≤ 55 := by
      simpa using exp_nat_le (n := 4) (by norm_num)
    have hstep : (12 / 10 ^ 4 : ℝ) ≤ Real.exp (-4) := by
      have hp : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
      rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ hp]
      nlinarith [he4]
    refine hstep.trans (Real.exp_le_exp.mpr ?_)
    -- `-4 ≤ log b / (2d)`
    have hbge : 1 / (61 * 10 ^ 4 * (d : ℝ)) ≤ 63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hd0]
    have hlogb : -(13.4 + ((d : ℝ) - 1)) ≤ Real.log (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) := by
      have h1 := Real.log_le_log (show (0:ℝ) < 1 / (61 * 10 ^ 4 * (d : ℝ)) by positivity) hbge
      have h2 : Real.log (1 / (61 * 10 ^ 4 * (d : ℝ)))
          = -(Real.log (61 * 10 ^ 4 : ℝ) + Real.log (d : ℝ)) := by
        rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (by positivity)]
      rw [h2] at h1
      have h3 : Real.log (d : ℝ) ≤ (d : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      have h4 := log_610000_le
      linarith
    have hu : (0 : ℝ) < 1 / (2 * (d : ℝ)) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hlogb hu.le
    refine le_trans ?_ hmul
    have hbound : (13.4 + ((d : ℝ) - 1)) * (1 / (2 * (d : ℝ))) ≤ 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    have heq : -(13.4 + ((d : ℝ) - 1)) * (1 / (2 * (d : ℝ)))
        = -((13.4 + ((d : ℝ) - 1)) * (1 / (2 * (d : ℝ)))) := by ring
    rw [heq]
    linarith

/-- B1: the block sampling set. -/
theorem block_norming (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0) {N : ℕ}
    (hN : 0 < N) :
    ∃ S : Finset (Fin d → ℂ), (∀ z ∈ S, ofC z ∈ annulus d mu N) ∧
      (∀ z ∈ S, ∀ w ∈ S, z ≠ w → blockSep d h N ≤ euclideanDist z w) ∧
      ∀ F ∈ VhN h N, ∀ G ∈ VhN h N, ∀ z : Fin d → ℂ,
        euclideanDist z 0 < mu * Real.sqrt N → ∃ w ∈ S,
          |‖ev z F‖ ^ 2 - ‖ev z G‖ ^ 2|
            ≤ Real.exp (4 * (N + levelBound h)) * |‖ev w F‖ ^ 2 - ‖ev w G‖ ^ 2| := by
  classical
  have hmu : (0 : ℝ) < mu := by norm_num [mu]
  obtain ⟨S, hSΩ, hSsep, hSnorm⟩ :=
    discrete_norming_explicit (d := d) (n := N + levelBound h)
      (N := Module.finrank ℂ (VhN h N)) hd
      (annulus_measurable d mu N) (annulus_bounded d mu N)
      (annulus_vol_pos hd hmu hN) (annulus_hull_defect hd hmu hN)
      (𝒱 := VhN h N) (fun F hF => totalDegree_le_of_mem_VhN hF) rfl
      (one_le_finrank_VhN hnonzero N)
  refine ⟨S.image toC, ?_, ?_, ?_⟩
  · -- the sample points lie in the block
    intro z hz
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hz
    rw [ofC_toC]
    exact hSΩ (Finset.mem_coe.mpr hxS)
  · -- separation
    intro z hz w hw hzw
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hw
    rw [euclideanDist_eq_dist, ofC_toC, ofC_toC]
    exact hSsep x hxS y hyS fun hxy => hzw (by rw [hxy])
  · -- the norming inequality
    intro F hF G hG z hz
    have hx : ofC z ∈ ball (0 : Pt d) (mu * Real.sqrt N) := by
      rw [mem_ball_zero_iff, norm_ofC]
      exact hz
    obtain ⟨y, hy, hle⟩ := hSnorm F hF G hG (ofC z)
      (ball_subset_hull_annulus hd hmu hN hx)
    refine ⟨toC y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    simp only [DiscreteNorming.diff, toC_ofC] at hle
    convert hle using 3
    push_cast
    ring

/-- B2: the separation on the block is at least `4μ√d/10⁵` once `N ≥ 16 d`. -/
theorem blockSep_ge (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0) {N : ℕ}
    (hN : 16 * d ≤ N) :
    4 * mu * Real.sqrt d / 10 ^ 5 ≤ blockSep d h N := by
  have hmu : (0 : ℝ) < mu := by norm_num [mu]
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdR0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hNnat : 0 < N := by omega
  have hNR : (16 : ℝ) * (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNR0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hball := unitBallVol_pos d
  have hc : (0 : ℝ) < 3 * 10 ^ 5 * (1 + (d : ℝ)) := by positivity
  -- Step 1: lower bound for `deltaPaper`
  have hdelta : 1 / 16 * (mu * Real.sqrt N) *
      (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) ^ (1 / (2 * (d : ℝ)))
      ≤ deltaPaper d (annulus d mu N) := by
    have h1 : 63 / 64 * mu ^ (2 * d) * (N : ℝ) ^ d * unitBallVol d ≤ vol (annulus d mu N) :=
      annulus_vol_ge hd hmu hNnat
    have h2 : mu ^ (2 * d) * (N : ℝ) ^ d * (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ))))
        ≤ vol (annulus d mu N) / unitBallVol d / (3 * 10 ^ 5 * (1 + (d : ℝ))) := by
      rw [le_div_iff₀ hc, le_div_iff₀ hball]
      have hrw : mu ^ (2 * d) * (N : ℝ) ^ d * (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) *
          (3 * 10 ^ 5 * (1 + (d : ℝ))) * unitBallVol d
          = 63 / 64 * mu ^ (2 * d) * (N : ℝ) ^ d * unitBallVol d := by
        field_simp
      rw [hrw]
      exact h1
    have h3 := Real.rpow_le_rpow (z := 1 / (2 * (d : ℝ)))
      (by positivity) h2 (by positivity)
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      rpow_two_mul_inv hd hmu.le, rpow_pow_half hd (le_of_lt hNR0)] at h3
    rw [deltaPaper]
    nlinarith [h3]
  -- Step 2: lower bound for the `finrank` factor
  have hK : (0 : ℝ) < ((N : ℝ) + d) * Real.exp 1 / d := by positivity
  have hR1 : (1 : ℝ) ≤ (Module.finrank ℂ (VhN h N) : ℝ) := by
    exact_mod_cast one_le_finrank_VhN hnonzero N
  have hRK : (Module.finrank ℂ (VhN h N) : ℝ) ≤ (((N : ℝ) + d) * Real.exp 1 / d) ^ d := by
    have h1 : (Module.finrank ℂ (VhN h N) : ℝ) ≤ ((N + d).choose d : ℝ) := by
      exact_mod_cast finrank_VhN_le h N
    exact h1.trans (choose_le_pow_mul_exp N hd)
  have hfin : (Real.sqrt (((N : ℝ) + d) * Real.exp 1 / d))⁻¹
      ≤ (Module.finrank ℂ (VhN h N) : ℝ) ^ (-(1 / (2 * (d : ℝ)))) := by
    have h2 := Real.rpow_le_rpow_of_nonpos (z := -(1 / (2 * (d : ℝ))))
      (by linarith : (0:ℝ) < (Module.finrank ℂ (VhN h N) : ℝ)) hRK
      (by simp only [neg_nonpos]; positivity)
    rw [← Real.rpow_natCast (((N : ℝ) + d) * Real.exp 1 / d) d, ← Real.rpow_mul hK.le,
      show (d : ℝ) * (-(1 / (2 * (d : ℝ)))) = -(1 / 2) by field_simp,
      Real.rpow_neg hK.le, ← Real.sqrt_eq_rpow] at h2
    exact h2
  -- Step 3: combine
  have hcomb : (1 / 16 * (mu * Real.sqrt N) *
      (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) ^ (1 / (2 * (d : ℝ)))) *
      (Real.sqrt (((N : ℝ) + d) * Real.exp 1 / d))⁻¹ ≤ blockSep d h N := by
    rw [blockSep]
    refine mul_le_mul hdelta hfin (by positivity) ?_
    refine le_trans ?_ hdelta
    positivity
  refine le_trans ?_ hcomb
  -- Step 4: the numerics
  set S : ℝ := Real.sqrt ((N : ℝ) / (((N : ℝ) + d) * Real.exp 1)) with hSdef
  have hden : (0 : ℝ) < ((N : ℝ) + d) * Real.exp 1 := by positivity
  have hS : (588 / 1000 : ℝ) ≤ S := by
    rw [hSdef]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hden]
    nlinarith [Real.exp_one_lt_d9,
      mul_le_mul_of_nonneg_left Real.exp_one_lt_d9.le
        (show (0:ℝ) ≤ (N : ℝ) + d by positivity)]
  have hB := base_rpow_ge d hd
  have hkey : (4 : ℝ) / 10 ^ 5 ≤ 1 / 16 *
      (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) ^ (1 / (2 * (d : ℝ))) * S := by
    nlinarith [hB, hS]
  have hsq : Real.sqrt N * (Real.sqrt (((N : ℝ) + d) * Real.exp 1 / d))⁻¹
      = Real.sqrt d * S := by
    rw [← Real.sqrt_inv, inv_div, hSdef,
      ← Real.sqrt_mul (Nat.cast_nonneg N), ← Real.sqrt_mul (Nat.cast_nonneg d)]
    congr 1
    field_simp
  calc 4 * mu * Real.sqrt d / 10 ^ 5 = (4 / 10 ^ 5) * (mu * Real.sqrt d) := by ring
    _ ≤ (1 / 16 * (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) ^ (1 / (2 * (d : ℝ))) * S) *
        (mu * Real.sqrt d) := by
      exact mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 1 / 16 * (mu * (Real.sqrt d * S)) *
        (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) ^ (1 / (2 * (d : ℝ))) := by ring
    _ = (1 / 16 * (mu * Real.sqrt N) *
        (63 / 64 / (3 * 10 ^ 5 * (1 + (d : ℝ)))) ^ (1 / (2 * (d : ℝ)))) *
        (Real.sqrt (((N : ℝ) + d) * Real.exp 1 / d))⁻¹ := by rw [← hsq]; ring

end DiscretePR
