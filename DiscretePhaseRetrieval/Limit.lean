import DiscretePhaseRetrieval.Coefficients
import DiscretePhaseRetrieval.Annulus

/-!
# Claims L2, S1, S2: passing to the limit, and the union of the blocks

* L2: if `||F_{N_j}|² − |G_{N_j}|²| ≤ ε_j` on `B_{μ√N_j}` with `N_j → ∞`, `ε_j → 0`, then
  `|F| = |G|` on `ℂ^d` (for fixed `z`, eventually `z ∈ B_{μ√N_j}`, and `F_N(z) → F(z)`).
* S1: for `N' ≥ 100 N` the blocks `A_{N,μ}` and `A_{N',μ}` are at distance `≥ μ√N/4`
  (`|w| ≥ μ√N'/8 ≥ 10 μ√N/8` and `|z| ≤ μ√N`).
* S2: a union of `δ`-separated subsets of blocks along a sequence with `N_{j+1} ≥ 100 N_j` is
  `δ`-separated as soon as `δ ≤ μ√N_0/4`.

All three statements are about points `z w : Fin d → ℂ` and the comparator's `euclideanDist`;
the block is described by `mem_annulus_ofC`.
-/

open MeasureTheory Metric Filter Topology DiscreteNorming PolyFock

namespace DiscretePR

variable {d : ℕ}

/-- `μ = 1/100` is positive. -/
theorem mu_pos : (0 : ℝ) < mu := by norm_num [mu]

/-- `√(100 x) = 10 √x`. -/
private theorem sqrt_hundred_mul (x : ℝ) :
    Real.sqrt (100 * x) = 10 * Real.sqrt x := by
  have h100 : Real.sqrt 100 = 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 100) x, h100]

/-- L2. -/
theorem norm_eq_of_blocks (h : (Fin d → ℕ) →₀ ℂ) (F G : PolyFock d) (Nseq : ℕ → ℕ)
    (hN : Tendsto (fun j ↦ (Nseq j : ℝ)) atTop atTop) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hblock : ∀ j (z : Fin d → ℂ), euclideanDist z 0 < mu * Real.sqrt (Nseq j) →
      |‖polyanalyticEval h (truncate (Nseq j) F) z‖ ^ 2
        - ‖polyanalyticEval h (truncate (Nseq j) G) z‖ ^ 2| ≤ ε j) :
    ∀ z, ‖polyanalyticEval h F z‖ = ‖polyanalyticEval h G z‖ := by
  have hmu : (0 : ℝ) < mu := mu_pos
  -- `N_j → ∞` as a sequence of naturals
  have hNat : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  intro z
  set A := polyanalyticEval h F z with hA
  set B := polyanalyticEval h G z with hB
  -- `|F_{N_j}(z)|² → |F(z)|²` and likewise for `G`
  have ha : Tendsto
      (fun j ↦ ‖polyanalyticEval h (truncate (Nseq j) F) z‖ ^ 2) atTop (𝓝 (‖A‖ ^ 2)) :=
    (((tendsto_truncate h F z).comp hNat).norm).pow 2
  have hb : Tendsto
      (fun j ↦ ‖polyanalyticEval h (truncate (Nseq j) G) z‖ ^ 2) atTop (𝓝 (‖B‖ ^ 2)) :=
    (((tendsto_truncate h G z).comp hNat).norm).pow 2
  -- eventually `z` lies in the ball `B_{μ√N_j}`, so the hypothesis applies
  have hev : ∀ᶠ j in atTop,
      |‖polyanalyticEval h (truncate (Nseq j) F) z‖ ^ 2
        - ‖polyanalyticEval h (truncate (Nseq j) G) z‖ ^ 2| ≤ ε j := by
    filter_upwards [hN.eventually_gt_atTop ((euclideanDist z 0 / mu) ^ 2)] with j hj
    refine hblock j z ?_
    have hlt : euclideanDist z 0 / mu < Real.sqrt (Nseq j) :=
      (Real.lt_sqrt (div_nonneg (euclideanDist_zero_nonneg z) hmu.le)).mpr hj
    have : mu * (euclideanDist z 0 / mu) < mu * Real.sqrt (Nseq j) := by
      exact mul_lt_mul_of_pos_left hlt hmu
    rwa [mul_div_cancel₀ _ hmu.ne'] at this
  -- hence `||F(z)|² − |G(z)|²| ≤ 0`
  have hlim : Tendsto
      (fun j ↦ |‖polyanalyticEval h (truncate (Nseq j) F) z‖ ^ 2
        - ‖polyanalyticEval h (truncate (Nseq j) G) z‖ ^ 2|) atTop
      (𝓝 |‖A‖ ^ 2 - ‖B‖ ^ 2|) := (ha.sub hb).abs
  have hle : |‖A‖ ^ 2 - ‖B‖ ^ 2| ≤ 0 := le_of_tendsto_of_tendsto hlim hε hev
  have hsq : ‖A‖ ^ 2 = ‖B‖ ^ 2 := by
    have := abs_nonneg (‖A‖ ^ 2 - ‖B‖ ^ 2)
    have h0 : ‖A‖ ^ 2 - ‖B‖ ^ 2 = 0 := by
      have := abs_eq_zero.mp (le_antisymm hle this)
      exact this
    linarith
  calc ‖A‖ = Real.sqrt (‖A‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖B‖ ^ 2) := by rw [hsq]
    _ = ‖B‖ := Real.sqrt_sq (norm_nonneg _)

/-- S1. -/
theorem annuli_far {μ : ℝ} (hμ : 0 < μ) {N N' : ℕ} (hN : 0 < N) (h : 100 * N ≤ N')
    {z w : Fin d → ℂ} (hz : ofC z ∈ annulus d μ N) (hw : ofC w ∈ annulus d μ N') :
    μ * Real.sqrt N / 4 ≤ euclideanDist z w := by
  rw [mem_annulus_ofC] at hz hw
  obtain ⟨-, hz2⟩ := hz
  obtain ⟨hw1, -⟩ := hw
  -- `√N' ≥ 10 √N`
  have hcast : (100 * N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast h
  have h10 : 10 * Real.sqrt N ≤ Real.sqrt N' := by
    calc 10 * Real.sqrt N = Real.sqrt (100 * N) := (sqrt_hundred_mul (N : ℝ)).symm
      _ ≤ Real.sqrt N' := Real.sqrt_le_sqrt hcast
  have key : μ * (10 * Real.sqrt N) ≤ μ * Real.sqrt N' :=
    mul_le_mul_of_nonneg_left h10 hμ.le
  -- `euclideanDist z w ≥ |w| − |z|`
  have hd : euclideanDist w 0 - euclideanDist z 0 ≤ euclideanDist z w := by
    rw [euclideanDist_eq_dist z w, ← norm_ofC, ← norm_ofC, dist_comm, dist_eq_norm]
    exact norm_sub_norm_le _ _
  linarith

/-- S2. -/
theorem union_separated {μ : ℝ} (hμ : 0 < μ) (Nseq : ℕ → ℕ) (hN0 : 0 < Nseq 0)
    (hgrow : ∀ j, 100 * Nseq j ≤ Nseq (j + 1)) (S : ℕ → Set (Fin d → ℂ))
    (hS : ∀ j, ∀ z ∈ S j, ofC z ∈ annulus d μ (Nseq j)) {δ : ℝ}
    (hsep : ∀ j, ∀ z ∈ S j, ∀ w ∈ S j, z ≠ w → δ ≤ euclideanDist z w)
    (hδ : δ ≤ μ * Real.sqrt (Nseq 0) / 4) :
    ∀ z ∈ ⋃ j, S j, ∀ w ∈ ⋃ j, S j, z ≠ w → δ ≤ euclideanDist z w := by
  have hmono : Monotone Nseq :=
    monotone_nat_of_le_succ fun j ↦ le_trans (by omega) (hgrow j)
  have hpos : ∀ j, 0 < Nseq j := fun j ↦ lt_of_lt_of_le hN0 (hmono (Nat.zero_le j))
  -- points in blocks with different indices are far apart
  have hfar : ∀ i j, i < j → ∀ z ∈ S i, ∀ w ∈ S j, δ ≤ euclideanDist z w := by
    intro i j hij z hz w hw
    have h100 : 100 * Nseq i ≤ Nseq j := le_trans (hgrow i) (hmono hij)
    have hfar' : μ * Real.sqrt (Nseq i) / 4 ≤ euclideanDist z w :=
      annuli_far hμ (hpos i) h100 (hS i z hz) (hS j w hw)
    refine le_trans (le_trans hδ ?_) hfar'
    have hle : ((Nseq 0 : ℕ) : ℝ) ≤ ((Nseq i : ℕ) : ℝ) :=
      Nat.cast_le.mpr (hmono (Nat.zero_le i))
    gcongr
  intro z hz w hw hzw
  simp only [Set.mem_iUnion] at hz hw
  obtain ⟨i, hzi⟩ := hz
  obtain ⟨j, hwj⟩ := hw
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact hfar i j hij z hzi w hwj
  · exact hsep i z hzi w hwj hzw
  · rw [euclideanDist_comm]
    exact hfar j i hij w hwj z hzi

end DiscretePR
