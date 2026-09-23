import DiscretePhaseRetrieval.TailBound
import DiscretePhaseRetrieval.BlockNorming

/-!
# Claims C and X: the combined block estimate (paper p. 6)

For a block sampling set `S` with the norming property of B1, and any `F, G ∈ 𝓕_h`
(coefficient vectors), on `B_{μ√N}` (`L = levelBound h`):

    ‖|F_N|² − |G_N|²‖_{L∞(B_{μ√N})}
      ≤ e^{4(N+L)} ‖|F|² − |G|²‖_{L∞(S)} + C N^{c} e^{(μ²/2 + 9/2 + log μ) N} max(‖F‖,‖G‖)²,

by the triangle inequality `||F_N|²−|G_N|²| ≤ ||F|²−|G|²| + ||F|²−|F_N|²| + ||G|²−|G_N|²|` on
`S ⊆ B_{μ√N}`, E2 for the last two terms (note `e^{4(N+L)} e^{(μ²/2+1/2+log μ)N}` is
`e^{4L} e^{(μ²/2 + 9/2 + log μ)N}`), and B1 for `F_N, G_N ∈ V_h^N`.

X: with `μ = 1/100`, `μ²/2 + 9/2 + log μ ≤ −1/10`.
-/

open MeasureTheory Metric DiscreteNorming PolyFock PolyFock.Fock

namespace DiscretePR

variable {d : ℕ}

/-- X. -/
theorem exponent_neg : mu ^ 2 / 2 + 9 / 2 + Real.log mu ≤ -1 / 10 := by
  -- `log 100 ≥ 4.60005`, via `log 100 = 7 log 2 − log (32/25)` and `log (32/25) ≤ 16 · 0.0157`.
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hr : (32 / 25 : ℝ) ≤ (1.0157 : ℝ) ^ 16 := by norm_num
  have hlogr : Real.log (1.0157 : ℝ) ≤ 0.0157 := by
    have := Real.log_le_sub_one_of_pos (x := (1.0157 : ℝ)) (by norm_num)
    linarith
  have h32 : Real.log (32 / 25 : ℝ) ≤ 0.2512 := by
    calc Real.log (32 / 25 : ℝ) ≤ Real.log ((1.0157 : ℝ) ^ 16) :=
          Real.log_le_log (by norm_num) hr
      _ = 16 * Real.log (1.0157 : ℝ) := by rw [Real.log_pow]; norm_num
      _ ≤ 16 * 0.0157 := by linarith
      _ = 0.2512 := by norm_num
  have h100 : Real.log 100 = 7 * Real.log 2 - Real.log (32 / 25 : ℝ) := by
    have he : (100 : ℝ) = 2 ^ 7 / (32 / 25) := by norm_num
    rw [he, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hmu : Real.log mu = - Real.log 100 := by
    simp only [mu]
    rw [show (1 / 100 : ℝ) = (100 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hmu]
  simp only [mu]
  norm_num
  linarith

/-- The arithmetic core of the block estimate: the triangle inequality
`|a′ − b′| ≤ |a − b| + |a − a′| + |b − b′|`, the two error bounds, and `u, v ≤ M`. -/
private lemma block_arith {P a a' b b' E T u v M : ℝ} (hP : P ≤ E * |a' - b'|)
    (hE : 0 ≤ E) (hT : 0 ≤ T) (ha : |a - a'| ≤ T * u) (hb : |b - b'| ≤ T * v)
    (hu : u ≤ M) (hv : v ≤ M) :
    P ≤ E * |a - b| + E * T * (2 * M) := by
  have t1 : |a' - b'| ≤ |a - b| + |a - a'| + |b - b'| := by
    have h1 := le_abs_self (a - b)
    have h2 := neg_abs_le (a - b)
    have h3 := le_abs_self (a - a')
    have h4 := neg_abs_le (a - a')
    have h5 := le_abs_self (b - b')
    have h6 := neg_abs_le (b - b')
    rw [abs_le]
    constructor <;> linarith
  have h2 : |a' - b'| ≤ |a - b| + T * u + T * v := by linarith
  have h3 : E * |a' - b'| ≤ E * (|a - b| + T * u + T * v) := mul_le_mul_of_nonneg_left h2 hE
  have h4 : T * u + T * v ≤ T * (2 * M) := by nlinarith
  have h5 : E * (T * u + T * v) ≤ E * (T * (2 * M)) := mul_le_mul_of_nonneg_left h4 hE
  calc P ≤ E * |a' - b'| := hP
    _ ≤ E * (|a - b| + T * u + T * v) := h3
    _ = E * |a - b| + E * (T * u + T * v) := by ring
    _ ≤ E * |a - b| + E * (T * (2 * M)) := by linarith
    _ = E * |a - b| + E * T * (2 * M) := by ring

/-- C: the combined block estimate. -/
theorem block_estimate (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) :
    ∃ C : ℝ, ∃ c : ℕ, 0 ≤ C ∧ ∀ N : ℕ, max (3 * levelBound h) (levelBound h + 9) ≤ N → 0 < N →
      ∀ S : Finset (Fin d → ℂ), (∀ z ∈ S, ofC z ∈ annulus d mu N) →
        (∀ F ∈ VhN h N, ∀ G ∈ VhN h N, ∀ z : Fin d → ℂ,
          euclideanDist z 0 < mu * Real.sqrt N → ∃ w ∈ S,
            |‖ev z F‖ ^ 2 - ‖ev z G‖ ^ 2|
              ≤ Real.exp (4 * (N + levelBound h)) * |‖ev w F‖ ^ 2 - ‖ev w G‖ ^ 2|) →
        ∀ (F G : PolyFock d), ∀ x : Fin d → ℂ,
          euclideanDist x 0 < mu * Real.sqrt N → ∃ y ∈ S,
            |‖polyanalyticEval h (truncate N F) x‖ ^ 2
                - ‖polyanalyticEval h (truncate N G) x‖ ^ 2|
              ≤ Real.exp (4 * (N + levelBound h))
                  * |‖polyanalyticEval h F y‖ ^ 2 - ‖polyanalyticEval h G y‖ ^ 2|
                + C * (N : ℝ) ^ c * Real.exp ((mu ^ 2 / 2 + 9 / 2 + Real.log mu) * N)
                  * max ‖F‖ ‖G‖ ^ 2 := by
  obtain ⟨C₀, c, hC₀, hE⟩ := modulus_error hd h
  refine ⟨2 * C₀ * Real.exp (4 * levelBound h), c, by positivity, ?_⟩
  intro N hN _hN0 S hS hnorm F G x hx
  -- B1 applied to the truncations `F_N, G_N ∈ V_h^N`.
  obtain ⟨y, hyS, hy⟩ := hnorm (truncPoly h N F) (truncPoly_mem h N F)
    (truncPoly h N G) (truncPoly_mem h N G) x hx
  refine ⟨y, hyS, ?_⟩
  have hdiff : ∀ z : Fin d → ℂ, ‖ev z (truncPoly h N F)‖ ^ 2 - ‖ev z (truncPoly h N G)‖ ^ 2
      = ‖polyanalyticEval h (truncate N F) z‖ ^ 2
        - ‖polyanalyticEval h (truncate N G) z‖ ^ 2 := by
    intro z
    simp only [eval_truncate]
  rw [hdiff x, hdiff y] at hy
  -- `y` lies in the annulus, hence in the ball `B_{μ√N}`, so E2 applies at `y`.
  have hrad : euclideanDist y 0 ≤ mu * Real.sqrt N :=
    ((mem_annulus_ofC y).1 (hS y hyS)).2.le
  have hFb := hE N hN F y hrad
  have hGb := hE N hN G y hrad
  -- the two elementary bounds feeding `block_arith`
  have hTnn : (0 : ℝ) ≤ C₀ * (N : ℝ) ^ c * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N) :=
    mul_nonneg (mul_nonneg hC₀ (by positivity)) (Real.exp_pos _).le
  have hMF : ‖F‖ ^ 2 ≤ max ‖F‖ ‖G‖ ^ 2 := by
    have hmx := le_max_left ‖F‖ ‖G‖
    nlinarith [norm_nonneg F]
  have hMG : ‖G‖ ^ 2 ≤ max ‖F‖ ‖G‖ ^ 2 := by
    have hmx := le_max_right ‖F‖ ‖G‖
    nlinarith [norm_nonneg G]
  -- `e^{4(N+L)} e^{(μ²/2+1/2+log μ)N} = e^{4L} e^{(μ²/2+9/2+log μ)N}`
  have hexp : Real.exp (4 * ((N : ℝ) + (levelBound h : ℝ)))
        * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N)
      = Real.exp (4 * (levelBound h : ℝ))
        * Real.exp ((mu ^ 2 / 2 + 9 / 2 + Real.log mu) * N) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hfinal : Real.exp (4 * ((N : ℝ) + (levelBound h : ℝ)))
        * (C₀ * (N : ℝ) ^ c * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N))
        * (2 * max ‖F‖ ‖G‖ ^ 2)
      = 2 * C₀ * Real.exp (4 * (levelBound h : ℝ)) * (N : ℝ) ^ c
        * Real.exp ((mu ^ 2 / 2 + 9 / 2 + Real.log mu) * N) * max ‖F‖ ‖G‖ ^ 2 := by
    linear_combination (2 * C₀ * (N : ℝ) ^ c * max ‖F‖ ‖G‖ ^ 2) * hexp
  calc |‖polyanalyticEval h (truncate N F) x‖ ^ 2
          - ‖polyanalyticEval h (truncate N G) x‖ ^ 2|
      ≤ Real.exp (4 * ((N : ℝ) + (levelBound h : ℝ)))
            * |‖polyanalyticEval h F y‖ ^ 2
                - ‖polyanalyticEval h G y‖ ^ 2|
          + Real.exp (4 * ((N : ℝ) + (levelBound h : ℝ)))
            * (C₀ * (N : ℝ) ^ c * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N))
            * (2 * max ‖F‖ ‖G‖ ^ 2) :=
        block_arith hy (Real.exp_pos _).le hTnn hFb hGb hMF hMG
    _ = Real.exp (4 * ((N : ℝ) + (levelBound h : ℝ)))
            * |‖polyanalyticEval h F y‖ ^ 2
                - ‖polyanalyticEval h G y‖ ^ 2|
          + 2 * C₀ * Real.exp (4 * (levelBound h : ℝ)) * (N : ℝ) ^ c
            * Real.exp ((mu ^ 2 / 2 + 9 / 2 + Real.log mu) * N) * max ‖F‖ ‖G‖ ^ 2 := by
        rw [hfinal]

end DiscretePR
