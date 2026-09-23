import DiscretePhaseRetrieval.BlockEstimate
import DiscretePhaseRetrieval.Limit
import DiscretePhaseRetrieval.ContinuousPR

/-!
# Theorem 1.1: uniformly discrete phase retrieval for the mixed-level polyanalytic Fock spaces

Assembly (paper §4, last paragraph), for the space `𝓕_h` of a nonzero finite family of level
weights `h`. Put `L = levelBound h` (the largest `‖q‖₁` with `h_q ≠ 0`), `N₁ = max(3L, L+9)`,
`N_* = max(16d, N₁, d)` and `N_j = N_* · 100^j`; take the block sets `S_j ⊆ ℂ^d` of
`block_norming` at `N_j` and `S = ⋃_j S_j`.
* Separation `4√d/10⁷ = 4μ√d/10⁵` in the comparator's `euclideanDist`: inside a block by
  `blockSep_ge` (`N_j ≥ 16d`), between blocks by `union_separated`
  (`μ√N_0/4 ≥ 4μ√d/10⁵` as `N_0 ≥ d`).
* Phase retrieval: for `f, g ∈ PolyFockSpace h` with coefficient vectors `F, G`, `|f| = |g|` on
  `S` kills the first term of `block_estimate` at every `N_j`; with `exponent_neg` the
  remainder is `ε_j = C N_j^c e^{−N_j/10} max(‖F‖,‖G‖)² → 0`; `norm_eq_of_blocks` gives
  `|F| = |G|` on `ℂ^d`; `continuous_phase_retrieval` gives `θ`.
The choice of the sequence is local to this proof.  The single-level space `𝓕^d_q` is the case
`h = Finsupp.single q 1` (`DiscretePhaseRetrieval_single`).
-/

open MeasureTheory Metric Filter Topology DiscreteNorming PolyFock

namespace DiscretePR

/-- Coefficient-level form of Theorem 1.1.  This is the common core used both by
the function-space theorem below and by the comparator bridge in `Check.lean`. -/
theorem DiscretePhaseRetrieval_coefficients
    (d : ℕ) (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0) :
    ∃ S : Set (Fin d → ℂ),
      UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧
        ∀ F G : PolyFock d,
          (∀ s ∈ S, ‖polyanalyticEval h F s‖ = ‖polyanalyticEval h G s‖) →
            ∃ θ : ℂ, ‖θ‖ = 1 ∧ polyanalyticEval h F = θ • polyanalyticEval h G := by
  classical
  obtain ⟨C, c, hC0, hBE⟩ := block_estimate hd h
  -- the sequence `N_j = N_* · 100^j`, with all the facts we need about it
  obtain ⟨Nseq, hNpos, h16, hN1, hgrow, hNtend⟩ :
      ∃ Nseq : ℕ → ℕ, (∀ j, 0 < Nseq j) ∧ (∀ j, 16 * d ≤ Nseq j) ∧
        (∀ j, max (3 * levelBound h) (levelBound h + 9) ≤ Nseq j) ∧
        (∀ j, 100 * Nseq j ≤ Nseq (j + 1)) ∧
        Tendsto (fun j ↦ (Nseq j : ℝ)) atTop atTop := by
    set A : ℕ := max (max (16 * d) (max (3 * levelBound h) (levelBound h + 9))) 1 with hA
    have hApos : 0 < A := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
    have hpow : ∀ j : ℕ, 1 ≤ 100 ^ j := fun j ↦ Nat.one_le_pow _ _ (by norm_num)
    have hAle : ∀ j, A ≤ A * 100 ^ j := by
      intro j
      nth_rewrite 1 [← mul_one A]
      gcongr
      exact hpow j
    refine ⟨fun j ↦ A * 100 ^ j, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, ?_⟩
    · exact Nat.mul_pos hApos (pow_pos (by norm_num) j)
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hAle j)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hAle j)
    · exact le_of_eq (by ring)
    · refine tendsto_natCast_atTop_iff.mpr ?_
      refine tendsto_atTop_mono (fun j ↦ ?_) tendsto_id
      calc j ≤ 100 ^ j := (Nat.lt_pow_self (by norm_num)).le
        _ ≤ A * 100 ^ j := by
              nth_rewrite 1 [← one_mul (100 ^ j)]
              gcongr
              exact hApos
  -- the block sets
  have hSex := fun j ↦ block_norming hd h hnonzero (hNpos j)
  choose S hSsub hSsep hSnorm using hSex
  refine ⟨⋃ j, ((S j : Finset (Fin d → ℂ)) : Set (Fin d → ℂ)), ?_, ?_⟩
  · -- separation
    have hδ : 4 * mu * Real.sqrt d / 10 ^ 5 ≤ mu * Real.sqrt (Nseq 0) / 4 := by
      have hcast : ((16 * d : ℕ) : ℝ) ≤ ((Nseq 0 : ℕ) : ℝ) := Nat.cast_le.mpr (h16 0)
      push_cast at hcast
      have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have hd0 : (d : ℝ) ≤ (Nseq 0 : ℝ) := by linarith
      have hsq : Real.sqrt (d : ℝ) ≤ Real.sqrt (Nseq 0 : ℝ) := Real.sqrt_le_sqrt hd0
      have hs0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      simp only [mu]
      linarith
    have hsepU := union_separated (d := d) mu_pos Nseq (hNpos 0) hgrow
      (fun j ↦ ((S j : Finset (Fin d → ℂ)) : Set (Fin d → ℂ)))
      (fun j z hz ↦ hSsub j z (Finset.mem_coe.mp hz))
      (δ := 4 * mu * Real.sqrt d / 10 ^ 5)
      (fun j z hz w hw hzw ↦ (blockSep_ge hd h hnonzero (h16 j)).trans
        (hSsep j z (Finset.mem_coe.mp hz) w (Finset.mem_coe.mp hw) hzw)) hδ
    have hval : 4 * mu * Real.sqrt d / 10 ^ 5 = 4 * Real.sqrt d / 10 ^ 7 := by
      simp only [mu]; ring
    intro z hz w hw hzw
    have hfin := hsepU z hz w hw hzw
    rwa [hval] at hfin
  · -- phase retrieval for coefficient expansions
    intro F G hff'
    refine continuous_phase_retrieval hd h hnonzero F G ?_
    set M : ℝ := max ‖F‖ ‖G‖ with hM
    refine norm_eq_of_blocks h F G Nseq hNtend
      (fun j ↦ C * (Nseq j : ℝ) ^ c * Real.exp (-(1 / 10) * (Nseq j : ℝ)) * M ^ 2) ?_ ?_
    · -- `ε_j → 0`
      have hdiv : Tendsto (fun j ↦ (Nseq j : ℝ) / 10) atTop atTop :=
        hNtend.atTop_div_const (by norm_num)
      have h1 : Tendsto
          (fun j ↦ ((Nseq j : ℝ) / 10) ^ c * Real.exp (-((Nseq j : ℝ) / 10))) atTop (𝓝 0) :=
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero c).comp hdiv
      have h2 := h1.const_mul (C * 10 ^ c * M ^ 2)
      rw [mul_zero] at h2
      refine Filter.Tendsto.congr (fun j ↦ ?_) h2
      have h10 : ((10 : ℝ) ^ c) ≠ 0 := by positivity
      rw [div_pow, show -((Nseq j : ℝ) / 10) = -(1 / 10) * (Nseq j : ℝ) by ring]
      field_simp
    · -- the block bound
      intro j z hz
      obtain ⟨y, hyS, hy⟩ :=
        hBE (Nseq j) (hN1 j) (hNpos j) (S j) (hSsub j) (hSnorm j) F G z hz
      have hmem : y ∈ ⋃ j, ((S j : Finset (Fin d → ℂ)) : Set (Fin d → ℂ)) :=
        Set.mem_iUnion.mpr ⟨j, Finset.mem_coe.mpr hyS⟩
      have hyy : ‖polyanalyticEval h F y‖ ^ 2 - ‖polyanalyticEval h G y‖ ^ 2 = 0 := by
        rw [hff' y hmem]; ring
      rw [hyy, abs_zero, mul_zero, zero_add] at hy
      refine hy.trans ?_
      have hexp : Real.exp ((mu ^ 2 / 2 + 9 / 2 + Real.log mu) * (Nseq j : ℝ))
          ≤ Real.exp (-(1 / 10) * (Nseq j : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have hNn : (0 : ℝ) ≤ (Nseq j : ℝ) := Nat.cast_nonneg _
        nlinarith [exponent_neg]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg M)
      exact mul_le_mul_of_nonneg_left hexp (mul_nonneg hC0 (by positivity))

/-- **Theorem 1.1**, in the vocabulary of `Definitions.lean`. -/
theorem DiscretePhaseRetrieval_proved
    (d : ℕ) (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0) :
    ∃ S : Set (Fin d → ℂ),
      UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧
        PhaseRetrievalSet (PolyFockSpace h) S := by
  obtain ⟨S, hSsep, hSphase⟩ := DiscretePhaseRetrieval_coefficients d hd h hnonzero
  refine ⟨S, hSsep, ?_⟩
  intro f hf g hg hfg
  obtain ⟨-, -, F, rfl⟩ := hf
  obtain ⟨-, -, G, rfl⟩ := hg
  exact hSphase F G hfg

/-- The true polyanalytic Fock space `𝓕^d_q` at Landau level `q` is the case
`h = Finsupp.single q 1` of the main theorem. -/
theorem DiscretePhaseRetrieval_single (d : ℕ) (hd : 0 < d) (q : Fin d → ℕ) :
    ∃ S : Set (Fin d → ℂ),
      UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧
        PhaseRetrievalSet (PolyFockSpace (Finsupp.single q 1)) S :=
  DiscretePhaseRetrieval_proved d hd _ (Finsupp.single_ne_zero.mpr one_ne_zero)

end DiscretePR
