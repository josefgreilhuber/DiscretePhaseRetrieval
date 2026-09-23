# Theorem 1.1 (main theorem) — claim map

Each substantial claim of the proof of Theorem 1.1 (paper §4, using §3 and Prop. 2.1), with the
Lean declaration that proves it. Namespace `DiscretePR` unless noted. Status:
`planned` / `stated` (sorry) / `proved` / **`imported`** (proved in the earlier development `ContinuousPhaseRetrieval`, used through one bridge theorem).
Plan: `PLAN-MixedLevel-Main.md` (the level-`κ` version of the plan is `PLAN-MainTheorem.md`).

**The mixed-level spaces.** The theorem is stated for the polyanalytic Fock space `𝓕_h` of a
finitely supported family of level weights `h : (Fin d → ℕ) →₀ ℂ` (top-level `Definitions.lean`):
the basis is the normalized mixture
`Ψ_{n,h} = (∑_q |h_q|²)^{-1/2} ∑_{q ∈ supp g} h_q Φ_{n,q}` of the single-level basis elements, and
`PolyFockSpace h` is the corresponding function space. The single Landau level `q` of the paper
is the case `h = Finsupp.single q 1`. Two derived quantities replace `‖κ‖₁` throughout:
`levelBound h = max {‖q‖₁ : q ∈ supp g}` (the paper's `L`) and the normalisation
`hnorm h = (∑_q |h_q|²)^{1/2}` (`Defs.lean`). The hypothesis `h ≠ 0` is used only where a
*lower* bound on `dim V_h^N` is needed (P3, B1, B2) and in CPR.

**Status: complete.** The mixed-level development is sorry-free.  The main theorem is
`DiscretePR.DiscretePhaseRetrieval_proved` (`Main.lean`), with the reusable coefficient form
`DiscretePR.DiscretePhaseRetrieval_coefficients`.  Its comparator is
`DiscretePR_Showcase.DiscretePhaseRetrieval` in the top-level `Showcase.lean`; `Check.lean` proves
the bridge from polynomial weights to finitely supported level weights and from
`EuclideanSpace ℂ (Fin d)` to coordinate functions.  The same comparator now states the
complex polynomial-window STFT corollary `DiscretePR_Showcase.STFTPhaseRetrieval`;
`STFTComparatorBridge.lean` proves its window integrability and the corollary itself.  The
earlier level-`κ` version
(`PolyDiscreteSPR_proved` = `DiscretePR_Showcase.PolyDiscreteSPR`) was complete on 2026-09-03 and
depended only on `propext`, `Classical.choice`, `Quot.sound`; so does the bridge
`continuous_phase_retrieval`.

| # | claim (paper) | Lean declaration | file | status |
|---|---|---|---|---|
| P0 | the comparator's basis `Φ n q` (index order: coefficient multi-index first, Landau level second) is the polynomial evaluation `ev z (Psihat n q)` — the `PolyFock/` development is stated in that same basis, so no identification of two bases is needed; the same combination of levels on both sides identifies the mixed basis `Ψ n h` with `ev z (PsihatH n h)`; `toC`/`ofC` identify `Fin d → ℂ` with `ℝ^{2d}` isometrically, the comparator's `euclideanDist` being the distance of `Pt d` and `euclideanDist z 0` the norm; the sampling block read through `ofC` | `Phi_eq_ev`, `Psi_eq_ev`, `ofC`, `toC_ofC`, `ofC_toC`, `ofC_zero`, `euclideanDist_eq_dist`, `euclideanDist_comm`, `norm_ofC`, `euclideanDist_toC`, `mem_annulus_ofC` | `Bridge.lean` | proved |
| P1 | `Φ_{n,q}` is a polynomial in `z, z̄` of degree `‖n‖₁+‖q‖₁`, hence `Ψ_{n,h}` has degree `≤ ‖n‖₁ + L`, `L = levelBound h` (the size of a multi-index is `DiscretePR.size`, notation `‖·‖₁`, in `Auxiliary.lean`; the paper writes `|n|`) | `totalDegree_Psihat_le`, `totalDegree_PsihatH_le` | `Polynomials.lean` | proved |
| P2 | `V_h^N ⊆ Poly_{N+L}` | `totalDegree_le_of_mem_VhN` | `Polynomials.lean` | proved |
| P3 | `dim V_h^N = C(N+d,d)` (used as `1 ≤ dim ≤ C(N+d,d)`); the lower bound needs `h ≠ 0` and comes from pairing `Ψ_{α,h}` with `Φ_{α,q₀}`, `q₀ ∈ supp g`, under the Fock form, which returns `(hnorm h)⁻¹ h_{q₀} ≠ 0` (`PolyFock.Fock.form_Psihat` is orthonormality over **all** pairs `(n,q)`) | `form_PsihatH_Psihat`, `PsihatH_ne_zero`, `one_le_finrank_VhN`, `finrank_VhN_le` | `Polynomials.lean` | proved |
| P4 | `C(N+d,d) ≤ (N+d)^d e^d/d^d` | `choose_le_pow_mul_exp` | `Polynomials.lean` | proved |
| W | the coefficient series converges absolutely | `summable_Phi_sq`, `summable_Psi_sq` (`KernelBound.lean`), `summable_eval` | `Coefficients.lean` | proved |
| K | kernel bound `|F(z)| ≤ C(1+|z|)^{c} e^{|z|²/2}‖F‖` (the radius `|z|` is `euclideanDist z 0`) | `sum_sq_phi_le`, `kernel_bound` (one level), `sq_norm_Psi_le`, `kernel_bound_mixed` (Cauchy–Schwarz over `supp g`, polynomial factor at `L`), `eval_le`; the two pointwise inputs `sq_norm_phi_le_gen`, `sq_norm_phi_le_mid` are instances of the shared core estimate `PolyFock.norm_phi_le_of_term_le` (`PolyFock/PhiBound.lean`) | `KernelBound.lean` | proved |
| T | Lemma 3.1 for `F − F_N`, under `e·(euclideanDist z 0)² < N` | `tail_eval_le`, `tail_le_tailKernelDiag` (one level), `tail_le_tailKernelDiag_mixed`, `tailConstH`, `tail_bound_mixed`, `truncation_error`; `PolyFock.tail_bound`, `PolyFock.tail_bound_sqrt` (`PolyFock/TailBound.lean`, proved, also phrased with `euclideanDist z 0`) | `TailBound.lean` | proved |
| E1 | `||z|²−|w|²| ≤ 2 max(|z|,|w|)|z−w|` | `abs_sq_sub_sq_le` | `TailBound.lean` | proved |
| E2 | `‖|F|²−|F_N|²‖_{L∞(B_{μ√N})} ≤ C N^{c} e^{(μ²/2+1/2+log μ)N}‖F‖²`, the ball being `euclideanDist z 0 ≤ μ√N` | `modulus_error` | `TailBound.lean` | proved |
| A1 | `A_{N,μ}` bounded, measurable, positive measure; `Ω̂ = B̄_{μ√N}` | `annulus_measurable`, `annulus_bounded`, `annulus_vol_pos`, `hull_annulus_subset_closedBall`, `ball_subset_hull_annulus` | `Annulus.lean` | proved |
| A2 | `|Ω̂∖Ω| = 2^{−6d}|Ω̂| ≤ 2^{−4d−2}|Ω̂|` | `annulus_hull_defect` | `Annulus.lean` | proved |
| A3 | `|Ω|/|B^{2d}| ≥ (63/64)μ^{2d}N^d` | `annulus_vol_ge` | `Annulus.lean` | proved |
| B1 | Prop. 2.1 on the block, display (2), for `𝒱 = V_h^N` and degree `N + L` (needs `h ≠ 0` through P3); the sample set is a `Finset (Fin d → ℂ)` inside the block (`ofC z ∈ annulus`), `euclideanDist`-separated, and the sup-norm comparison is over `euclideanDist z 0 < μ√N` with the moduli `‖ev z F‖²` | `block_norming`; `DiscreteNorming.discrete_norming_explicit` (proved on `Pt d`; generalized to `z, z̄` in Step 1) | `BlockNorming.lean` | proved |
| B2 | `δ ≥ 4μ√d/10⁵` for large `N` (needs `h ≠ 0`: the `finrank` factor of `blockSep` is a lower bound only for a nonzero dimension) | `blockSep_ge` | `BlockNorming.lean` | proved |
| C | combined block estimate (p. 6), stated for `S : Finset (Fin d → ℂ)` and points of `ℂ^d` with `euclideanDist x 0 < μ√N` (no `toC`); given the norming set, so no `h ≠ 0` | `block_estimate` | `BlockEstimate.lean` | proved |
| X | `μ = 1/100 ⇒ μ²/2 + 9/2 + log μ ≤ −1/10` | `exponent_neg` | `BlockEstimate.lean` | proved |
| L1 | `F_N → F` pointwise | `tendsto_truncate` | `Coefficients.lean` | proved |
| L2 | block estimates on the balls `euclideanDist z 0 < μ√N_j`, `N_j → ∞`, force `|F| = |G|` on `ℂ^d` | `norm_eq_of_blocks` | `Limit.lean` | proved |
| S1 | consecutive blocks are `μ√N/4` apart in `euclideanDist`, for `z w : Fin d → ℂ` with `ofC z`, `ofC w` in the blocks | `annuli_far` | `Limit.lean` | proved |
| S2 | union of `euclideanDist`-separated subsets of `ℂ^d` sitting in the blocks is `euclideanDist`-separated | `union_separated` | `Limit.lean` | proved |
| CPR | `|F| = |G|` on `ℂ^d` ⇒ `F = λG`, `|λ| = 1` for `𝓕_h` (continuous phase retrieval for the STFT with the mixed Hermite window `w_h = ∑_q (-1)^{|q|} conj(h_q) φ_q / ‖h‖`) | `continuous_phase_retrieval`, by one call of `DiscretePolyFock.exactModulusRecovery` (`ContinuousPhaseRetrieval/ContinuousPR.lean`), stated directly for `DiscretePR.polyanalyticEval h`; that is `ModulusRecovery.exact_modulus_recovery_mixed` (`ContinuousPhaseRetrieval/ModulusRecovery/MixedLevel.lean`): the STFT model `stft_model_modulus_mixed`, the window's ambiguity function `windowAmbiguity_factorization_mixed` = polynomial `PH h` × Gaussian, nonzero at the origin (`PH_zero_ne`, via `ambiguityRep_self_zero` and `windowH_ne_zero`), hence dense nonvanishing, then the window-free core `spectrogram_eq_of_equal_modulus_to_ambiguity_eq_of_window`, `ambiguity_eq_to_coeffs_phase` of `ExactModulusRecovery.lean` | `ContinuousPR.lean` | proved |
| STFT | **Corollary** (the paper's Theorem `thm:STFT`): discrete phase retrieval for the STFT with the window `h(x) e^{−π|x|²}`, `h` a real polynomial, separation `√d/10⁷` in the Euclidean distance of `ℝ^d × ℝ^d` | `STFTDiscretePhaseRetrieval` (`STFT.lean`), from STFT-unit by the unitary dilation `t = s/√(2π)`: `dilate`, `stft_dilate`, `rescalePoly`, `dilate_gaussWindowUnit`, `norm_stft_gaussWindow`, `phaseDistUnit_scaled`, `sqrt_pi_le_four` (`Dilation.lean`); the phase-space map becomes the paper's `z = √π (x − iξ)` | `STFT.lean`, `Dilation.lean` | proved |
| STFT-finite | unit-scale phase retrieval for an arbitrary nonzero finite Hermite combination, extracted so other polynomial presentations can reuse the analytic core | `STFTDiscretePhaseRetrieval_unit_of_finite_window` | `STFT.lean` | proved |
| STFT-unit | the corollary in the unit scale of the Hermite functions: window `h(x) e^{−|x|²/2}`, sampling set `T⁻¹(S)` for the isometry `T(x,ξ) = (x − 2πiξ)/√2` of `phaseDistUnit` (`UnitScale.lean`), separation `4√d/10⁷` | `STFTDiscretePhaseRetrieval_unit` (`STFT.lean`), from M, `exact_modulus_recovery_mixed`, `stft_model_modulus_mixed`, the Hermite completeness `hermiteExpansion_hermiteCoeffs` (`ContinuousPhaseRetrieval/ModulusRecovery/HermiteBasis.lean`) and the window expansion `gaussWindow_eq_sum`, `windowH_signedConj`, `toFunH_mem_polyFockSpace`, `phaseDist_eq` (`WindowExpansion.lean`) | `STFT.lean` | proved |
| STFT-comparator | complex polynomial window `h(x)e^{−‖x‖²}` in the standalone comparator, with its inner-product STFT on `EuclideanSpace` and separation `√d/10⁷` | `ComparatorBridge.window_MemLp_proved`, `ComparatorBridge.stft_comparator_proved`; finite Hermite expansion of the complex polynomial window, identification with the integral STFT, and anisotropic phase-space dilation | `STFTComparatorBridge.lean` | proved |
| M | **Theorem 1.1** for `𝓕_h` | `DiscretePhaseRetrieval_proved` (= `Showcase.DiscretePhaseRetrieval`; the only use of `continuous_phase_retrieval`); the single-level case `𝓕^d_q` is the corollary `DiscretePhaseRetrieval_single` (`h = Finsupp.single q 1`) | `Main.lean` | proved |

## The Euclidean distance

Every statement of the proof uses the comparator's `DiscretePR.euclideanDist`
(the top-level `Definitions.lean`) for the geometry of `ℂ^d`; the radius of `z` is `euclideanDist z 0`.
Mathlib's `dist`, `Metric.ball` and `‖·‖` on `Pt d = EuclideanSpace ℝ (Fin (2d))` occur only in
the definition of `annulus`/`blockSep` (`Defs.lean`), in the measure computations of
`Annulus.lean`, in the transport lemmas of `Bridge.lean`, and inside proofs — never in another
theorem statement.  `mem_annulus_ofC` describes the sampling block in the comparator's
distance.

## Local choices (kept inside the proof of M only)

`N_* = max(16d, 3L, L+9, 1)` with `L = levelBound h`, `N_j = N_* · 100^j` (packaged as one
`obtain ⟨Nseq, …⟩` so the concrete choice is never unfolded), and the comparison of the
within-block and between-block separations. The threshold `16d ≤ N` of B2 replaces the paper's
"for sufficiently large `N`" (the case `d = 1` is the binding one).

## Deviations from the paper's text

* The kernel bound K is proved with polynomial factor `(1+|z|²)^{4L}` instead of
  `(1+|z|)^{L}`; the exponent `e^{|z|²/2}` is the paper's. Immaterial for the rate `−1/10`.
* The mixed-level estimates K and T are obtained from the single-level ones by Cauchy–Schwarz
  over `supp g` and by taking the exponents at `L = levelBound h`; the constants are the sums of
  the single-level constants over `supp g` (`tailConstH`, the `C` of `kernel_bound_mixed`).
* `dim V_h^N` is only bounded above by `C(N+d,d)`; that is all the separation bound uses.
* The paper's "for sufficiently large `N`" in B2 is made explicit (`N ≥ N₀`).
* CPR is imported from the old development through one bridge theorem (see above); Step 2 of the plan records any compile patches to the copied files.
* Proposition 2.1 is used in its generalization to polynomials in `z, z̄` (Step 1 of the plan).
