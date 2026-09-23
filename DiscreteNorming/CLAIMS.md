# Proposition 2.1 — claim map

Each substantial claim of the proof of Proposition 2.1 (paper p. 2–4, including Lemma 2.2),
with the Lean declaration that proves it (all in namespace `DiscreteNorming` unless noted).
Status 2026-09-02: **everything proved**; `lake build DiscreteNorming` is sorry-free, and
`discrete_norming_explicit`, `discrete_norming`, `discrete_norming_core`,
`vcDim_superlevel_family` depend only on `propext`, `Classical.choice`, `Quot.sound`.
About 2500 lines in 10 files.

| # | claim (paper) | Lean declaration | file |
|---|---|---|---|
| C1 | Remez inequality in exponential form: `‖p‖_V ≤ exp(4k (|V∖ω|/|V|)^{1/(2m)}) ‖p‖_ω` for `|V∖ω| ≤ 2^{−2m}|V|` | `remez_exp`; ingredients `T_eval_cosh`, `strictMonoOn_eval_T`, `T_eval_le_pow` (`T_k(y) ≤ (y+√(y²−1))^k`), `T_eval_le_exp` (`T_k((1+β)/(1−β)) ≤ e^{4k√β}`, `β ≤ 1/4`) | `Chebyshev.lean` |
| C2 | the superlevel set `{z ∈ Ω : |P(z)| ≥ e^{−8nθ^{1/(4d)}} ‖P‖_{L∞(Ω̂)}}` has measure `≥ t|Ω|` (`θ = (t|Ω| + |Ω̂∖Ω|)/|Ω̂| ≤ 2^{−4d}`) | `superlevel_measure_ge`; Chebyshev-form version for every `θ < 1`: `superlevel_measure_ge_T`; also `exists_max_on_hull`, `vol_hull_eq`, `isCompact_hull` | `Superlevel.lean` |
| C3 | `|F|² − |G|²` is a real polynomial of degree `≤ 2n` in `2d` real variables | `exists_realPoly` (via `psi`: substitution `z_j ↦ x_j + i x_{j+d}`, `z̄_j ↦ x_j − i x_{j+d}`; `cpart`: real/imaginary parts of coefficients) | `ComplexPoly.lean` |
| C3' | basis of `𝒱`; uniform approximation on bounded `Ω` by Gaussian-rational coefficient vectors | `exists_spanning` (needs `1 ≤ N`), `comb_mem`, `totalDegree_comb_le`, `exists_rat_approx`, `continuous_diff` | `ComplexPoly.lean` |
| C4a | VC dimension is non-increasing under pull-back | `VCDimLE_preimage` | `VCBound.lean` |
| C4b | shattering `K` points by `𝒢_N` ⇒ all `2^K` strict sign patterns of the quartic polynomials `p_ℓ = (|Σa y^ℓ|² − |Σb y^ℓ|²)² − 1` occur (scaling by `λ > 1`) | `univFamily` (the family `𝒢_N`), `exists_signPoly` (the `p_ℓ`, degree `≤ 4`), `shatter_signPatterns` | `SignPoly.lean` |
| C4c | Warren ⇒ `K ≤ 36N` (with Lean's Warren bound, `2^K ≤ (4e(K+1)/N)^{4N}`) | `card_le_of_signPatterns`; `SignPatterns.sign_patterns_warren` (`Warren/SignPatterns/SignPatternBound.lean`) | `VCBound.lean` |
| C4 | **Lemma 2.2**: `vc {{z ∈ Ω : ||F(z)|²−|G(z)|²| ≥ τ}} ≤ 36N` | `vcDim_superlevel_family` (via `vcDim_univFamily`) | `VCBound.lean` |
| C5 | relative VC inequality with Sauer–Shelah, constant 8 | `VCInequality.relative_deviation_vc` (`VCInequality/RelativeVCInequality.lean`) | — |
| C6 | `8(2eM/V)^V e^{−Mε²/4} ≤ 1/100` for `ε = √t/2`, `V = 36N`, `M = ⌊(3000+1200|log t|)N/t⌋`, **`0 < t ≤ 1/8`** | `sample_size_bound`; `sampleSize_pos` (`36N ≤ 2M`), `sampleSize_le` | `Sampling.lean` |
| C7 | off the bad event each family set of measure `≥ t` receives `≥ (t/2)M` sample points | `count_ge_of_not_bad` | `Sampling.lean` |
| C7' | the countable subfamily (Gaussian-rational coefficients w.r.t. a spanning family, rational threshold): countable, measurable, contained in the family of Lemma 2.2; uniform measure `volume[|Ω]` | `ratFamily`, `RatIndex`, `instCountableRatIndex`, `measurableSet_ratFamily`, `ratFamily_mem_superlevelFamily`, `unif`, `isProbabilityMeasure_unif`, `unif_real_apply`, `unif_compl` | `Defs.lean`, `Sampling.lean` |
| C8 | two independent uniform points are `r`-close with probability `≤ r^{2d}|B^{2d}|/|Ω|`; expected number of close pairs `≤ (M(M−1)/2) r^{2d}|B^{2d}|/|Ω|` | `prob_close_le`, `expected_closePairs_le` | `Separation.lean` |
| C9 | with `δ = (tN|Ω|/(2M|B^{2d}|))^{1/(2d)}` the expectation is `≤ (t/4)M`; Markov: `> (t/3)M` close pairs with probability `≤ 3/4` | `expected_closePairs_le_sepRadius`, `closePairs_markov` | `Separation.lean` |
| C10 | a sample exists that lies in `Ω`, avoids the bad event (probability `≤ 1/100`) and has `≤ (t/3)M` close pairs | `exists_good_sample` | `Separation.lean` |
| C11 | deleting one point of each close pair leaves a `δN^{−1/(2d)}`-separated nonempty set meeting every set with `≥ (t/2)M > (t/3)M` sample points | `exists_separated_subsample` | `Separation.lean` |
| C12 | hitting every rational-family set of measure `≥ t|Ω|` ⇒ `‖P‖_{L∞(S)} ≥ c‖P‖_{L∞(Ω̂)}` for all `F, G ∈ 𝒱` (approximation + limit, no constant lost) | `norming_of_hits` | `Density.lean` |
| C13 | the proof, parametric in `0 < t ≤ 1/8`, Remez constant `T_{2n}((1+β)/(1−β))`, separation `sepRadius = (t|Ω|/(2M|B^{2d}|))^{1/(2d)}` | `discrete_norming_core` | `Main.lean` |
| C14 | **Proposition 2.1, explicit constants**: `t = 2^{−4d−1}`, `|Ω̂∖Ω| ≤ 2^{−4d−2}|Ω̂|` ⇒ `C_norm = 4`, `δ = (1/16)(|Ω|/|B^{2d}|/(3·10⁵(1+d)))^{1/(2d)}` | `discrete_norming_explicit`; `deltaPaper_le_sepRadius`, `sepRadius_ge` | `Main.lean` |
| C15 | **Proposition 2.1, general constants** (`C_norm = 2 arcosh((1+β)/(1−β))`, `t = 1/8`) | `discrete_norming` | `Main.lean` |

## Reading the statements

`Pt d = EuclideanSpace ℝ (Fin (2d))` is `ℂ^d`; `toC x` are the complex coordinates;
`𝒱 : Submodule ℂ (PolyFock.Fock.P d)`, `PolyFock.Fock.P d = MvPolynomial (Fin d ⊕ Fin d) ℂ`
is `ℂ[z, z̄]`, evaluated at `z` by `PolyFock.Fock.ev z`;
`diff F G x = |F(z)|² − |G(z)|²`; `hull Ω` is the closed convex hull (`= Ω̂` up to a null set);
`vol` is Lebesgue measure as a real number; `unitBallVol d = |B^{2d}|`; `deltaPaper d Ω` is the
paper's `δ`. `‖·‖_{L∞(S)}` appears as `∃ y ∈ S, |P x| ≤ C |P y|`.

## Deviations from the paper's text (to be amended in the paper)

* Proposition 2.1 is stated for `𝒱 ⊆ ℂ[z, z̄]` (`PolyFock.Fock.P d`, evaluated by
  `PolyFock.Fock.ev`), as the paper's `Poly_n(ℂ^d)` requires in §4; the holomorphic case is the
  image of `rename Sum.inl`.
* The sample-size choice `M = ⌊(3000 + 1200|log t|)N/t⌋` needs the hypothesis `t ≤ 1/8`
  (the displayed bound fails for `t ≥ 1/4`); the paper uses `t = 2^{−4d−1}`, which satisfies it.
* p. 4: `½M` and `⅓M` should read `(t/2)M` and `(t/3)M`.
* The general (non-explicit) claim holds for every bounded measurable `Ω` of positive measure,
  by the Chebyshev form of Remez; the exponential form used in the paper needs
  `|Ω̂ ∖ Ω| < 2^{−4d}|Ω̂|`. The paper says "bounded domain"; the Lean statement asks for
  measurable, bounded, positive measure.
* Lemma 2.2 is formalised exactly as written (two-sided family, bound `36N`); Lean's Warren
  bound has `(K+1)` in place of `K`, which is absorbed.
