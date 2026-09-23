# Duplicate definitions (wide sense) — inventory for a future clean-up

Compiled 2026-09-06 from a mechanical inventory (300 `def`/`abbrev`/`instance`/`structure`
declarations; the only literally identical bodies are the deliberate triples in `Definitions.lean`,
`Showcase.lean`, `ContinuousPhaseRetrieval/Defs.lean`) and three read-throughs of the sources.
"Duplicate" means: could be unified so that the code references one definition, without adding
many lines. Nothing has been changed. Confidence: **C** certain, **L** likely, **S** speculative.
Line numbers refer to the state of 2026-09-06.

Constraints to respect when cleaning up: `Definitions.lean` is the public statement (checked by
`Check.lean` against the comparator `Showcase.lean`) and must not change; `Showcase.lean` is a
deliberate verbatim copy and stays; the earlier development `ContinuousPhaseRetrieval/` is certified
verbatim by its `PROVENANCE.md` (`diff -r -I '^import '`), so any edit there beyond import lines
must update that recipe.

## 1. Dead declarations (pure deletion, no statement changes)

| declaration | location | note |
|---|---|---|
| `PolyFock.kernel` | `PolyFock/Basic.lean:63` | never referenced; trim docstrings `Basic.lean:21–25`, `PolyFock/TailBound.lean:13,19` — **C** |
| `PolyFock.tailKernel`, `tailKernel_diag` | `PolyFock/Basic.lean:73`, `PolyFock/Rotation.lean:88` | only `tailKernelDiag` is used — **C** |
| `PolyFock.tailKernelDiag_nonneg` | `PolyFock/Basic.lean:87` | **C** |
| `PolyFock.euclideanDist_radialPoint` | `PolyFock/Rotation.lean:75` | **C** |
| `PolyFock.norm_phi_zero_self` | `PolyFock/PhiBound.lean:63` | **C** |
| `PolyFock.Fock.mapDomain_swap_single` | `PolyFock/Fock/Creation.lean:39` | **C** |
| `PolyFock.Fock.Psihat_mem_W` | `PolyFock/Fock/Kernel.lean:60` | distinct from the used `R_Psihat_mem_W`; re-verify before deleting — **L** |
| `DiscretePR.euclideanDist_toC` | `DiscretePhaseRetrieval/Bridge.lean:117` (+ mention at `:11`) | is `norm_ofC` transported along `ofC_toC` — **C** |
| `DiscretePR.polyanalyticEval_eq_old` | `DiscretePhaseRetrieval/ContinuousPR.lean:12` | a `rfl` nobody names; the identification is used implicitly — **C** |
| `count_eq_card_filter` | `VCInequality/Binomial/Law.lean:25` | `rfl` restating the definition — **C** |
| `HermiteLEAN.phi`, `HermiteLEAN.phi0`, `HermiteLEAN.rho`, `Hermite1DimdLEAN.rho` | `ContinuousPhaseRetrieval/ModulusRecovery/Hermite/Definitions.lean:55,47,44`, `…/Hermite1Dimd/Definitions.lean:44` | zero references; `phi = HermitekLEAN.Phi 1`, `phi0 = Phi 1 0` up to a `k = 1` expansion — **C** (dead) |
| `Hermite1DimdLEAN.Circle`; `ModulusRecovery.Circle` + `zeta` | `…/Hermite1Dimd/Definitions.lean:25`; `…/ModulusRecovery/ImportedAnalyticInputs.lean:17,25` | four `Circle` abbrevs are all `AddCircle (2π)`; these two are unreferenced; every `Circle.foo` in proofs is Mathlib's `_root_.Circle` — **L** |
| duplicate `Fact (0 < T)` instance and `T_pos` | `…/Hermite1Dimd/Definitions.lean:21–23` | already provided by `Hermite/Definitions.lean:37`; third copy for `2π` at `ModulusRecovery/Definitions.lean:24` — **L** |
| `DiscretePolyFock.gaussianDensityParam/γParam/polyanalyticEvalParam/PolyFockSpaceParam`, `memBox/boxTruncFun/boxTrunc` (+4 lemmas), `UniformlyDiscrete`, `PolyFockSpace`, `PhaseRetrievalSet`, `γ`, `gaussianDensity` | `ContinuousPhaseRetrieval/Defs.lean:43–132` | zero references in the repo; see §4 for the whole file — **C** |

## 2. Same theorem or object defined twice within the new development

| # | items | relation / unification | cost | conf. |
|---|---|---|---|---|
| 2.1 | `VCInequality.sum_choose_le_pow` (`VCInequality/Sauer.lean:20`) vs `SignPatterns.sum_choose_le_exp_pow` (`Warren/SignPatterns/SignPatternBound.lean:137`) | same theorem `∑_{k≤V} C(n,k) ≤ (e n/V)^V`, same proof, ~55 lines each (`Iic V` vs `range (V+1)`); packages are independent, so the lemma needs a small shared file imported by both | −55 lines, new file, 2 call sites | C |
| 2.2 | `BoundedComponents.differentiable_eval` (`Warren/BoundedComponents/Perturbation.lean:194`) vs `AlgebraicTransversality.differentiable_evalPoly` (`Warren/Transversality.lean:287`) | identical statement and proof; Perturbation already imports Transversality | −4 lines, 3 uses in `BoundedComponents/Main.lean:46,76,102` | C |
| 2.3 | `binTail` (`VCInequality/Defs.lean:78`) vs private `binPmf` (`VCInequality/Binomial/DeMoivre.lean:34`); `binTail_eq_one` (`Binomial/Domination.lean:29`) vs `sum_binPmf_eq_one` (`DeMoivre.lean:116`) | `binPmf` is the summand of `binTail` (`rfl`); the two "total mass = 1" lemmas are the same fact, each ~11 lines | move `binPmf` to `Defs.lean`, restate `binTail` through it (defeq), keep one lemma; −15 lines, 3 files | C |
| 2.4 | `ofList_take_ofFn` (`Warren/WeakBezout/Regularity.lean:72`) vs private copy (`Warren/WeakBezout/Count.lean:284`, RHS `partialSpan L j`, definitionally the same) | same statement, 15 lines each | import Regularity (or move to `GradedDim.lean`); −14 lines | C |
| 2.5 | `SignPatterns.sqNorm` (`Warren/SignPatterns/Perturb.lean:37`) vs `BoundedComponents.sumSq` (`Warren/BoundedComponents/Perturbation.lean:37`) | `sqNorm n = sumSq X` by `rfl`; `eval_sqNorm`, `totalDegree_sqNorm_le` follow from the `sumSq` lemmas | −5 lines, 1 file, one acyclic import | L |
| 2.6 | `zeroSet`/`boundedComponents` (`Warren/BoundedComponents/Main.lean:33,37`) vs `zeroSetOn`/`boundedComponentsOn` (`Warren/SignPatterns/Counting.lean:30,56`) | the former are the `J = univ` instances; bridge half exists (`Counting.lean:39,50`). Also `bounded_components` (`BC/Main.lean:202`) re-spells the body of `boundedComponents` inline and then `change`s to it | ~15 proof lines touched, 2 files; the inline respelling alone −10 lines | L / C |
| 2.7 | `unitBallVol_pos` (`DiscreteNorming/Separation.lean:175`) and again (`DiscretePhaseRetrieval/Annulus.lean:38`) | same fact, two proofs; Annulus already imports the DiscreteNorming side | −4 lines | C |
| 2.8 | `mem_box'` (`DiscretePhaseRetrieval/Coefficients.lean:23`, private, self-declared copy) vs `mem_box` (`Polynomials.lean:19`) | identical 8-line proof; importing `Polynomials` into `Coefficients` is acyclic (or move `mem_box` next to `box` in `Defs.lean`) | −8 lines, 10 renames | C |
| 2.9 | `have key` block in `eval_truncate` (`Coefficients.lean:120–131`) and `tendsto_truncate` (`Coefficients.lean:198–210`) | same 12-line derivation of `polyanalyticEval κ (truncate N F) z = ∑_{α ∈ box} coeff F α * Φ α κ z` | extract one lemma; −13 lines | C |
| 2.10 | `DiscretePR.deg` (`DiscretePhaseRetrieval/Defs.lean:32`) vs inline `∑ i, n i` in `PolyFock/Basic.lean:65,75,85`, `Fock/Kernel.lean:52`, `Fock/Layer.lean:112,145`, `PolyFock/TailBound.lean:166,225`, `RadialReduction.lean:32,40` vs `Fock.dg` (`Fock/Rot.lean:156`, on `Finsupp`, = Mathlib `Finsupp.degree`) | three spellings of total degree; seam visible at `DiscretePhaseRetrieval/TailBound.lean:72` | move `deg` to `PolyFock/Basic.lean`, ~25 sites, 6 files; statements of `tail_bound` etc. change cosmetically; `dg` → `Finsupp.degree` ~8 lines | C (same notion) |
| 2.11 | the φ-estimate written three times: `PolyFock.sq_norm_phi_le` (`PhiBound.lean:82–200`), `sq_norm_phi_le_gen` (`DiscretePhaseRetrieval/KernelBound.lean:106–192`), `sq_norm_phi_le_mid` (`KernelBound.lean:261–348`) | same five steps after the shared `norm_phi_le_sum`; ~120 of ~250 lines coincide (e.g. `PhiBound.lean:186–200` = `KernelBound.lean:179–192`) | one parametrised core lemma (+45, −120 lines), 2 files; hypotheses differ, needs care | L |
| 2.12 | `pow_div_factorial_le` (`PolyFock/Estimates.lean:22`) vs `pow_div_factorial_le'` (`KernelBound.lean:195`) | same purpose (cancel `m^{2L}` against `m!`), incomparable conclusions | not free | S |
| 2.13 | `Phi` (`PolyFock/Basic.lean:54`) vs `Psihat` evaluated (`PolyFock/Fock/Bridge.lean:75,77`); `phi`'s `√(m!n!)` vs `nrm` (`Fock/Bridge.lean:24`) | explicit-function vs algebraic model of the same basis, tied by `ev_Psihat`; both models are used for different purposes | roughly line-neutral; recommend keeping | S |
| 2.14 | `HermitePoly`/`Φ` (`Definitions.lean:54,65`) vs `PolyFock.phi`/`Phi` (`PolyFock/Basic.lean:47,54`) | identical up to `star z` vs `starRingEnd ℂ z`; bridged by `hermitePoly_eq_phi`/`Phi_eq_Phi` (`Bridge.lean:26,32`), invoked at 4 sites (`Coefficients.lean:134`, `KernelBound.lean:498`, `TailBound.lean:34,72`) | delete the `PolyFock` pair, use the comparator's everywhere in `PolyFock` (~70 occurrences, 9 files; `PolyFock/Rotation.lean` already imports `Definitions`); direction must be `PolyFock → Definitions` | C (same object) / L (worth it) |

## 3. Repeated constructions and helper steps

| # | items | note | conf. |
|---|---|---|---|
| 3.1 | complex-coordinate readers: `DiscreteNorming.toC` (`DiscreteNorming/Defs.lean:24`), `coords`/`mkCoords` (`DiscreteNorming/SignPoly.lean:26,67`), `DiscretePR.ofC` (`DiscretePhaseRetrieval/Defs.lean:39`) with `toC_ofC`/`ofC_toC`/`coords_mkCoords` | one `Equiv (Fin (2n) → ℝ) ≃ (Fin n → ℂ)` would replace all (~35 lines saved) but `exists_signPoly` reads the four offsets directly (`SignPoly.lean:118–121`); Mathlib has no ready `(Fin d → ℂ) ≃ₗᵢ EuclideanSpace ℝ (Fin (2d))` | S (highest saving, highest churn) |
| 3.2 | "square-root a squared inequality": `Coefficients.lean:114–115`, `TailBound.lean:102–108,177–184`, `Limit.lean:77–79` | one helper `‖x‖² ≤ c²B → ‖x‖ ≤ c√B`; −12 lines, 3 files | L |
| 3.3 | numeric `exp` bounds by `exp_one_lt_d9` → `pow_le_pow_left₀` → `norm_num`: `BlockNorming.lean:45–52,78–84`, `TailBound.lean:133`, `PolyFock/TailBound.lean:84,293` | one lemma each direction; +8, −25 lines | L |
| 3.4 | `euclideanDist` API split: `PolyFock/Rotation.lean:36–55` re-opens `namespace DiscretePR` for `euclideanDist_zero/_nonneg/_sq`; `Bridge.lean:94–127` has the rest | move the three lemmas to `Bridge.lean` (13 lines) | C (split, not duplicate) |
| 3.5 | `DiscreteNorming/Chebyshev.lean` is Remez material: `strictMonoOn_eval_T` (`:33`) next to `Remez/Interpolation.lean:71 monotoneOn_eval_T`, proved by unrelated routes | move the file under `Remez/`, derive one monotonicity lemma from the other (−12 lines) | L |
| 3.6 | `VCDimLE_mono` (`DiscreteNorming/Main.lean:39`), `VCDimLE_preimage` (`DiscreteNorming/VCBound.lean:29`) are generic VC facts stranded in DiscreteNorming | move to `VCInequality` | C (misplacement) |
| 3.7 | `beta_nonneg`/`beta_lt_one` in `DiscreteNorming/Main.lean:81,86` and `Remez/Multivariate/BrudnyiGanzburgRemez.lean:55,62` | same names, different statements that coincide by `Superlevel.lean:239–244`; saving ~0, names misleading | S |
| 3.8 | stale docstrings: `PolyFock/Rotation.lean:20–33`, `PolyFock/TailBound.lean:19` describe an unproved input `PolyFock.RotationInvariant` that does not exist (the rotation input is proved: `Fock.layer_diag_rot` → `tailKernelDiag_le_of_radial_bound`) | fix the text | C |

## 4. The earlier development `ContinuousPhaseRetrieval/`

| # | items | relation | unification / cost | conf. |
|---|---|---|---|---|
| 4.1 | `DiscretePolyFock.HermitePoly`, `Φ`, `gaussianDensity`, `γ`, `PolyFock`, `coeff`, `polyanalyticEval`, `PolyFockSpace`, `PhaseRetrievalSet` (`ContinuousPhaseRetrieval/Defs.lean:29–72`) vs the same names in `Definitions.lean` | `HermitePoly`/`Φ` identical up to the argument swap (`DiscretePolyFock.HermitePoly k n = DiscretePR.HermitePoly n k`, `Φ κ α = Φ α κ`); the rest literally identical; `polyanalyticEval` defeq (used by the `rfl` at `DiscretePhaseRetrieval/ContinuousPR.lean:14`); `UniformlyDiscrete` (`:68`) genuinely different (existential ε, arbitrary metric) and dead | `Defs.lean` is imported only by `ContinuousPhaseRetrieval/ContinuousPR.lean` (70 lines), so the whole file can go: let that file `import Definitions`, state `exactModulusRecovery` about `DiscretePR.polyanalyticEval`; the bridge's `polyanalyticEval_eq_old` disappears too. −134 lines, ~5 edited; must update `PROVENANCE.md` | C (relation) / L (compiles: the two private `rfl`s in `ContinuousPR.lean` should still elaborate) |
| 4.2 | `ModulusRecovery.phi1D`/`complexHermite` (`…/ModulusRecovery/Definitions.lean:40,34`), `ModulusRecovery.Phi` (`:44`) vs `PolyFock.phi`/`Phi` and `DiscretePR.HermitePoly`/`Φ` | same function a fourth time (`phi1D k n = HermitePoly n k` syntactically; `Phi κ α = PolyFock.Phi α κ`) | unifying would make the root of the 16k-line closure import the new development and break `unfold phi1D complexHermite` sites (`TensorBasis.lean:90,409`); leave, add a cross-reference comment | C (not cheap) |
| 4.3 | `HermitekLEAN.Phi` (`…/Hermitek/TrueLevelBasis.lean:54`) vs `Hermite1DimdLEAN.oneDimPhi` (`…/Hermite1Dimd/Definitions.lean:33`) | byte-identical bodies (also noted in `PROVENANCE.md`) | add `import …Hermitek.TrueLevelBasis` to `Hermite1Dimd/Definitions.lean` (acyclic), `abbrev oneDimPhi := HermitekLEAN.Phi`; watch `simpa`/`unfold` sites `TensorBasis.lean:90,236,809`, `ProductBasisAndAnnuli.lean:216,225` | L |
| 4.4 | `ModulusRecovery.gaussianDensity`/`gamma_d`/`Cd`/`MultiIndex`/`Idx` (`…/ModulusRecovery/Definitions.lean:26,29,11,12,13`) vs `Hermite1DimdLEAN.gaussianDensity`/`gaussianMeasure`/`CSpace`/`MultiIndex` (`…/Hermite1Dimd/Definitions.lean:27,30,17,18`) | literally identical; the defeq is paid by hand (`change` at `TensorBasis.lean:537`; 3 of the 62 recorded toolchain patches were caused by this pair) | one import + 5 `abbrev` aliases, −8 lines | L |
| 4.5 | `HermiteLEAN.weightedInner/weightedNormSq/weightedNorm` vs `HermitekLEAN.*` | already aliases (false positive of the name scan); the pattern to copy | — | C |
| 4.6 | `ModulusRecovery.Skappa` (`…/ModulusRecovery/Definitions.lean:20–23`, bespoke ℓ² structure with hand-written instances) vs `lp (fun _ => ℂ) 2`; `ContinuousPhaseRetrieval/ContinuousPR.lean:23–35` exists only to convert between them | restatement of `Memℓp _ 2`; unifying rewrites the interface of the whole closure | not cheap | C |
| 4.7 | hand-rolled Gaussian inner products `HermiteLEAN.weightedInner…` (`Hermite/Definitions.lean:64–73`), `Hermite1DimdLEAN.gaussianInner/gaussianL2NormSq` (`Hermite1Dimd/Definitions.lean:46–51`) vs Mathlib `L2` inner product used elsewhere in the same library | ~20 use sites on non-`Lp` functions; switching means threading `MemLp` witnesses | do not touch | C |
| 4.8 | `ModulusRecovery.Idx`/`T`/`box`/`truncate` vs same-named `PolyFock.Fock.Idx`/`Fock.T`/`DiscretePR.box`/`truncate` | name collisions only (different objects) | nothing to merge | C |

## 5. Restatements of Mathlib

| # | project definition | Mathlib | cost | conf. |
|---|---|---|---|---|
| 5.1 | `DiscreteNorming.toPi` (`DiscreteNorming/Defs.lean:29`) | `WithLp.ofLp` — the project itself proves `toPi_eq_ofLp : toPi = WithLp.ofLp := rfl` (`Superlevel.lean:64`) | replace 20 occurrences in 3 files, drop `toPi_eq_ofLp`, `continuous_toPi`; −10 lines | C |
| 5.2 | `DiscreteNorming.vol Ω = (volume Ω).toReal` (`Defs.lean:52`) | `Measure.real` (`measureReal_*` API, already used 56× in the project; `unif_real_apply` mixes both) | `abbrev vol := volume.real`; 6 unfolding sites need `measureReal_def`; `vol_hull_eq` (`Superlevel.lean:43`) becomes a Mathlib lemma | C |
| 5.3 | `DiscreteNorming.hull Ω = closure (convexHull ℝ Ω)` (`Defs.lean:49`) | `closedConvexHull ℝ` (a `ClosureOperator`; needs a small bridging equality) gives `convex_hull'`, `subset_hull`, `measurableSet_hull` (`Superlevel.lean:33,36,39`) | ~5 lines net, mainly API reuse | L |
| 5.4 | `DiscreteNorming.unif Ω = ProbabilityTheory.cond volume Ω` (`Defs.lean:58`) | pure alias; its three lemmas unfold it immediately | optional | C |
| 5.5 | `DiscreteNorming.unitBallVol` (`Defs.lean:55`) | `EuclideanSpace.volume_ball` gives the closed form; the abbreviation itself is fine (see 2.7 for the duplicate lemma) | — | C |
| 5.6 | `DiscreteNorming.T_eval_one'` (`DiscreteNorming/Main.lean:92`) | `Polynomial.Chebyshev.T_eval_one` (integer index) | −4 lines, one cast | C |
| 5.7 | `PolynomialSard.toCPt x = fun j => ((x j : ℝ) : ℂ)`, `toCPt_injective` (`Warren/PolynomialSard.lean:54`) | `Complex.ofReal ∘ x`, `Complex.ofReal_injective.comp_left`; `toC` (`:36`) = `MvPolynomial.map (algebraMap ℝ ℂ)` is worth keeping for its lemmas | −6 lines, 1 file | L |
| 5.8 | `Fock.dg` (`PolyFock/Fock/Rot.lean:156`) with `dg_add_single`, `dg_sub_le` | `Finsupp.degree` | ~8 lines, 1 file | L |
| 5.9 | `euclideanDist_zero` (`PolyFock/Rotation.lean:43`), `euclideanDist_eq_dist` (`Bridge.lean:94–102`) | `EuclideanSpace.norm_eq`, `EuclideanSpace.dist_eq` — but `euclideanDist` on `Fin d → ℂ` is a user decision, and Mathlib has no `(Fin d → ℂ) ≃ₗᵢ EuclideanSpace ℝ (Fin (2d))`, so the two coordinate models `Pt d` (`toC`/`ofC`) and `Fin d → ℂ` (plus an ad-hoc `EuclideanSpace ℂ (Fin d)` at `PolyFock/Rotation.lean:118`) stay | — | S |
| 5.10 | `tsum_mul_sq_le` (`Coefficients.lean:32`, private Cauchy–Schwarz for `tsum`) | `inner_mul_le_norm_mul_norm` on `lp G 2`; needs `Memℓp` packaging and is used with truncated families | a wash | S |
| 5.11 | `VCInequality.VCDimLE` vs `Finset.vcDim` | different carriers (`Set (Set X)` vs `Finset (Finset α)`); `Sauer.lean` already bridges | not a duplicate | C |
| 5.12 | `γ`/`gaussianDensity` (`Definitions.lean:71,75`) vs `ProbabilityTheory.gaussianReal` | real 1-D only in Mathlib; comparator-facing | do not touch | C |

## 6. Not duplicates, despite the names

`BoundedComponents.pert` vs `AlgebraicTransversality.pert`; `DiscreteNorming.toC` vs
`PolynomialSard.toC`; `truncate` vs `truncPoly` (both needed by `block_estimate`); `DiscretePR.coeff`
(comparator-facing eta-wrapper, do not touch); `ModulusRecovery.Idx` vs `PolyFock.Fock.Idx`;
`HermiteLEAN.T` vs `PolyFock.Fock.T`; `ModulusRecovery.box` vs `DiscretePR.box`;
`HermitekLEAN.truncate` vs `DiscretePR.truncate`; `instFiniteDimensionalVqN` (used by instance search).

## Suggested order

1. §1 deletions and the docstring fix 3.8 (~150 lines, no risk).
2. 2.2, 2.7, 2.8, 2.9, 5.6, 5.1, 3.4 (small, local, certain).
3. 2.3, 2.4, 2.5, 4.3, 4.4, 5.2, 5.7, 5.8 (one import or one alias each).
4. 2.1 (shared binomial lemma file), 2.10 (one `deg`), 3.2, 3.3, 3.5.
5. 4.1 (drop `ContinuousPhaseRetrieval/Defs.lean`; update `PROVENANCE.md`).
6. 2.11 (merge the three φ-estimates), 2.14 (one basis; ~70 sites, do last).
7. 3.1 only if the `Fin` index arithmetic is being reworked anyway.

Files not read in full by the reviewers: `Remez/Remez.lean`, `Remez/Multivariate/Rearrangement.lean`,
`VCInequality/{Symmetrization,Swap,Rademacher,RelativeVCInequality,Binomial/Stirling,Binomial/Main}.lean`,
`Warren/WeakBezout/{DepthFragment,Interpolation,NullstellensatzStep,Main}.lean`,
`Warren/BoundedComponents/{Separation,CriticalPoint}.lean`, `Warren/SignPatterns/Orthant.lean`,
`DiscreteNorming/Density.lean`, the body of `ContinuousPhaseRetrieval/ModulusRecovery/ExactModulusRecovery.lean`
(8.9k lines; only its imports and grep hits). Duplicates confined to those files would have
surfaced only through the name scan.

## Done 2026-09-06 (clean-up pass over `Warren/`, `VCInequality/`, `DiscreteNorming/`)

Full `lake build` and `lake build Check` are green; `Check.lean` still reports
`[propext, Classical.choice, Quot.sound]` for `DiscretePR.PolyDiscreteSPR_proved` and
`DiscretePR.continuous_phase_retrieval`, and `SignPatterns.sign_patterns` and the
`PolyFock/Check.lean` audit are unchanged.  `DiscreteNorming/CLAIMS.md` needed no edit
(no claim's Lean name changed).

* **2.2** — deleted `BoundedComponents.differentiable_eval` (`BoundedComponents/Perturbation.lean`);
  the three uses in `BoundedComponents/Main.lean` now call
  `AlgebraicTransversality.differentiable_evalPoly`.  Net −2 lines.
* **2.3** — `binPmf`/`binPmf_nonneg` moved (public) into `VCInequality/Defs.lean`; `binTail` is now
  `∑ j ∈ Icc k m, binPmf m p j` (definitionally unchanged).  `DeMoivre.lean` imports
  `Binomial.Domination` and derives its private `sum_binPmf_eq_one` from `binTail_zero` in one line;
  `binTail_eq_one` is the surviving proof.  Sites that unfolded `binTail` now say
  `unfold binTail binPmf`.  Net −5 lines.
* **2.4** — the private 15-line copy of `ofList_take_ofFn` in `WeakBezout/Count.lean` is replaced by a
  3-line `ofList_take_partialSpan` delegating to `WeakBezout/Regularity.lean` (`Count` now imports
  `Regularity`; acyclic).  Net −11 lines.
* **2.5** — `SignPatterns.sqNorm` is now `BoundedComponents.sumSq X` and `totalDegree_sqNorm_le`
  comes from `totalDegree_sumSq_le`; `SignPatterns/Perturb.lean` imports
  `Warren.BoundedComponents.Perturbation` (acyclic — `SignPatterns/Counting.lean` already depended on
  `BoundedComponents`).  Net **+3** lines: the duplicate definition is gone but the item does not
  save lines.
* **2.6 (second half only)** — `BoundedComponents.bounded_components` is now stated with
  `boundedComponents p` instead of the inlined set-builder, and the `change` is gone; its single
  consumer `SignPatterns/Counting.lean` rewrites `boundedComponentsOn q J` to
  `BoundedComponents.boundedComponents (subfamily q J)` directly (no `mem_boundedComponents` needed).
  Net −10 lines.  The `zeroSet → zeroSetOn univ` unification was **not** done.
  Note: `plans/PLAN-BoundedComponents.md` still quotes the old spelling of the statement.
* **§1** — deleted `count_eq_card_filter` (`VCInequality/Binomial/Law.lean`); `count_le` closes by
  `exact`, one use by `rfl`, one by an inline `show … from rfl`.  Net −7 lines.
* **2.7** — nothing to do on the `DiscreteNorming` side; `Separation.lean:175 unitBallVol_pos` kept.
* **5.1** — `DiscreteNorming.toPi`, `toPi_eq_ofLp`, `continuous_toPi` deleted; all uses now spell
  `WithLp.ofLp` (continuity from `PiLp.continuous_ofLp`).  The four transport lemmas were renamed
  `convex_/isCompact_/volume_/vol_ofLp_image`.  `exists_realPoly` and `eval_psi` now state
  `WithLp.ofLp x` where they said `toPi x`; `superlevel_measure_ge*` are untouched.  Net ≈ −6 lines.
* **5.2** — `vol` is now `noncomputable abbrev vol Ω := volume.real Ω`.  `vol_hull_eq` is four lines
  via `measureReal_inter_add_diff`.  Unfolding sites got `measureReal_def`
  (`Superlevel.lean` ×2, `Separation.lean`, `Sampling.lean`, and — outside these folders —
  `DiscretePhaseRetrieval/Annulus.lean` ×2, the only downstream repair needed).  Net −4 lines.
* **5.6** — `T_eval_one'` deleted; the single use is `Polynomial.Chebyshev.T_eval_one ℝ _`
  (the ring argument is explicit there).  Net −4 lines.
* **5.7** — `PolynomialSard.toCPt` is now `Complex.ofReal ∘ x` and `toCPt_injective` is
  `Complex.ofReal_injective.comp_left`; the name `toCPt` was kept for readability at its image sites,
  `toC` untouched.  Net −5 lines.

Nothing was skipped.  Total ≈ −45 lines.

## Done 2026-09-06 (batch 2, `PolyFock/`)

Full `lake build`, `lake build Check` and `lake build PolyFock.Check` are green; both audits still
report `[propext, Classical.choice, Quot.sound]` only (`Check.lean`:
`DiscretePR.PolyDiscreteSPR_proved`, `DiscretePR.continuous_phase_retrieval`; `PolyFock/Check.lean`:
`tail_bound`, `tail_bound_sqrt`, `tailKernelDiag_radialPoint_le`,
`tailKernelDiag_le_of_radial_bound`, `Fock.layer_kernel_rot`, `Fock.form_Psihat`, `Fock.T_R`).
No statement used outside `PolyFock/` changed.

* **§1** — deleted `PolyFock.kernel`, `PolyFock.tailKernel` and `tailKernelDiag_nonneg`
  (`PolyFock/Basic.lean`), `tailKernel_diag` and `euclideanDist_radialPoint`
  (`PolyFock/Rotation.lean`), `norm_phi_zero_self` (`PolyFock/PhiBound.lean`),
  `Fock.mapDomain_swap_single` (`PolyFock/Fock/Creation.lean`) and `Fock.Psihat_mem_W`
  (`PolyFock/Fock/Kernel.lean`, confirmed unused — only `R_Psihat_mem_W` is).  The module
  docstrings of `Basic.lean` and `TailBound.lean` now describe `tailKernelDiag` alone (the tail
  kernel `K_{L,N}` is still named there, as prose, since that is what the diagonal is the diagonal
  of).  Net −67 lines.  Nothing else became dead: `Fock.Psi_mem_W'` (`Fock/Layer.lean`), the only
  lemma `Psihat_mem_W` used, still has four uses inside `Fock/Layer.lean`.
* **3.8** — the `PolyFock/Rotation.lean` header no longer announces an unproved
  `PolyFock.RotationInvariant`: it lists what the file actually provides (`radialPoint`,
  `exists_unitary_radialPoint`) and points at the proved analytic half (`Fock.layer_diag_rot`,
  combined in `tailKernelDiag_le_of_radial_bound`).  The `PolyFock/TailBound.lean` header cites
  `tailKernelDiag_le_of_radial_bound` instead of the phantom hypothesis.
  `grep -rn RotationInvariant PolyFockComplete2` is now empty.  Net +2 lines.
* **5.8** — `Fock.dg`, `dg_add_single`, `dg_sub_le` deleted (`PolyFock/Fock/Rot.lean`);
  `T_unique_aux`/`T_unique` now use `Finsupp.degree` (`ν.degree`), with `map_add`/
  `Finsupp.degree_single` for the peeling step, `Finsupp.degree_mono tsub_le_self` for the
  decrease, and `Finsupp.degree_eq_zero_iff` for the base case (which collapsed from 8 lines to 2).
  Net −23 lines.
* **3.3 (PolyFock part)** — two public lemmas added to `PolyFock/Estimates.lean` (+10 lines):
  `PolyFock.exp_nat_le {n : ℕ} {c : ℝ} (h : (2.7182818286 : ℝ) ^ n ≤ c) : Real.exp n ≤ c` and
  `PolyFock.le_exp_nat {n : ℕ} {c : ℝ} (h : c ≤ (2.7182818283 : ℝ) ^ n) : c ≤ Real.exp n`;
  each is `rw [← Real.exp_one_pow]` plus one `pow_le_pow_left₀` step, and the hypothesis is a
  `norm_num` goal.  They are intended for `DiscretePhaseRetrieval/BlockNorming.lean:45–52,78–84`
  and `DiscretePhaseRetrieval/TailBound.lean:133` in the next batch, where the 8-line pattern
  really is duplicated.  The two `PolyFock/TailBound.lean` sites turned out **not** to be instances
  of that pattern — both are one-liners about `Real.exp 1`, not about `Real.exp n`: `:84` now reads
  `simpa using le_exp_nat (n := 1) (by norm_num)`, and `:293` needed only `1 ≤ e` and now uses
  Mathlib's `Real.one_le_exp` (`le_mul_of_one_le_right`) instead of `nlinarith` with the nine-digit
  bound.  Net for the item +10 lines; no line saved inside `PolyFock/`.

Nothing was skipped.  Total ≈ −78 lines.

## Done 2026-09-06 (batch 3, `DiscretePhaseRetrieval/`)

Full `lake build`, `lake build Check` and `lake build PolyFock.Check` are green; both audits still
report `[propext, Classical.choice, Quot.sound]` only (`Check.lean`:
`DiscretePR.PolyDiscreteSPR_proved`, `DiscretePR.continuous_phase_retrieval`; `PolyFock/Check.lean`:
`tail_bound`, `tail_bound_sqrt`, `tailKernelDiag_radialPoint_le`,
`tailKernelDiag_le_of_radial_bound`, `Fock.layer_kernel_rot`, `Fock.form_Psihat`, `Fock.T_R`).
No statement used by `Main.lean` or `Definitions.lean` changed; `Main.lean` compiles unchanged.

* **§1** — deleted `DiscretePR.euclideanDist_toC` (`Bridge.lean`, confirmed unused by
  `grep -rn euclideanDist_toC`); the module docstring now cites `norm_ofC` alone.  Net −4 lines.
* **§1** — deleted `DiscretePR.polyanalyticEval_eq_old` (`ContinuousPR.lean`); the proof of
  `continuous_phase_retrieval` still elaborates unchanged (the identification of
  `DiscretePR.polyanalyticEval` with `DiscretePolyFock.polyanalyticEval` is definitional and used
  implicitly).  The module docstring says so, and the CPR row of `DiscretePhaseRetrieval/CLAIMS.md`
  no longer names a bridge lemma.  Net −2 lines.
* **2.7** — the copy of `unitBallVol_pos` in `Annulus.lean` is gone; the four uses in
  `Annulus.lean`/`BlockNorming.lean` now resolve to `DiscreteNorming.unitBallVol_pos` through the
  `open DiscreteNorming`.  `Annulus.lean` needed `import DiscreteNorming.Separation` (it imported
  only `DiscreteNorming.Superlevel`, which does not reach `Separation`; `BlockNorming.lean` already
  had it via `DiscreteNorming.Main`).  Net −3 lines.
* **2.8** — the private `mem_box'` in `Coefficients.lean` is deleted; `Coefficients.lean` imports
  `DiscretePhaseRetrieval.Polynomials` (acyclic: `Polynomials` imports only `Bridge`) and its nine
  uses now name `mem_box`.  Net −9 lines.
* **2.9** — the shared derivation is now `DiscretePR.eval_truncate_eq_sum`
  (`polyanalyticEval κ (truncate N F) z = ∑ α ∈ box d N, coeff F α * Φ α κ z`), stated just before
  `eval_truncate` in `Coefficients.lean`.  `eval_truncate` is `rw [eval_truncate_eq_sum, truncPoly,
  map_sum]` plus its old `Finset.sum_congr`, and `tendsto_truncate` drops its `have key` and closes
  with `simpa only [eval_truncate_eq_sum, Function.comp_def] using hsum.comp hbox`.  Net −12 lines.
* **3.2** — new `DiscretePR.norm_le_of_sq_le {E} [SeminormedAddGroup E] {x : E} {c B : ℝ}
  (h : ‖x‖ ^ 2 ≤ c ^ 2 * B) (hc : 0 ≤ c) : ‖x‖ ≤ c * Real.sqrt B` at the end of `Bridge.lean`
  (+11 lines with its section header).  It replaces the two `calc` chains in `TailBound.lean`
  (`truncation_error`, and `hgen` inside the block estimate) by one `exact` each (−13).
  The other two sites listed under 3.2 were **skipped**: `Coefficients.lean` `norm_truncate_le`
  is `‖x‖ ^ 2 ≤ ‖F‖ ^ 2` with no `B` factor (going through the lemma needs `B := 1` and two
  `simpa`s — tried, compiles, reverted as less readable for one line saved), and `Limit.lean:77–79`
  takes square roots in an *equality* `‖A‖ ^ 2 = ‖B‖ ^ 2`, not an inequality.  Net −2 lines.
* **3.3** — the two genuine instances in `BlockNorming.lean` now use the lemmas added in batch 2:
  `Real.exp 13 ≥ 442413` inside `log_610000_le` is `simpa using le_exp_nat (n := 13) (by norm_num)`
  and `Real.exp 4 ≤ 55` inside `base_rpow_ge` is `simpa using exp_nat_le (n := 4) (by norm_num)`.
  Net −14 lines.  The two remaining sites of the item were **skipped** as not instances of the
  pattern: `TailBound.lean:127` is the one-liner `Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9`
  (about `exp 1`, no `pow`/`norm_num` chain — same for `BlockNorming.lean:223–224`, which feeds
  `Real.exp_one_lt_d9` straight to `nlinarith`), and `Polynomials.lean:185` is
  `Real.exp_one_pow` with a *symbolic* exponent `d` inside `Real.pow_div_factorial_le_exp`.

Two items were partially skipped (3.2 and 3.3, reasons above); all seven were attempted.
Total ≈ −46 lines.

## Done 2026-09-06 (batch 4, `ContinuousPhaseRetrieval/`)

Full `lake build`, `lake build Check` and `lake build PolyFock.Check` are green; both audits still
report `[propext, Classical.choice, Quot.sound]` only (`Check.lean`:
`DiscretePR.PolyDiscreteSPR_proved`, `DiscretePR.continuous_phase_retrieval`).
`DiscretePhaseRetrieval/ContinuousPR.lean` compiles **unchanged**; `Definitions.lean`,
`Showcase.lean`, `Main.lean`, `Check.lean` and `lakefile.toml` were not touched.
`ContinuousPhaseRetrieval/PROVENANCE.md` has a new section "2026-09-06 clean-up" listing every
deliberate divergence from the originals, so the `diff -r -I '^import '` recipe stays honest.

* **§1 (dead)** — deleted `HermiteLEAN.rho`, `HermiteLEAN.phi0`, `HermiteLEAN.phi`
  (`ModulusRecovery/Hermite/Definitions.lean`, −20 lines with docstrings) and
  `Hermite1DimdLEAN.rho` (−2).  Confirmed unused by whole-word greps over `PolyFockComplete2`:
  no file `open`s any of the four `…LEAN`/`ModulusRecovery` namespaces, the 46 `phi` hits in
  `ExactModulusRecovery.lean` are proof-local binders, and `HermitekLEAN.phi0` (a different,
  used declaration) takes a level argument.  Net −22 lines.
* **§1 (dead)** — deleted `Hermite1DimdLEAN.Circle` (−2) and `ModulusRecovery.Circle` +
  `ModulusRecovery.zeta` (`ModulusRecovery/ImportedAnalyticInputs.lean`, −14).  Every `Circle.foo`
  in `ExactModulusRecovery.lean`, `ImportedAnalyticInputs.lean`, `TrueLevelBasis.lean` and
  `ProductBasisAndAnnuli.lean` is Mathlib's `_root_.Circle` (mostly written that way explicitly),
  and every `zeta` in `ExactModulusRecovery.lean` is a proof-local `let`.
  `HermiteLEAN.Circle` stays (it is aliased by `HermitekLEAN.Circle`).  Net −16 lines.
* **§1 (duplicate instance)** — deleted `Hermite1DimdLEAN.T_pos` and the second
  `instance : Fact (0 < T)` (`Hermite1Dimd/Definitions.lean`); `Hermite1DimdLEAN.T` is a reducible
  `abbrev` for `HermiteLEAN.T`, whose `Fact` instance is in scope through the existing import.
  Net −4 lines.
* **4.3** — `Hermite1DimdLEAN.oneDimPhi` is now
  `noncomputable def oneDimPhi (k n : ℕ) : ℂ → ℂ := HermitekLEAN.Phi k n`, with
  `import ContinuousPhaseRetrieval.ModulusRecovery.Hermitek.TrueLevelBasis` added to
  `Hermite1Dimd/Definitions.lean` (acyclic: `TrueLevelBasis` imports only `Hermite/Definitions`).
  **No repair was needed at all** — the `unfold oneDimPhi` at `ProductBasisAndAnnuli.lean:312` and
  the `unfold …` / `simpa […]` at `TensorBasis.lean:90,809` still work (`:809` already listed both
  names).  Net −2 lines.
* **4.4** — `Hermite1DimdLEAN.CSpace`, `MultiIndex`, `gaussianDensity`, `gaussianMeasure` are now
  `abbrev` aliases of `ModulusRecovery.Cd`, `ModulusRecovery.MultiIndex`,
  `ModulusRecovery.gaussianDensity`, `ModulusRecovery.gamma_d`, with
  `import ContinuousPhaseRetrieval.ModulusRecovery.Definitions` (acyclic).  The two-line `change`
  that paid the defeq by hand in `TensorBasis.lean` `PhiL2_orthonormal` is gone.  Cost: **23
  tactic sites** in `Hermite1Dimd/{ImportedAnalyticInputs,ProductBasisAndAnnuli}.lean` need the
  target name added to an unfolding list (`rw [gaussianMeasure]` →
  `rw [gaussianMeasure, ModulusRecovery.gamma_d]`, `unfold gaussianDensity` →
  `unfold gaussianDensity ModulusRecovery.gaussianDensity`, and the same inside `simp`/`simpa`
  lists) — mechanical, and **no line was added or removed** by them, so the item was kept rather
  than reverted even though the number of touched lines exceeds ten.  The two `change` bridges at
  `Hermite1Dimd/ImportedAnalyticInputs.lean:30,79` were left alone: they also unfold `oneDimLift`,
  so dropping them is not free.  Net 0 lines (+2 in `Hermite1Dimd/Definitions.lean`, −2 in
  `TensorBasis.lean`).
* **4.1** — `ContinuousPhaseRetrieval/Defs.lean` deleted (134 lines).  Its only importer,
  `ContinuousPhaseRetrieval/ContinuousPR.lean`, now says `import Definitions` and states
  `toSkappa`, `toFun_toSkappa` and `exactModulusRecovery` about `DiscretePR.PolyFock` and
  `DiscretePR.polyanalyticEval`.  **Both private `rfl`s still elaborate**, as predicted: the
  argument swap `DiscretePolyFock.HermitePoly k n = DiscretePR.HermitePoly n k` cancels against
  `Φ κ α = Φ α κ`, so `ModulusRecovery.toFun κ (toSkappa κ F) z` and
  `DiscretePR.polyanalyticEval κ F z` are the same term.  The statement of
  `DiscretePolyFock.exactModulusRecovery` therefore changed spelling (same objects), and its single
  consumer `DiscretePhaseRetrieval/ContinuousPR.lean` needed **no change**.  Net −134 lines.
* **7** — confirmed: `lakefile.toml` needed no change (its globs are `ContinuousPhaseRetrieval.+`).

Nothing was skipped.  The folder went from 16148 to 15970 lines (−178).

Noticed but not done: `HermitekLEAN.Circle` (`Hermitek/TrueLevelBasis.lean:39`) and
`Hermite1DimdLEAN.T` are unreferenced aliases too (the fourth and fifth `Circle`/`T` spellings);
`ModulusRecovery.Idx` (`ModulusRecovery/Definitions.lean:13`) was left out of 4.4 because it is an
alias of `MultiIndex` in the same file, not a cross-file duplicate.  Two prose references to the
now-deleted `DiscretePolyFock.polyanalyticEval` are stale and were left untouched (out of the
batch's edit scope): the module docstring of `DiscretePhaseRetrieval/ContinuousPR.lean` and the CPR
row of `DiscretePhaseRetrieval/CLAIMS.md`.  Both should now say that the earlier development's
`exactModulusRecovery` is stated directly about `DiscretePR.polyanalyticEval`, so no identification
is used.

## Done 2026-09-07 (item 2.1)

Full `lake build` and `lake build Check` are green; `Check.lean` still reports
`[propext, Classical.choice, Quot.sound]` for `DiscretePR.PolyDiscreteSPR_proved` and
`DiscretePR.continuous_phase_retrieval`, and `SignPatterns.sign_patterns` likewise.  No statement
outside the two deleted lemmas changed (`VCInequality.isGrowthBound_of_vcDimLE`,
`relative_deviation`, `relative_deviation_vc`, `SignPatterns.sign_patterns`,
`sign_patterns_warren` are untouched).

* **2.1** — new file `DiscretePhaseRetrieval/AuxiliaryLemmas.lean` (renamed `Auxiliary.lean` on
  2026-09-08; the two `AuxiliaryLemmas` names below are the historical ones) (82 lines, `import Mathlib`
  only, namespace `DiscretePR`), the shared home for lemmas used by several otherwise independent
  parts of the development.  It holds
  `DiscretePR.sum_choose_le_exp_pow (n V : ℕ) (hV : 1 ≤ V) (hVn : V ≤ n) :`
  `(∑ k ∈ Iic V, (n.choose k : ℝ)) ≤ (Real.exp 1 * n / V) ^ V` — the proof moved verbatim from
  `VCInequality/Sauer.lean` (the `Iic` form, the cleaner of the two) — and the 3-line corollary
  `sum_choose_le_exp_pow_range` in the `Finset.range (V+1)` / `ℕ`-cast form that
  `SignPatterns.sign_patterns_warren` needs (`Nat.cast_sum` + `Nat.range_succ_eq_Iic`).
  `VCInequality.sum_choose_le_pow` (`Sauer.lean`, −55) and `SignPatterns.sum_choose_le_exp_pow`
  (`Warren/SignPatterns/SignPatternBound.lean`, −55) are deleted; both files now
  `import DiscretePhaseRetrieval.AuxiliaryLemmas` (acyclic — the new file imports nothing from the
  project) and call the shared lemma at their single call site each
  (`Sauer.lean` `isGrowthBound_of_vcDimLE`; `SignPatternBound.lean` `sign_patterns_warren`, which
  now says `DiscretePR.sum_choose_le_exp_pow_range (n := m + 1) (V := n) hn hnm`).
  The `Sauer.lean` module docstring now attributes the binomial estimate to the shared lemma.
  Net **−24 lines** (167 + 234 = 401 → 115 + 180 + 82 = 377).

Prose updated: `README.md` (the `Sauer.lean` and `SignPatternBound.lean` table rows, and "13 files"
→ "14 files" for `DiscretePhaseRetrieval/`), `PolyFockComplete2/README.md` (the
`DiscretePhaseRetrieval/` row, "89 modules" → "90 modules"), `plans/PLAN-VCInequality.md` (step E
row), `plans/PLAN-SignPatterns.md` (`SignPatternBound.lean` row).  Neither `CLAIMS.md` mentions the
lemma, so both were left alone.  `lakefile.toml` needed no change (the glob
`DiscretePhaseRetrieval.+` picks the new file up).

## Done 2026-09-07 (item 2.14)

Full `lake build` and `lake build Check` are green; `Check.lean` still reports
`[propext, Classical.choice, Quot.sound]` for `DiscretePR.PolyDiscreteSPR_proved` and
`DiscretePR.continuous_phase_retrieval`, and `PolyFock/Check.lean` likewise for `tail_bound`,
`tail_bound_sqrt`, `tailKernelDiag_radialPoint_le`, `tailKernelDiag_le_of_radial_bound`,
`Fock.layer_kernel_rot`, `Fock.form_Psihat`, `Fock.T_R`.  `Main.lean` and `Check.lean` compile
unchanged.

* **2.14** — `PolyFock.phi` and `PolyFock.Phi` (`PolyFock/Basic.lean`) are deleted.
  `PolyFock/Basic.lean` now `import Definitions` and the whole of `PolyFock/` is stated in the
  comparator's basis `DiscretePR.HermitePoly` / `DiscretePR.Φ` (the paper's `φ_{m,n}`, `Φ_{n,q}`),
  brought in per file by `open DiscretePR (…)` — never `open DiscretePR` wholesale, because the
  `abbrev DiscretePR.PolyFock` would shadow the namespace `PolyFock`.  With the two definitions
  gone, the bridge lemmas `DiscretePR.hermitePoly_eq_phi` and `DiscretePR.Phi_eq_Phi`
  (`DiscretePhaseRetrieval/Bridge.lean`) are deleted too and their four call sites
  (`Coefficients.lean`, `KernelBound.lean`, `TailBound.lean` ×2) simply lost a rewrite.
  `DiscretePR.Phi_eq_ev` stays where it was, in `DiscretePhaseRetrieval/Bridge.lean`, and is now
  `(PolyFock.Fock.ev_Psihat _ _ _).symm` — a one-line term proof (so claim P0 of
  `DiscretePhaseRetrieval/CLAIMS.md` keeps its file column).  The only proof-level cost of the
  change is the `star z` vs `starRingEnd ℂ z` spelling of the conjugate: three proofs that unfold
  the definition gained one `simp only [RCLike.star_def]` (`PhiBound.phi_zero`,
  `Fock.ev_Hpoly`, the `φ_{1,1}` example of `PolyFock/Check.lean`) and `norm_phi_le_sum` uses
  `norm_star` in place of `RCLike.norm_conj`.  No declaration was renamed: lemma names still spell
  the basis `phi`/`Phi` (`phi_zero`, `norm_phi_le_sum`, `sq_norm_phi_le`, `Phi_rot`,
  `Phi_radialPoint_eq_zero`, `summable_Phi_sq`, …).  Net **−11 lines** over 13 Lean files.

Statements whose *spelling* changed (`phi` → `HermitePoly`, `Phi` → `Φ`; nothing else in them
changed):

* `PolyFock/Basic.lean` — `tailKernelDiag`, `diagTerm_nonneg`
* `PolyFock/PhiBound.lean` — `phi_zero`, `phi_zero_of_ne`, `norm_phi_le_sum`, `norm_phi_le`,
  `sq_norm_phi_le`
* `PolyFock/Fock/Bridge.lean` — `ev_Hpoly`, `ev_Psi`, `ev_Psihat`
* `PolyFock/Fock/Kernel.lean` — `Phi_rot`, `layer_kernel_rot`, `layer_diag_rot`
* `PolyFock/RadialReduction.lean` — `tailKernelDiag_le_of_radial_bound`
* `PolyFock/TailBound.lean` — `norm_phi_zero_le_one`, `Phi_radialPoint_eq_zero`,
  `norm_Phi_radialPoint_le`, `diagTerm_le`, `tailDiag_finset_le`
* `DiscretePhaseRetrieval/KernelBound.lean` — `sq_norm_phi_le_gen`, `sq_norm_phi_le_tail`,
  `sq_norm_phi_le_mid`, `sum_sq_phi_le` (and the `phi` occurrences inside their proofs)
* `DiscretePhaseRetrieval/TailBound.lean` — `summable_tail_family`

Prose updated: the module docstrings of `PolyFock/Basic.lean` (the two basis bullets became a
paragraph pointing at `Definitions.lean`), `PolyFock/PhiBound.lean`, `PolyFock/Fock/Bridge.lean`,
`PolyFock/Fock/Hermite.lean`, `PolyFock/Fock/Ortho.lean`, `PolyFock/Check.lean` and
`DiscretePhaseRetrieval/Bridge.lean`;
the P0 row of `DiscretePhaseRetrieval/CLAIMS.md` (it no longer claims an identification of two
bases); the `PolyFock/` row of `PolyFockComplete2/README.md`; the root `README.md` (the PolyFock
definitions table, the `Fock/Bridge.lean` row, the "Link to `Showcase.lean`" section); and a
one-line historical note in `plans/PLAN-MainTheorem.md`.  The inventory rows 2.14 and 4.2 above,
and `ContinuousPhaseRetrieval/PROVENANCE.md`, keep the old names as historical records; so does the
sentence in the root `README.md` about the superseded `ShowcaseBridge.lean`.  `import-map.html` is
a generated artifact and still records `PolyFock.Basic` as importing Mathlib only.

## Done 2026-09-07 (item 2.11)

Full `lake build` and `lake build Check` are green; `Check.lean` still reports
`[propext, Classical.choice, Quot.sound]` for `DiscretePR.PolyDiscreteSPR_proved` and
`DiscretePR.continuous_phase_retrieval`, and `PolyFock/Check.lean` likewise for `tail_bound`,
`tail_bound_sqrt`, `tailKernelDiag_radialPoint_le`, `tailKernelDiag_le_of_radial_bound`,
`Fock.layer_kernel_rot`, `Fock.form_Psihat`, `Fock.T_R`.  `Main.lean` and `Check.lean` compile
unchanged, and every statement used downstream (`sq_norm_phi_le`, `sq_norm_phi_le_gen`,
`sq_norm_phi_le_tail`, `sq_norm_phi_le_mid`, `sum_sq_phi_le`, `kernel_bound`, `summable_Phi_sq`)
is **verbatim** what it was.

* **2.11** — the φ-estimate is proved once, in `PolyFock/PhiBound.lean`, as

  ```lean
  lemma PolyFock.norm_phi_le_of_term_le {m n N : ℕ} {T : ℝ} {z : ℂ} (hT : 0 ≤ T)
      (hN : min m n ≤ N)
      (hterm : ∀ r ≤ min m n, (r.factorial : ℝ) * (m.choose r : ℝ) * (n.choose r : ℝ) *
        ‖z‖ ^ (m - r) * ‖z‖ ^ (n - r) ≤ T) :
      ‖HermitePoly m n z‖ ≤ ((N : ℝ) + 1) * T * (Real.sqrt (m.factorial : ℝ))⁻¹
  ```

  — `norm_phi_le_sum`, `Finset.sum_le_sum`, `sum_const`/`card_range`, and dropping `n!` from the
  square root, with the term bound `T` as the only parameter.  Two companions carry the rest of
  the shared text: `PolyFock.phi_term_le` (the termwise step: `r! C(m,r) = (m)_r ≤ m^r` via
  `Nat.descFactorial_le_pow`, `C(n,r) ≤ b`, and the split
  `‖z‖^{m-r} ‖z‖^{n-r} = ‖z‖^{m-n} (‖z‖²)^{n-r}`, for `r ≤ n ≤ m`, concluding
  `≤ a * b * (‖z‖^{m-n} * c)`), and `PolyFock.sq_norm_phi_le_of_norm_le`
  (`‖φ‖ ≤ A (√(m!))⁻¹ → ‖φ‖² ≤ A²/m!`, the identical squaring bookkeeping of
  `PhiBound.lean:186–200` = `KernelBound.lean:179–192`).

  The three consumers are now short corollaries that supply only their own `T`:
  `PolyFock.norm_phi_le` (`T = 2^L (m^L ‖z‖^{m-L})`, its old `hlast` step absorbed into the term
  bound) and `PolyFock.sq_norm_phi_le` in `PolyFock/PhiBound.lean`;
  `DiscretePR.sq_norm_phi_le_gen` (`T = m^k 2^k (‖w‖^{m-k}(1+(‖w‖²)^k))`) and
  `DiscretePR.sq_norm_phi_le_mid` (`T = (4k)! 2^{4k} 2^k (1+‖w‖)^{5k}`, and the prefactor
  discarded through `(√(m!))⁻¹ ≤ 1`) in `DiscretePhaseRetrieval/KernelBound.lean`.

  `sq_norm_phi_le_gen` and `sq_norm_phi_le_mid` were **left in `KernelBound.lean`**: moving them
  next to the core lemma would mean making them (and `midConst`, `midConst_nonneg`) public in
  `PolyFock`, splitting the `midConst`/`sq_norm_phi_le_tail`/`sum_sq_phi_le` group over two
  files for no gain — the four uses of the core lemma read the same from either side.

  `sq_norm_phi_le_mid` is the one instance that does **not** go through `phi_term_le`: it allows
  `m < k`, so `‖z‖^{m-r} ‖z‖^{n-r}` cannot be split off a factor `‖z‖^{m-k}`; it uses the core
  lemma only.  Nothing else resisted unification.

  Line count: `PhiBound.lean` 206 → 241, `KernelBound.lean` 546 → 484, i.e. **−27 lines** in
  total, of which about +41 are new prose (the two module docstrings and the three core
  docstrings); counting code lines only, ≈ **−60**.  The saving is smaller than the −75 the
  inventory predicted because the three term bounds `T` are genuinely different and account for
  20–35 lines each; what disappeared is the sum/normalisation/squaring skeleton, which used to be
  written three times.

Prose updated: the module docstrings of `PolyFock/PhiBound.lean` (it now describes the core
estimate and lists its three instances) and of `DiscretePhaseRetrieval/KernelBound.lean`;
row K of `DiscretePhaseRetrieval/CLAIMS.md` (naming `PolyFock.norm_phi_le_of_term_le` as the
shared input of `sq_norm_phi_le_gen`/`sq_norm_phi_le_mid`); the root `README.md` section
"Deviation from the paper's proof of the estimate".  `PolyFockComplete2/README.md` needed no
edit — its `PolyFock/` row describes the folder, not the estimate.

Also fixed in the root `README.md` (noticed earlier, unrelated to 2.11): the PolyFock definitions
table still listed `kernel`, `tailKernel` and the lemma `tailKernel_diag`, deleted on 2026-09-06;
the table now has the single row `tailKernelDiag` and a sentence recording that the kernels
themselves are never formed.

## Done 2026-09-08 (item 2.10 + rename)

Full `lake build`, `lake build Check` and `lake build PolyFock.Check` are green; `Check.lean`
still reports `[propext, Classical.choice, Quot.sound]` for `DiscretePR.PolyDiscreteSPR_proved`
and `DiscretePR.continuous_phase_retrieval`, and its
`example : type_of% @DiscretePR_Showcase.PolyDiscreteSPR := @DiscretePR.PolyDiscreteSPR_proved`
still elaborates (`Main.lean`'s theorem statement is untouched).

* **Rename** — `DiscretePhaseRetrieval/AuxiliaryLemmas.lean` → `DiscretePhaseRetrieval/Auxiliary.lean`
  (module `DiscretePhaseRetrieval.Auxiliary`), the file having outgrown "lemmas": it now also
  holds a definition.  The two importers (`VCInequality/Sauer.lean`,
  `Warren/SignPatterns/SignPatternBound.lean`), the module docstring, both `README.md`s and
  `plans/PLAN-VCInequality.md`, `plans/PLAN-SignPatterns.md` were updated; the stale
  `.lake/build/{lib/lean,ir}/DiscretePhaseRetrieval/AuxiliaryLemmas.*` artefacts were deleted.
  `lakefile.toml` needed no change (the glob `DiscretePhaseRetrieval.+` picks the file up).

* **2.10** — the three spellings of the total degree of a multi-index are now one.
  `Auxiliary.lean` gains

      /-- The size `‖α‖₁ = ∑ i, α i` of a multi-index `α ∈ ℕ^d` (the paper's `|α|`; for the
      Landau level `κ` this is `|κ|`). -/
      def size (α : Fin d → ℕ) : ℕ := ∑ i, α i

      @[inherit_doc size]
      scoped notation:max "‖" q "‖₁" => size q

  (`scoped notation` with `@[inherit_doc]` compiles).  `DiscretePR.deg`
  (`DiscretePhaseRetrieval/Defs.lean:32`) is deleted and its ~150 uses in
  `DiscretePhaseRetrieval/*.lean` and `Main.lean` respelled `‖·‖₁`; `deg_cons` and
  `deg_eq_head_add_tail` (`Polynomials.lean`) kept their names (`deg_cons`, `deg_eq_head_add_tail`: they refer to the degree of the polynomial; renamed back on 2026-09-08 at the user's request).
  `Defs.lean` now imports `DiscretePhaseRetrieval.Auxiliary` explicitly (it would also get it
  transitively through `PolyFock.TailBound`).  In `PolyFock/` the inline `∑ i, n i` spellings
  are gone from `Basic.lean` (`tailKernelDiag`, `diagTerm_nonneg`), `RadialReduction.lean`,
  `TailBound.lean` (`diagTerm_le`, `tailDiag_finset_le`), `Fock/Layer.lean` (`W`, `Psi_mem_W`,
  `Psi_mem_W'`, `R_Psi_mem_W`), `Fock/Kernel.lean` (`mem_LayerIdx`, `R_Psihat_mem_W`) and
  `Fock/Ortho.lean` (`form_Psi_aux`); those files carry `open scoped DiscretePR` (not
  `open DiscretePR`, which would clash the abbrev `DiscretePR.PolyFock` with the namespace
  `PolyFock`).  Only the low-level `Function.update` bookkeeping (`sum_update_succ`,
  `sum_update_pred`) and the local sum splittings inside proofs still speak of `Finset.sum`;
  eight proof steps in three files unfold once with `simp only [DiscretePR.size]` (or `simpa`).  The seam
  `simp only [deg, true_and]` at `DiscretePhaseRetrieval/TailBound.lean:72`, which used to
  reconcile the two spellings, is now `simp only [true_and]`.  `Fock.dg` was already gone.

  Statements whose spelling changed (nothing else about them changed): `PolyFock.tailKernelDiag`,
  `PolyFock.diagTerm_nonneg`, `PolyFock.tailKernelDiag_le_of_radial_bound`,
  `PolyFock.diagTerm_le`, `PolyFock.tailDiag_finset_le`, `PolyFock.Fock.W`,
  `PolyFock.Fock.Psi_mem_W`, `PolyFock.Fock.Psi_mem_W'`, `PolyFock.Fock.R_Psi_mem_W`,
  `PolyFock.Fock.mem_LayerIdx`, `DiscretePR.box`, `DiscretePR.mem_box`,
  `DiscretePR.deg_cons`, `DiscretePR.deg_eq_head_add_tail`,
  `DiscretePR.totalDegree_Psihat_le`, `DiscretePR.totalDegree_le_of_mem_VqN`,
  `DiscretePR.kernel_bound`, `DiscretePR.truncate_apply`, `DiscretePR.tail_eval_le`,
  `DiscretePR.summable_tail_family`, `DiscretePR.tail_le_tailKernelDiag`,
  `DiscretePR.truncation_error`, `DiscretePR.modulus_error`, `DiscretePR.block_norming`,
  `DiscretePR.block_estimate` (and the private auxiliaries of those files).
  `Main.lean`'s theorem statement never mentioned the degree and is unchanged; its proof's local
  sequence facts now say `‖q‖₁`.

  Net **+22 lines** (the new definition, notation and docstrings, minus the deleted `deg`).

Prose updated: the module docstrings of `DiscretePhaseRetrieval/{Auxiliary,Defs,Polynomials,
Coefficients,KernelBound,TailBound,BlockNorming,BlockEstimate}.lean` and of
`PolyFock/{Basic,Rotation,TailBound}.lean`, `PolyFock/Fock/{Layer,Kernel,Ortho}.lean` (every
`|α|`, `|κ|`, `|𝐧|`, `|𝐪|` denoting a size is now `‖·‖₁`; the paper's `|α|` is mentioned once,
in the docstring of `size`); rows P1, P2 and the "Deviations" bullet of
`DiscretePhaseRetrieval/CLAIMS.md`; the `DiscretePhaseRetrieval/` row of
`PolyFockComplete2/README.md`; the `tailKernelDiag`, layer-kernel and main-theorem parts of the
root `README.md`.  The inventory rows above (item 2.1, item 2.10) are historical and stay as
written.

## Done 2026-09-08 (unreached declarations in `ContinuousPhaseRetrieval/`)

Everything in `ContinuousPhaseRetrieval/` that the dependency scan of the compiled environment
does not reach from `DiscretePolyFock.exactModulusRecovery` (the folder's single entry point, used
once by `DiscretePhaseRetrieval/ContinuousPR.lean`) is deleted.  Per-file line counts:

| file | before | after |
| --- | ---: | ---: |
| `ModulusRecovery/Definitions.lean` | 127 | 119 |
| `ModulusRecovery/Hermite/Definitions.lean` | 64 | 55 |
| `ModulusRecovery/Hermitek/TrueLevelBasis.lean` | 1825 | 1800 |
| `ModulusRecovery/Hermite1Dimd/Definitions.lean` | 105 | 102 |
| `ModulusRecovery/Hermite1Dimd/ProductBasisAndAnnuli.lean` | 365 | 310 |
| `ModulusRecovery/ImportedAnalyticInputs.lean` | 2674 | 2668 |
| `ModulusRecovery/TensorBasis.lean` | 1246 | 1192 |
| `ModulusRecovery/ExactModulusRecovery.lean` | 8920 | 8920 |
| `ModulusRecovery/Hermite1Dimd/ImportedAnalyticInputs.lean` | 554 | 554 |
| `ContinuousPR.lean` | 70 | 70 |
| **folder total** | **15950** | **15790** |

The declaration-level list is in `ContinuousPhaseRetrieval/PROVENANCE.md`, section
"2026-09-08 removal of unreached declarations".  This closes item 4.3's remaining duplicate pair
(`Hermite1DimdLEAN`'s private `circle_pow_factor` / `Phi_rotation_equivariant` copies of the
`HermitekLEAN` lemmas).  `lake build` and `lake build Check` pass; the axioms of
`DiscretePR.PolyDiscreteSPR_proved` and `DiscretePR.continuous_phase_retrieval` are still exactly
`propext, Classical.choice, Quot.sound`.
