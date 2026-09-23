# Provenance of `ContinuousPhaseRetrieval/`

Verbatim copies (2026-09-02) of the import closure of `DiscretePolyFock/ContinuousPR.lean` in
`Discrete Phase Retrieval/DiscreteFock/PolyFockComplete` (Lean/Mathlib v4.30.0), 11 files,
compiled here under Lean/Mathlib v4.31.0-rc2. Only the `DiscretePolyFock.exactModulusRecovery`
theorem is used, once, by `DiscretePhaseRetrieval/ContinuousPR.lean`.

Mechanical change applied to every file at copy time:
`import DiscretePolyFock.X` → `import ContinuousPhaseRetrieval.X` (module prefix only).

Check against the originals:
```bash
diff -r -I '^import ' "DiscreteFock/PolyFockComplete/DiscretePolyFock" "ContinuousPhaseRetrieval" --exclude=PROVENANCE.md
```
(the originals directory has more files than the closure; only the 11 copied files are compared).
Add `--strip-trailing-cr`: the copies use LF, the originals CRLF.

**Since 2026-09-06 the copies are no longer verbatim**: a de-duplication pass deleted `Defs.lean`
(10 files remain) and edited seven of the ten survivors.  The diff above now reports those deliberate differences as
well; they are listed in full in "2026-09-06 clean-up" below.

## Patches needed for the newer toolchain

Compiled 2026-09-03 under Lean/Mathlib v4.31.0-rc2. **No theorem statement was changed, no proof
was rewritten, no `sorry` was introduced.** 5 of the 11 files needed no change at all
(`Defs.lean`, `ContinuousPR.lean`, `ModulusRecovery/Definitions.lean`,
`ModulusRecovery/Hermite/Definitions.lean`, `ModulusRecovery/Hermite1Dimd/Definitions.lean`).
The 62 patched tactic sites below (in 6 files) are all local repairs of tactic invocations.
They fall into five groups,
each caused by one v4.30 → v4.31 change:

* **(A) `simpa … using e` is now a syntactic match.** After simplifying both the goal and `e`'s
  type, `simpa` no longer accepts a merely definitionally equal result. Where the residual
  difference is pure `rfl` (`f * g` vs `fun x => f x * g x`, `⇑(h.toSchwartzMap _)` vs `g`,
  `Cd d` vs `CSpace d`, `gamma_d d` vs `gaussianMeasure d`, `MeasurableSpace.pi` vs
  `MeasureSpace.pi.toMeasurableSpace`, a `let`-bound name vs its value, an unfolded `def`), the
  fix is `exact e` (which still uses full defeq), sometimes after a `show`/`change` that restates
  the goal in the shape simp produces, or after `simp only [...] at e`.
* **(B) `simp` no longer unfolds `Function.comp`, `Function.uncurry`, `Pi.mul`, `Pi.star`
  through the bare definition name.** Fix: name the equation lemma — `Function.comp_def`,
  `Function.uncurry_def`, `Pi.mul_def`, `Pi.star_def` — in the same simp set.
* **(C) `convert … using 1` on `HasDerivAt`/`Integrable` now emits extra congruence subgoals**
  for the `AddCommGroup`/`Module`/`MeasurableSpace` instance arguments (Mathlib gained further
  instance paths on `ℂ`, e.g. via `CStarAlgebra`). Fix: dispatch them with `rfl`, i.e.
  `all_goals first | rfl | <the original closing tactic>` (or an explicit `· rfl` bullet).
* **(D) renamed/retyped Mathlib lemmas.** `HasDerivAt.pow` now concludes `HasDerivAt (f ^ n)`;
  the pointwise form is `HasDerivAt.fun_pow`. `Integrable.re` now yields `RCLike.re`.
  `SchwartzMap`'s Fourier transform is now `𝓕 : 𝓢(V,E) → 𝓢(V,E)`, related to the function-level
  one by `SchwartzMap.fourier_coe`.
* **(E) `ring_nf`/`simp` now error on "no progress"** (they used to be no-ops), which turned the
  leftover goals of (C) into hard errors.

Deprecation warnings (`integral_finset_sum`, `push_neg`, `continuous_finset_sum`,
`ofReal_norm_eq_enorm`, …) were left untouched: they are warnings, not errors.

### `ModulusRecovery/Hermitek/TrueLevelBasis.lean` (1 patch)

| line | before | after | why |
|---|---|---|---|
| 744 (`integrable_weightedDiag`) | `convert hC.re using 1` | `convert hC.re using 1` + `funext z` + `exact (RCLike.ofReal_re (K := ℂ) (f z)).symm` | (D) `Integrable.re` now produces `RCLike.re`, so `convert … using 1` no longer closes the residual goal by `rfl` |

### `ModulusRecovery/ImportedAnalyticInputs.lean` (16 patches)

| line | before | after | why |
|---|---|---|---|
| 288 | `simpa [s, μ] using hg₃` | `exact hg₃` | (A) `⇑(hg₁.toSchwartzMap hg₂)` vs `g` |
| 572 | `simpa [… mul_comm] using congrFun h ω` | `simpa [… mul_comm, Function.comp_def] using congrFun h ω` | (B) |
| 602 | `simpa [schwartzCompSubConstCLM_apply] using …` | `simpa [schwartzCompSubConstCLM_apply, Function.comp_def] using …` | (B) |
| 781 | `simpa using SchwartzMap.integral_norm_sq_fourier …` | `simpa [SchwartzMap.fourier_coe] using …` | (D) |
| 796 | `simpa [stftRep_schwartz_eq_fourier_apply] using h_fourier` | `simpa [stftRep_schwartz_eq_fourier_apply, SchwartzMap.fourier_coe] using h_fourier` | (D) |
| 848 | `simpa [Pi.mul_apply, Pi.star_apply, μ] using …` | `simpa [Pi.mul_def, Pi.star_def, μ] using …` | (B) |
| 875 | `simpa [Pi.mul_apply, Pi.star_apply, μ] using …` | `simpa [Pi.mul_def, Pi.star_def, μ] using …` | (B) |
| 1311 | `simpa using (continuous_enorm.tendsto 0).comp hdiff` | `simpa [Function.comp_def] using …` | (B) |
| 1314 | `simpa [ENNReal.zero_rpow_of_pos …] using …comp hnorm` | same + `Function.comp_def` | (B) |
| 1325 | `simpa [ENNReal.zero_rpow_of_pos …] using …comp hInt` | same + `Function.comp_def` | (B) |
| 1651 | `simpa [K, Function.uncurry, mul_comm] using …` | `simpa [K, Function.uncurry_def, Function.comp_def, mul_comm] using …` | (B) |
| 1662 | `simpa [hLp, fLp, μ] using stftRep_sq_integrable_schwartz_realVec h f` | `exact stftRep_sq_integrable_schwartz_realVec h f` | (A) `PhaseSpace d`/`volume` vs `RealVec d × RealVec d`/`volume.prod volume` |
| 2078 | `simpa [mul_comm] using hg.mul hf` | `simpa [Pi.mul_def, mul_comm] using hg.mul hf` | (B) |
| 2188 | `simpa [Aₙ, Bₙ, Pi.mul_apply] using …` | `simpa [Aₙ, Bₙ, Pi.mul_def] using …` | (B) |
| 2401 | `simpa [K, G, Function.uncurry, mul_assoc, …] using hG.swap` | `simpa [K, G, Function.uncurry_def, Function.comp_def, mul_assoc, …] using hG.swap` | (B) |
| 2416 | `simpa [μ] using hSphase` | `exact hSphase` | (A) same measurable-space/measure mismatch as 1662 |

### `ModulusRecovery/Hermite1Dimd/ImportedAnalyticInputs.lean` (7 patches)

| line | before | after | why |
|---|---|---|---|
| 43 | `simpa [e, mul_assoc] using (volume_preserving_funUnique …).integrable_comp_of_integrable …` | `have hcomp := (…).integrable_comp_of_integrable …` + `simp only [Function.comp_def] at hcomp` + `exact hcomp` | (A)+(B) `(f ∘ ·) `, and `Fin 1 → ℂ` vs `CSpace 1` |
| 58 | `convert hsmul.const_mul (1 / Real.pi) using 1` + `funext z` | inserted `· rfl` before `funext z` | (C) `MeasurableSpace.pi = MeasureSpace.pi.toMeasurableSpace` |
| 105 | `convert hEq0 using 1 <;> ext z <;> ring` | `convert hEq0 using 1 <;> rfl` | (C) the residual goal is now the whole integral equality, closed by `rfl` |
| 115 | `convert hEq using 1 <;> ext z <;> rfl` | `convert hEq using 1 <;> rfl` | (C) |
| 320 | `simpa [e] using …integrable_comp_of_integrable …` | `simpa [e, Function.comp_def] using …` | (B) |
| 369 | `convert hEq0 using 1 <;> ext z <;> rfl` | `convert hEq0 using 1 <;> rfl` | (C) |
| 443 | `convert hprod_volume using 1` + `funext z` | inserted `· rfl` before `funext z` | (C) |

### `ModulusRecovery/Hermite1Dimd/ProductBasisAndAnnuli.lean` (5 patches)

| line | before | after | why |
|---|---|---|---|
| 43 | as line 43 of the file above (the same lemma is duplicated) | idem | (A)+(B) |
| 57 | `convert hsmul.const_mul (1 / Real.pi) using 1` + `funext z` | inserted `· rfl` | (C) |
| 216 | `simpa [oneDimLift] using (oneVariableBasisOrthonormal …)` | `have h1 := oneVariableBasisOrthonormal …` + `rw [if_pos rfl] at h1` + `exact h1` | (A) `oneDimLift f` vs `fun z => f (z 0)` |
| 223 | `simpa [oneDimLift, hq] using (oneVariableBasisOrthonormal …)` | `have h1 := …` + `rw [if_neg hq] at h1` + `exact h1` | (A) |
| 225 | `simpa [PhiKappaAlpha] using hfactor.2.trans hprod` | `exact hfactor.2.trans hprod` | (A) `PhiKappaAlpha κ α` vs its body |

### `ModulusRecovery/TensorBasis.lean` (6 patches)

| line | before | after | why |
|---|---|---|---|
| 145 | `simpa using Hermite1DimdLEAN.finiteParseval kappa ⟨F⟩` | `exact …` | (A) `⟨F⟩.support` vs `F.support` |
| 149 | `simpa [hermiteNormSq, gaussianL2NormSq, evalPkappa_eq_evalHermiteSum kappa F] using hparseval` | `rw [evalPkappa_eq_evalHermiteSum kappa F]` + `exact hparseval` | (A) `Cd d`/`gamma_d d` vs `CSpace d`/`gaussianMeasure d` |
| 236 | `simpa using phi1D_eq_oneDimPhi k m z` | `exact phi1D_eq_oneDimPhi k m z` | (A) `oneDimPhi` vs `HermitekLEAN.Phi` (identical bodies) |
| 377 | `simpa [partialSum, toFun, HasSum, SummationFilter.unconditional] using …` | same + `Function.comp_def` | (B) |
| 537 | `simpa [gaussianInner, Phi_eq_PhiKappaAlpha, eq_comm] using horth` | prefixed by `change (∫ z : Hermite1DimdLEAN.CSpace d, …  ∂ Hermite1DimdLEAN.gaussianMeasure d) = …` | (A) same `Cd`/`gamma_d` mismatch, restated so the two simp normal forms agree |
| 616 | `simpa [HasSum, SummationFilter.unconditional, evalPkappaL2_truncateFinset …] using …` | same + `Function.comp_def` | (B) |

### `ModulusRecovery/ExactModulusRecovery.lean` (27 patched sites, 17 rows)

| line | before | after | why |
|---|---|---|---|
| 81–83 | `ext v` / `simp only [Pi.sub_apply]` / `ring_nf` | `all_goals first \| rfl \| (funext v; simp only [Pi.sub_apply]; ring)` | (C)+(E) |
| 87 | `ring` | `all_goals first \| rfl \| ring` | (C)+(E) |
| 1492 | `simpa [sub_eq_add_neg] using (hu.add_const (z * u)).sub hz` | `exact (hu.add_const (z * u)).sub hz` | (A) |
| 1822 | `simpa [complex_monomial_gaussian] using complex_monomial_gaussian_memLp k` | `exact complex_monomial_gaussian_memLp k` | (A) |
| 1824 | idem for `l` | `exact complex_monomial_gaussian_memLp l` | (A) |
| 1825 | `simpa only [Pi.mul_apply] using hk.integrable_mul hl` | `exact hk.integrable_mul hl` | (A) |
| 2733 | `simpa [realHermite1D] using (…).const_mul (…)` | `exact (…).const_mul (…)` | (A) |
| 3479 | `simpa [μpi] using hg_pi` | `exact hg_pi` | (A) `Measure.pi fun _ => volume` vs `volume` |
| 3484 | `simpa [Function.comp_def, g, realHermiteTensorRep] using hcomp` | `exact hcomp` | (A) `WithLp 2 (Fin d → ℝ)` vs `RealVec d`, `x.ofLp q` vs `x q` |
| 4146 | `simpa [oneDWindowAmbiguityFactor, realHermite1D_zero, inner, mul_assoc, mul_comm, mul_left_comm] using …` | same + `div_eq_mul_inv` | (A) `x / 2` vs `x * 2⁻¹` |
| 4497, 4502, 4534, 4540 | `simpa using (hasDerivAt_id z).pow n` | `simpa using (hasDerivAt_id z).fun_pow n` | (D) |
| 4499, 4530, 4536 | `ring` (after `convert … using 1`) | `all_goals first \| rfl \| ring` | (C)+(E) |
| 4503, 4541 | `convert hpow.const_mul c using 1 <;> ring_nf` | `convert hpow.const_mul c using 1` + `all_goals first \| rfl \| ring \| (funext y; ring)` | (C)+(E) |
| 4505–4506 | `convert h.deriv using 1` + `ring` | `exact h.deriv.trans (by ring)` | (C) |
| 7039 | `simp only [mul_zero, …]` + `ring` | `all_goals first \| rfl \| (simp only [mul_zero, …]; ring)` | (C)+(E) |
| 7985 | `simpa using hswap.symm` | prefixed by a `change` restating `𝓕` as `VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V)` (definitionally the same) | (A) |
| 8326, 8339, 8346, 8351, 8812 | `simpa [centerDiff / f0, μ / g0, μ / coeffSkappa] using e` | `exact e` | (A) `f - g` vs pointwise, `t + -(c • x)` vs `t - c • x`, `(w • U).coeff` vs `w * U.coeff` |

## 2026-09-06 clean-up (deliberate divergences from the originals)

The files are **no longer byte-identical** to the originals: the de-duplication pass recorded in
`plans/DUPLICATES.md` (batch 4) removed dead declarations and replaced four duplicated definitions
by aliases.  No theorem statement changed, no proof was rewritten, no `sorry` was introduced, and
`DiscretePolyFock.exactModulusRecovery` is still the only exported result (its statement now names
`DiscretePR.PolyFock` / `DiscretePR.polyanalyticEval` instead of the deleted copies in
`Defs.lean`; the two are the same objects, and its single consumer
`DiscretePhaseRetrieval/ContinuousPR.lean` compiles unchanged).

The `diff -r -I '^import '` recipe above therefore now also reports the following **deliberate**
differences, in addition to the 62 toolchain patches:

* `Defs.lean` — **file deleted** (134 lines).  It restated `HermitePoly`, `Φ`, `gaussianDensity`,
  `γ`, `PolyFock`, `coeff`, `polyanalyticEval`, `PolyFockSpace`, `PhaseRetrievalSet` (identical to,
  or a swap of the two indices of, the public `Definitions.lean`) plus the unreferenced
  `gaussianDensityParam`, `γParam`, `polyanalyticEvalParam`, `PolyFockSpaceParam`, `memBox`,
  `boxTruncFun`, `boxTrunc` (+4 lemmas) and `UniformlyDiscrete`.  Its only importer was
  `ContinuousPR.lean`.
* `ContinuousPR.lean` — `import ContinuousPhaseRetrieval.Defs` → `import Definitions` (the
  top-level public statement file, which imports only Mathlib); `PolyFock d` →
  `DiscretePR.PolyFock d` and `polyanalyticEval` → `DiscretePR.polyanalyticEval` throughout
  (5 declaration lines plus docstrings).  The two private `rfl`s (`toSkappa`, `toFun_toSkappa`)
  are unchanged and still elaborate: the index swap
  `DiscretePolyFock.HermitePoly k n = DiscretePR.HermitePoly n k` cancels against
  `Φ κ α = Φ α κ`.
* `ModulusRecovery/Hermite/Definitions.lean` — deleted the unreferenced `HermiteLEAN.rho`,
  `HermiteLEAN.phi0`, `HermiteLEAN.phi` with their docstrings (−20 lines).
* `ModulusRecovery/ImportedAnalyticInputs.lean` — deleted the unreferenced `ModulusRecovery.Circle`
  and `ModulusRecovery.zeta` (−14 lines with the surrounding blank lines).  Every `Circle.foo` in
  the proofs of this file and of `ExactModulusRecovery.lean` is Mathlib's `_root_.Circle`, and
  every `zeta` there is a proof-local `let`.
* `ModulusRecovery/Hermite1Dimd/Definitions.lean` — deleted the unreferenced
  `Hermite1DimdLEAN.rho` and `Hermite1DimdLEAN.Circle`, and the duplicate `T_pos` /
  `instance : Fact (0 < T)` (supplied by `HermiteLEAN` through the existing import, `T` being a
  reducible alias of `HermiteLEAN.T`).  `oneDimPhi` is now
  `noncomputable def oneDimPhi (k n : ℕ) : ℂ → ℂ := HermitekLEAN.Phi k n` (the bodies were
  byte-identical), which adds
  `import ContinuousPhaseRetrieval.ModulusRecovery.Hermitek.TrueLevelBasis`.  `CSpace`,
  `MultiIndex`, `gaussianDensity` and `gaussianMeasure` are now `abbrev` aliases of
  `ModulusRecovery.Cd`, `ModulusRecovery.MultiIndex`, `ModulusRecovery.gaussianDensity` and
  `ModulusRecovery.gamma_d` (literally identical bodies), which adds
  `import ContinuousPhaseRetrieval.ModulusRecovery.Definitions`.  Both new imports are acyclic.
* `ModulusRecovery/Hermite1Dimd/ImportedAnalyticInputs.lean`,
  `ModulusRecovery/Hermite1Dimd/ProductBasisAndAnnuli.lean` — 23 tactic sites only: the alias of
  the previous item costs one extra name in an unfolding list, `rw [gaussianMeasure]` →
  `rw [gaussianMeasure, ModulusRecovery.gamma_d]`, `unfold gaussianDensity` →
  `unfold gaussianDensity ModulusRecovery.gaussianDensity`, and likewise inside `simp`/`simpa`
  lists.  No line was added or removed.
* `ModulusRecovery/TensorBasis.lean` — the two-line `change` in `PhiL2_orthonormal` that paid the
  `Cd`/`CSpace` and `gamma_d`/`gaussianMeasure` defeq by hand is gone (the aliases make it a
  no-op).

Net effect on the folder: 16148 → 15970 lines.  Files whose content is still verbatim (modulo the
toolchain patches): `ModulusRecovery/Definitions.lean`,
`ModulusRecovery/ExactModulusRecovery.lean`, `ModulusRecovery/Hermitek/TrueLevelBasis.lean`.

## Audit

```
$ grep -rn "sorry\|^axiom" ContinuousPhaseRetrieval --include=*.lean   # no matches, not even in comments
$ #print axioms DiscretePolyFock.exactModulusRecovery
'DiscretePolyFock.exactModulusRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
# (re-checked 2026-09-06 after the clean-up above; `lake build Check` unchanged)
```

### 2026-09-08 clean-up (continued)

Unreferenced aliases removed: `HermiteLEAN.Circle` (`ModulusRecovery/Hermite/Definitions.lean`, was `abbrev Circle := AddCircle T`; every use of a circle in the proofs is Mathlib's `AddCircle` or `_root_.Circle` directly), `HermitekLEAN.Circle` (`ModulusRecovery/Hermitek/TrueLevelBasis.lean`, alias of the former) and `Hermite1DimdLEAN.T` (`ModulusRecovery/Hermite1Dimd/Definitions.lean`, alias of `HermiteLEAN.T`). `ModulusRecovery.Idx` is kept: it is used unqualified in its own file.

### 2026-09-08 removal of unreached declarations

A dependency scan of the compiled environment (proof terms included, auxiliary constants folded
in) starting from `DiscretePolyFock.exactModulusRecovery` — the single declaration of this folder
that `DiscretePhaseRetrieval/ContinuousPR.lean` uses — found the following hand-written
declarations unreached.  All of them are deleted, together with their own docstrings; no `example`,
`#check`/`#eval`/`#print` or prose elsewhere in `PolyFockComplete2/` referred to any of them.

* `ModulusRecovery/Definitions.lean` (127 → 119) — `CircleFreq`, `CircleTrigPoly`, the `Norm`
  instance `instNormCircleTrigPoly` on `CircleTrigPoly`, and `instance : Fact (0 < (2 * Real.pi : ℝ))`.
* `ModulusRecovery/Hermite/Definitions.lean` (64 → 55) — `HermiteLEAN.T`, `HermiteLEAN.T_pos` and
  `instance : Fact (0 < T)`.  `weightedInner`, `weightedNormSq` and `weightedNorm` stay; they are
  what `Hermitek/TrueLevelBasis.lean` re-exports.
* `ModulusRecovery/Hermitek/TrueLevelBasis.lean` (1825 → 1800) — `HermitekLEAN.T` (the `abbrev` for
  `HermiteLEAN.T`), `phi0`, `hermiteCoeff_phi0`, `qkn`, `qkn_real`.  The file's own
  `circle_pow_factor` and `Phi_rotation_equivariant` are *reached* (used by
  `Phi_rotation_equivariant` resp. the level-`k` rotation argument) and stay.
* `ModulusRecovery/Hermite1Dimd/Definitions.lean` (105 → 102) — `Hermite1DimdLEAN.totalDegree`.
* `ModulusRecovery/Hermite1Dimd/ProductBasisAndAnnuli.lean` (365 → 310) — the private
  `circle_pow_factor` and `Phi_rotation_equivariant` (duplicates of the `HermitekLEAN` pair above;
  the second was the only user of the first).
* `ModulusRecovery/ImportedAnalyticInputs.lean` (2674 → 2668) — the structure `CircleArc` with its
  fields, hence also the projections `CircleArc.left_le_right` and `CircleArc.width_le_period`.
* `ModulusRecovery/TensorBasis.lean` (1246 → 1192) — `exact_truncate_coeff_energy`,
  `toFun_as_L2_eq_boxLimit` and `toFun_represents_toL2` (the last was a one-line restatement of the
  one before it, and nothing else cited either).

Nothing else was touched: no import list, `set_option`, section comment or surrounding proof was
edited, and the four untouched files (`ContinuousPR.lean`,
`ModulusRecovery/ExactModulusRecovery.lean`, `ModulusRecovery/Hermite1Dimd/ImportedAnalyticInputs.lean`)
are unchanged.

Net effect on the folder: 15950 → 15790 lines (−160).  After this pass no file of the folder is
verbatim in the sense of the `diff -r -I '^import '` recipe above except
`ModulusRecovery/ExactModulusRecovery.lean` and
`ModulusRecovery/Hermite1Dimd/ImportedAnalyticInputs.lean`.

```
$ lake build            # whole package, no errors, no sorry outside Showcase.lean
$ lake build Check
'DiscretePR.PolyDiscreteSPR_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'DiscretePR.continuous_phase_retrieval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Fork (2026-09-17)

As of 2026-09-17 this folder is maintained independently of
`Discrete Phase Retrieval/DiscreteFock/PolyFockComplete`.  The sections above describe its origin
and its state at the fork; they are not updated any more, and the `diff -r -I '^import '` recipe of
the first section is no longer meaningful, because the files below now diverge from the originals
by design rather than by the listed repairs.

First change after the fork: the phantom level parameter of the coefficient types was removed
(`ModulusRecovery/{Definitions,TensorBasis,ExactModulusRecovery}.lean` and `ContinuousPR.lean`), so
that a `kappa` in this folder is now always a level the statement really uses — the basis `Phi
kappa` or the window `varphiKappa kappa`.  Main renamings: `Skappa d kappa` → `Coeffs d`,
`Pkappa d kappa` → `Pfin d`, `coeffSkappa` → `coeffAt`, `coeffPkappa` → `coeffPfin`,
`evalPkappa` → `evalPfin`, `ofPkappa kappa` → `ofPfin`, `instNormPkappa` → `instNormPfin`,
`bKappa kappa` → `hermiteExpansion`, `bKappaRep kappa` → `hermiteExpansionRep`,
`TKappa kappa` → `phaseToC`, `QKappa kappa` → `gaussQuad`, `WKappa kappa` → `gaussWeight`,
`tKappaCoordPoly`/`tKappaConjCoordPoly`/`PhiTKappaMvPolynomial` →
`phaseToCPoly`/`phaseToCConjPoly`/`PhiPhaseToCPoly`, `skappa_ext_coeff_*` → `Coeffs.ext_coeffAt`
(the two duplicates merged into one), `lift_unimodular_phase_L2_to_Skappa` →
`lift_unimodular_phase_L2_to_coeffs`, `ambiguity_eq_to_skappa_phase` →
`ambiguity_eq_to_coeffs_phase`, `exact_modulus_recovery_skappa(_ae)` →
`exact_modulus_recovery_coeffs(_ae)`, `toSkappa` → `toCoeffs`, and the `_exact_wip` suffixes of the
affected lemmas dropped.  No statement about the mathematics changed and no proof was rewritten.
