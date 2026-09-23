# Plan: remove the phantom level index from the coefficient types of `ContinuousPhaseRetrieval/`

**Status (2026-09-17): executed.**  `lake build ContinuousPhaseRetrieval.ModulusRecovery.ExactModulusRecovery`
passes with no new warnings; `exact_modulus_recovery_coeffs` depends on `propext`, `Classical.choice`,
`Quot.sound` only.  Deviations from the text below: `summable_realHermiteTensorL2_coeff_smul_of_orthonormal`
also lost its level (phantom by the rule of Section 1); the injectivity statements read
`Function.Injective (hermiteExpansion (d := d))`; the `evalPkappa_*`, `summable_skappa_eval_mul*`
(now `summable_coeffs_eval_mul*`), `toFun_ofPkappa`, `memLp_two_evalPkappa`, `continuous_evalPkappa`,
`integrable_evalPkappa_sq` lemma names follow their objects; no binder in `TensorBasis.lean` became
unused; the two `_exact_wip` lemmas without a level (`coeff_eq_zero_of_self_kernel_zero_exact_wip`,
`norm_eq_of_self_kernel_eq_exact_wip`) keep their names.  Decisions of the author (Section 5): remove the
phantom parameter only; rename the de-phantomed objects; declare the folder an independently
maintained fork and stop updating `PROVENANCE.md`; no intermediate build of the refactor alone —
it is carried out together with `PLAN-MixedLevel-ContinuousPR.md` (which is written for the
names below) and verified by the final `lake build Check`.

## 0. The problem

`ModulusRecovery/Definitions.lean` declares the coefficient types with a level parameter that
no field uses:

```lean
abbrev Pkappa (d : Nat) (kappa : MultiIndex d) := Finsupp (Idx d) ℂ      -- finitely supported
structure Skappa (d : Nat) (kappa : MultiIndex d) where                    -- square-summable
  coeff : Idx d -> ℂ
  summable_norm_sq : Summable (fun alpha : Idx d => ‖coeff alpha‖ ^ 2)
```

`Skappa d κ` and `Skappa d κ'` are different types with identical contents.  The same
happens for functions that take `kappa` only to type such an argument or ignore it outright:
`bKappa kappa U` (the real Hermite expansion of `U` in `L²(ℝ^d)`), `bKappaRep`, `TKappa _kappa`
(the linear map phase space → `ℂ^d`), `QKappa _kappa`, `WKappa kappa` (the Gaussian weight),
the `Zero`/`SMul` instances, `coeffSkappa`, `coeffPkappa`, `ofPkappa`, `truncateFinset`, and
every lemma about these.  The level is real only in the basis `Phi kappa ·` (hence `toFun`,
`toL2`, `evalPkappa`, `evalPkappaL2`, `PhiL2`, `partialSum`, …), in the window `varphiKappa`,
and in what is computed from them (`stftModelPhase`, `PKappa`, `stft_model_*`,
`windowAmbiguity_*`).

For the single-level proof this is harmless.  For the mixed-level proof it is misleading: a
coefficient family is expanded against `Ψ · h`, which has no level, yet its type would still
name one.  This plan deletes the parameter wherever it is phantom, so that after it every
`kappa` in the folder is a level that the statement actually uses.

Occurrence counts (whole folder): `Pkappa` 160, `coeffSkappa` 117, `Skappa` 81, `bKappa` 65,
`TKappa` 49, `WKappa` 26, `QKappa` 14.  Only four files mention them:
`ModulusRecovery/Definitions.lean`, `ModulusRecovery/TensorBasis.lean`,
`ModulusRecovery/ExactModulusRecovery.lean`, `ContinuousPR.lean`.  The `Hermite*/` and
`Hermitek/` folders and `ImportedAnalyticInputs.lean` are untouched.

## 1. The rule

For every declaration: **`kappa` stays exactly when the statement mentions the basis or the
window** (`Phi kappa`, `toFun kappa`, `toL2 kappa`, `evalPfin kappa`, `evalPkappaL2 kappa`,
`PhiL2 kappa`, `partialSum kappa`, `varphiKappa kappa`, `stftModelPhase kappa`, `PKappa kappa`,
or a hypothesis about these); **otherwise it is deleted**, from the type of the coefficient
arguments and from the parameter list.  The compiler enforces the rule: after the change to
`Definitions.lean`, every remaining phantom use is a type error or an unused-variable warning.

## 2. New names (`ModulusRecovery/Definitions.lean`)

| old | new | remark |
|---|---|---|
| `Pkappa d kappa` | `Pfin d` | `abbrev Pfin (d : Nat) := Finsupp (Idx d) ℂ` |
| `Skappa d kappa` | `Coeffs d` | same two fields |
| `coeffPkappa F α` | `coeffPfin F α` | |
| `coeffSkappa U α` | `coeffAt U α` | not `coeff`: the bridge files open both `ModulusRecovery` and `DiscretePR`, which has `DiscretePR.coeff` |
| `evalPkappa kappa F` | `evalPfin kappa F` | keeps `kappa` (basis) |
| `toFun kappa U`, `toL2 kappa U` | unchanged | keep `kappa` (basis) |
| `ofPkappa kappa F` | `ofPfin F` | |
| `truncateFinset E U` | unchanged name, type `Coeffs d → Pfin d` | |
| `instNormPkappa` | `instNormPfin` | |
| `Zero (Skappa d kappa)`, `SMul ℂ (Skappa d kappa)` | on `Coeffs d` | same bodies |

`ModulusRecovery/ExactModulusRecovery.lean`:

| old | new |
|---|---|
| `bKappa kappa U` | `hermiteExpansion U` |
| `bKappaRep kappa U` | `hermiteExpansionRep U` |
| `bKappa_smul`, `bKappa_injective`, `bKappa_injective_of_realHermite_orthonormal`, `bKappa_injective_of_realHermite_coeff_recovery`, `bKappa_coeff_recovery_of_realHermite_orthonormal`, `bKappaRep_isL2Rep`, `bKappa_zero_exact_wip`, `skappa_eq_zero_of_bKappa_eq_zero_exact_wip` | `hermiteExpansion_smul`, `hermiteExpansion_injective`, …, `hermiteExpansionRep_isL2Rep`, `hermiteExpansion_zero`, `coeffs_eq_zero_of_hermiteExpansion_eq_zero` |
| `TKappa kappa ξ` | `phaseToC ξ` |
| `QKappa kappa ξ`, `WKappa kappa ξ`, `WKappa_pos`, `TKappa_zero` | `gaussQuad ξ`, `gaussWeight ξ`, `gaussWeight_pos`, `phaseToC_zero` |
| `tKappaCoordPoly`, `tKappaConjCoordPoly`, `PhiTKappaMvPolynomial` | `phaseToCPoly`, `phaseToCConjPoly`, `PhiPhaseToCPoly` (these are polynomials in the phase-space coordinates; `PhiPhaseToCPoly κ α` keeps its two levels) |
| `skappa_ext_coeff_from_realHermite`, `skappa_ext_coeff_exact_wip`, `skappa_eq_zero_of_coeff_zero_exact_wip` | `Coeffs.ext_coeffAt` (one lemma; the two are duplicates), `coeffs_eq_zero_of_coeffAt_zero` |
| `lift_unimodular_phase_L2_to_Skappa`, `ambiguity_eq_to_skappa_phase` | `lift_unimodular_phase_L2_to_coeffs`, `ambiguity_eq_to_coeffs_phase` |
| `scalar_multiple_of_coeff_kernel_exact_wip`, `coeff_kernel_of_scalar_multiple_exact_wip` | drop `_exact_wip` |
| `exact_modulus_recovery_skappa(_ae)`, `skappa_eq_zero_of_toFun_zero_exact_wip` | `exact_modulus_recovery_coeffs(_ae)`, `coeffs_eq_zero_of_toFun_zero`; keep `kappa` (they are about `toFun kappa`) |

`ContinuousPR.lean`: `toSkappa κ F` ↦ `toCoeffs F`; `toFun_toSkappa` ↦ `toFun_toCoeffs`.
Names with a genuine level (`varphiKappa`, `PKappa`, `stftModelPhase`, `PhiL2`, `evalPkappaL2`)
keep their names.

## 3. `ModulusRecovery/TensorBasis.lean`

Every declaration keeps `kappa` (all are about `Phi kappa`, `evalPfin kappa`, `toFun kappa`,
`PhiL2 kappa`, `partialSum kappa`); the edit is the argument types only,
`(U : Skappa d kappa)` ↦ `(U : Coeffs d)`, `(F : Pkappa d kappa)` ↦ `(F : Pfin d)` (about 45
headers), the renamings of Section 2, and a few implicit `{kappa}` binders of `private` lemmas
that become unused (the linter lists them).

## 4. `ModulusRecovery/ExactModulusRecovery.lean` and `ContinuousPR.lean`

Declarations that **lose** `kappa` (phantom in all of them): the signal side (`hermiteExpansion`
and its lemmas), the phase-space geometry (`phaseToC`, `gaussQuad`, `gaussWeight` and their
lemmas, `phaseToCPoly_eval`, `phaseToCConjPoly_eval`), and the end of the chain
(`lift_unimodular_phase_L2_to_coeffs`, `ambiguity_eq_to_coeffs_phase`, `Coeffs.ext_coeffAt`,
`hermiteExpansion_zero`, `coeffs_eq_zero_of_hermiteExpansion_eq_zero`,
`coeffs_eq_zero_of_coeffAt_zero`, `scalar_multiple_of_coeff_kernel`,
`coeff_kernel_of_scalar_multiple`); in `ContinuousPR.lean`, `toCoeffs`.

Declarations that **keep** `kappa` (basis or window in the statement), with only argument types
and names changed: `varphiKappa`, `PKappa`, `PKappa_isPolynomial`, `PhiPhaseToCPoly(_eval)`,
`stftModelPhase(_norm)`, `stft_model_basis_formula`, `stft_model_global_phase(_of_basis_formula)`,
`stft_model_modulus(_of_global_phase_formula)`, `windowAmbiguity_factorization`,
`windowAmbiguity_dense_nonvanishing`, `spectrogram_eq_of_equal_modulus_to_ambiguity_eq`,
`ae_modulus_to_pointwise_modulus`, `ae_modulus_to_stft_modulus`, `ae_modulus_to_ambiguity_eq`,
`coeff_kernel_of_exact_modulus_recovery_coeffs_ae`, `exact_modulus_recovery_coeffs(_ae)`,
`toFun_zero`, `coeffs_eq_zero_of_toFun_zero`, and `DiscretePolyFock.exactModulusRecovery`
(about `polyanalyticEval κ` today; about `polyanalyticEval h` after the mixed-level work).

## 5. Decisions (author, 2026-09-17)

* **Scope:** the phantom parameter only; `Coeffs` stays a structure (no replacement by the
  comparator's `lp` space).
* **Names:** the de-phantomed objects are renamed as in Section 2.
* **Provenance:** `PROVENANCE.md` receives one closing note — "as of 2026-09-17 this folder is
  maintained independently of `DiscreteFock/PolyFockComplete`; the sections above describe its
  origin and the state at the fork" — and is not updated afterwards.  The `diff` recipe there
  stops being meaningful.
* **Ordering:** no intermediate build of the refactor alone.  It is executed together with
  `PLAN-MixedLevel-ContinuousPR.md`, and `lake build ContinuousPhaseRetrieval` / `lake build Check`
  at the end of that plan is the verification.

## 6. Mechanics

1. Edit `ModulusRecovery/Definitions.lean` (Section 2).
2. Script the pure renamings over the four files (`Skappa d kappa` ↦ `Coeffs d`,
   `Pkappa d kappa` ↦ `Pfin d`, `coeffSkappa` ↦ `coeffAt`, `bKappa kappa` ↦ `hermiteExpansion`,
   `TKappa kappa` ↦ `phaseToC`, `QKappa kappa` ↦ `gaussQuad`, `WKappa kappa` ↦ `gaussWeight`,
   the lemma names of Section 2); then build file by file (`TensorBasis`, `ExactModulusRecovery`,
   `ContinuousPR`) and remove, at each error or unused-variable warning, the `(kappa : MultiIndex d)`
   binder that has become unused together with the corresponding argument at its call sites.
3. The `MixedLevel.lean` file of the other plan is written against the new names from the start.
4. Verification at the end of the other plan: `lake build ContinuousPhaseRetrieval` clean (no
   `sorry`, no new warnings), `#print axioms DiscretePolyFock.exactModulusRecovery` unchanged
   (`propext`, `Classical.choice`, `Quot.sound`).
5. `PROVENANCE.md`: the closing note of Section 5.  `README.md`, row `ContinuousPhaseRetrieval/`:
   say that the folder is an independent fork and that its coefficient families `Coeffs d` carry
   no level.

No mathematics changes; no proof is rewritten beyond removing an argument.  Estimated touch:
about 120 declaration headers and 500 call sites, all mechanical.
