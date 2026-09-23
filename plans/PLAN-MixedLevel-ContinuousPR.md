# Plan: continuous phase retrieval for the mixed-level spaces `𝓕_h` (`ContinuousPhaseRetrieval/`)

**Status (2026-09-17): executed.**  `MixedLevel.lean` (461 lines) and the two bridges build; `DiscretePR.continuous_phase_retrieval` depends on `propext`, `Classical.choice`, `Quot.sound` only.  Deviations: the explicit-phase model formula is `stft_model_eq_of_basis_formula`/`stft_model_eq` in `ExactModulusRecovery.lean` (the existential lemma is now a one-line corollary); the window-generic spectrogram lemma is `spectrogram_eq_of_equal_modulus_to_ambiguity_eq_of_window`; `ambiguityRep_sum_sum` is proved from `ambiguityRep_eq_exp_mul_stftRep` and linearity of `stftRep` in both arguments (`stftRep_signal_*` added); `toFunH_eq_finsetSum` carries the division `h q / hnorm h`.  Original text follows.  Executed together with
`PLAN-RemovePhantomLevel.md` (whose names are used throughout: `Coeffs d`, `coeffAt`,
`hermiteExpansion`, `phaseToC`, `gaussQuad`, `gaussWeight`, `PhiPhaseToCPoly`,
`ambiguity_eq_to_coeffs_phase`, `toCoeffs`).  Companion plan for everything outside
`ContinuousPhaseRetrieval/`: `PLAN-MixedLevel-Main.md`.

## 0. Target

`Definitions.lean` and `Showcase.lean` now state the main theorem for the mixed-level spaces.
The new objects (namespace `DiscretePR`, all in `Definitions.lean`):

```lean
def Ψ (n : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) (z : Fin d → ℂ) : ℂ :=
  (((Real.sqrt (∑ q ∈ h.support, ‖h q‖ ^ 2)) : ℂ)⁻¹) * ∑ q ∈ h.support, h q * Φ n q z
def polyanalyticEval (h : (Fin d → ℕ) →₀ ℂ) (F : PolyFock d) (z : Fin d → ℂ) : ℂ :=
  ∑' n : Fin d → ℕ, coeff F n * Ψ n h z
def PolyFockSpace (h : (Fin d → ℕ) →₀ ℂ) : Set ((Fin d → ℂ) → ℂ) :=
  { f | MemLp f 2 γ ∧ Continuous f ∧ ∃ F : PolyFock d, f = polyanalyticEval h F }
```

The single-level space is the case `h = Finsupp.single q 1`, where `Ψ n h = Φ n q`
(`simp [Ψ]`).  This plan delivers the input the main theorem needs from this folder:

```lean
-- DiscretePhaseRetrieval/ContinuousPR.lean (replaces the level-κ version)
theorem continuous_phase_retrieval {d : ℕ} (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0)
    (F G : PolyFock d)
    (h : ∀ z, ‖polyanalyticEval h F z‖ = ‖polyanalyticEval h G z‖) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧ polyanalyticEval h F = θ • polyanalyticEval h G
```

proved from a new exported theorem of this folder,

```lean
-- ContinuousPhaseRetrieval/ContinuousPR.lean (replaces `exactModulusRecovery`)
theorem DiscretePolyFock.exactModulusRecovery {d : ℕ} (hd : 0 < d)
    (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0) {a b : DiscretePR.PolyFock d}
    (hmod : ∀ z, ‖DiscretePR.polyanalyticEval h a z‖ = ‖DiscretePR.polyanalyticEval h b z‖) :
    ∃ τ : ℂ, ‖τ‖ = 1 ∧ b = τ • a
```

The hypothesis `hg` is genuinely needed here (the window of Section 2 must be a nonzero
`L²` function); it is also a hypothesis of the comparator.

## 1. Why the existing proof carries over

`ModulusRecovery/ExactModulusRecovery.lean` proves `exact_modulus_recovery_coeffs` (level `κ`)
by the STFT/ambiguity argument.  Its anatomy, with the level-dependence of each part:

| step | declaration | depends on the level through |
|---|---|---|
| signal: coefficients `U : Coeffs d` ↦ `hermiteExpansion U = ∑' α, U_α • realHermiteTensorL2 α ∈ L²(ℝ^d)` | `hermiteExpansion`, `hermiteExpansion_injective`, `hermiteExpansion_smul` | nothing |
| window `φ_κ = varphiKappa κ` | `varphiKappa` | the window |
| STFT of `φ_α` against `φ_κ`: `stftRep (varphiKappa κ) (realHermiteTensorL2 α) ξ = stftModelPhase κ ξ * (W ξ * Phi κ α (T ξ))`, `stftModelPhase κ ξ = (-1)^{‖κ‖₁} exp(-π i ⟨x, ω⟩)`, `W = gaussWeight = exp(-gaussQuad)`, `T = phaseToC` | `stft_model_basis_formula` (private), `stftModelPhase` (private) | **already proved for arbitrary pairs `(α, κ)`** |
| STFT of the signal = phase · `W` · `toFun κ U ∘ T` | `stft_model_global_phase_of_basis_formula` (private), `stft_model_modulus` | the window and the basis, both at `κ` |
| ambiguity of the window = `PKappa κ · exp(-Q)`, `PKappa κ` a phase-space polynomial, nonzero at `0` | `windowAmbiguity_factorization`, `PKappa_isPolynomial`, `Phi_self_zero_ne` | the diagonal pair `(κ, κ)` |
| a phase-space polynomial nonzero somewhere is nonzero on a dense set | `dense_ne_zero_of_phaseSpace_polynomial` (private) | nothing |
| equal spectrograms + dense nonvanishing window ambiguity ⟹ equal signal ambiguities | `spectrogram_eq_of_equal_modulus_to_ambiguity_eq`, `spectrogram_ambiguity_identity`, `continuous_ambiguityRep` | only through the dense-nonvanishing input |
| equal ambiguities ⟹ global phase, lifted to `Coeffs` | `ambiguity_eq_to_coeffs_phase`, `rankOneRecoveryFromAmbiguity` | nothing |

So the whole Fourier-analytic core is window-free, and the two window computations exist for
arbitrary index pairs.  What is missing is a thin layer: a mixed window, linearity of the STFT in
the window, the mixed ambiguity function as polynomial × Gaussian with a nonzero witness, and
the top-level chain re-run.  Nothing in `ImportedAnalyticInputs.lean`, `TensorBasis.lean`,
`Hermite*/` or `Hermitek/` changes beyond the renamings of the other plan.

Identification used throughout: `ModulusRecovery.Phi κ α z = DiscretePR.Φ α κ z` is `rfl`
(the index order differs), so the new definitions below are written directly with
`DiscretePR.Ψ`.

## 2. The mixed window

New file `ContinuousPhaseRetrieval/ModulusRecovery/MixedLevel.lean`, importing
`ContinuousPhaseRetrieval.ModulusRecovery.ExactModulusRecovery` and `Definitions`; namespace
`ModulusRecovery`, `open DiscretePR (Ψ)`.

```lean
/-- `‖h‖ = (∑ |h_q|²)^{1/2}`, the normalisation of `Ψ`. -/
def hnorm (h : (Fin d → ℕ) →₀ ℂ) : ℝ := Real.sqrt (∑ q ∈ h.support, ‖h q‖ ^ 2)
theorem hnorm_pos (hnonzero : h ≠ 0) : 0 < hnorm h
  -- `Finsupp.support_nonempty_iff`, `Finset.sum_pos'`, `Real.sqrt_pos`

/-- The window coefficient of level `q`: the sign `(-1)^{|q|}` of `stftModelPhase q`
is absorbed here, and the STFT conjugates the window. -/
def weight (h : (Fin d → ℕ) →₀ ℂ) (q : Fin d → ℕ) : ℂ :=
  (-1 : ℂ) ^ (∑ i, q i) * star (h q) / (hnorm h : ℂ)
theorem star_weight_mul_sign (h) (q) :
    star (weight h q) * (-1 : ℂ) ^ (∑ i, q i) = h q / (hnorm h : ℂ)
theorem weight_ne_zero (hnonzero : h ≠ 0) (hq : q ∈ h.support) : weight h q ≠ 0

/-- The mixed window `w_h = ∑_q weight h q · φ_q ∈ L²(ℝ^d)`. -/
def windowH (h : (Fin d → ℕ) →₀ ℂ) : L2Real d :=
  ∑ q ∈ h.support, weight h q • varphiKappa q

/-- The mixed-level function of a coefficient family. -/
def toFunH (h : (Fin d → ℕ) →₀ ℂ) (U : Coeffs d) : Cd d → ℂ :=
  fun z => ∑' α, coeffAt U α * Ψ α h z
```

`toFunH h (toCoeffs F) z = DiscretePR.polyanalyticEval h F z` is `rfl` (same series, same
terms), so the bridge in Section 6 needs no identification lemma.

The exponent `∑ i, q i` is written as in `stftModelPhase` (`Finset.univ.sum fun q => kappa q`),
not with the scoped notation `‖·‖₁` of `DiscretePhaseRetrieval/Auxiliary.lean`, to keep this
folder's imports as they are.

## 3. Linearity in the window (new, `MixedLevel.lean`)

`stftRep h f ξ` and `ambiguityRep f h ξ` are `lpPairing`s of `f` (resp. a translate of `f`) with
`modulateL2 · (star (translateL2 · h))` (`stftRep_eq_lpPairing`, `ambiguityRep_eq_lpPairing`,
`ImportedAnalyticInputs.lean`).  `lpPairing` is a continuous bilinear map, `star` on `Lp` is
additive and conjugate-homogeneous, `translateL2 a = (DomAddAct.mk a +ᵥ ·)` is additive and
homogeneous (the `DistribMulAction`/`Module` instances of `Mathlib/MeasureTheory/Function/LpSpace/
DomAct/Basic.lean`; failing that, `Lp.ext` with `translateL2_coeFn`), and `modulateL2 ω` is
additive and homogeneous (`MemLp.toLp_add`, `MemLp.toLp_const_smul`, or `Lp.ext` with
`modulateL2_coeFn`).  Hence:

```lean
theorem stftRep_window_add (h₁ h₂ f : L2Real d) (ξ) :
    stftRep (h₁ + h₂) f ξ = stftRep h₁ f ξ + stftRep h₂ f ξ
theorem stftRep_window_smul (c : ℂ) (h f : L2Real d) (ξ) :
    stftRep (c • h) f ξ = star c * stftRep h f ξ
theorem stftRep_window_sum (s : Finset ι) (c : ι → ℂ) (h : ι → L2Real d) (f) (ξ) :
    stftRep (∑ i ∈ s, c i • h i) f ξ = ∑ i ∈ s, star (c i) * stftRep (h i) f ξ
theorem ambiguityRep_sum_sum (s : Finset ι) (c : ι → ℂ) (h : ι → L2Real d) (ξ) :
    ambiguityRep (∑ i ∈ s, c i • h i) (∑ j ∈ s, c j • h j) ξ
      = ∑ i ∈ s, ∑ j ∈ s, c i * star (c j) * ambiguityRep (h i) (h j) ξ
```

(`ambiguityRep` is linear in its first and conjugate-linear in its second argument.)
About 60 lines.

## 4. The STFT model for the mixed window

**4a. Generalise in place** the private `stft_model_global_phase_of_basis_formula`
(`ExactModulusRecovery.lean:6489`): its proof never uses that the window level equals the level
of the basis in the conclusion.  New statement (window level `q`, any `U : Coeffs d`):

```lean
theorem stft_model_eq (hd : 0 < d) (q : MultiIndex d) (U : Coeffs d) (ξ : PhaseSpace d) :
    stftRep (varphiKappa q) (hermiteExpansion U) ξ =
      stftModelPhase q ξ * (((gaussWeight ξ : ℝ) : ℂ) * toFun q U (phaseToC ξ))
```

Proof: the existing one verbatim with `hbasis := stft_model_basis_formula hd q` (its `hsummable`
is `summable_realHermiteTensorL2_coeff_smul_of_orthonormal …`, unchanged).  After the other plan
this is literally the old statement with `U` no longer typed by `q`, so `stft_model_global_phase`
and `stft_model_modulus` compile untouched.  Make `stftModelPhase`, `stftModelPhase_norm`,
`stft_model_basis_formula` public (remove `private`).

**4b. Mixed model** (`MixedLevel.lean`):

```lean
theorem stft_model_eq_mixed (hd : 0 < d) (h) (U : Coeffs d) (ξ) :
    stftRep (windowH h) (hermiteExpansion U) ξ =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
        (((gaussWeight ξ : ℝ) : ℂ) * toFunH h U (phaseToC ξ))
```

Proof: `stftRep_window_sum`, then `stft_model_eq hd q U ξ` for each `q ∈ h.support`,
`star_weight_mul_sign` (the signs `(-1)^{|q|}` of `stftModelPhase q` cancel against `weight`),
pull `exp(…) * W` out of the finite sum, and interchange the finite sum over `q` with the series
over `α` (`Summable.tsum_finsetSum`; summability of each `α ↦ coeffAt U α * Phi q α z` is
`summable_skappa_eval_mul q U z`, `TensorBasis.lean:278`, renamed with the other plan); finally
`tsum_mul_left` and `Finset.mul_sum` to recognise `Ψ α h (T ξ)` (unfold `Ψ`, `hnorm`, `toFun`).
About 50 lines.

```lean
theorem stft_model_modulus_mixed (hd) (h) (U) (ξ) :
    ‖stftRep (windowH h) (hermiteExpansion U) ξ‖ = gaussWeight ξ * ‖toFunH h U (phaseToC ξ)‖
```

as `stft_model_modulus_of_global_phase_formula` (norm of the exponential is `1`:
`Complex.norm_exp_ofReal_mul_I` after rewriting the exponent). About 15 lines.

## 5. The mixed window's ambiguity function

**5a. Ambiguity from the STFT** (`MixedLevel.lean`), by one translation of the integral
(`MeasureTheory.integral_add_right_eq_self` with the shift `(1/2 : ℝ) • ξ.1`, then
`inner_add_right`, `Complex.exp_add`):

```lean
theorem ambiguityRep_eq_exp_mul_stftRep (f h : L2Real d) (ξ) :
    ambiguityRep f h ξ =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) * stftRep h f ξ
```

About 25 lines.  (Alternative if the coercions fight: generalise the private
`oneDWindowAmbiguityFactor` to two indices, whose monomial kernel
`oneDWindowAmbiguityMonomialKernel k l` is already two-index; longer.)

**5b. Cross ambiguities of Hermite pairs.**  With 5a, `stft_model_basis_formula hd κ α ξ`
(`realHermiteTensorL2 α = varphiKappa α` is `rfl`) and the two exponentials cancelling:

```lean
theorem ambiguityRep_hermite (hd) (α κ : MultiIndex d) (ξ) :
    ambiguityRep (varphiKappa α) (varphiKappa κ) ξ =
      (-1 : ℂ) ^ (∑ i, κ i) * (((gaussWeight ξ : ℝ) : ℂ) * Phi κ α (phaseToC ξ))
```

(For `α = κ` this is `windowAmbiguity_factorization`, so it can double as a check.)  About 20
lines.

**5c. Factorisation.**

```lean
/-- The polynomial part of the mixed window's ambiguity function. -/
def PG (h : (Fin d → ℕ) →₀ ℂ) : PhaseSpace d → ℂ := fun ξ =>
  ∑ q ∈ h.support, ∑ q' ∈ h.support,
    weight h q * star (weight h q') * (-1 : ℂ) ^ (∑ i, q' i) * Phi q' q (phaseToC ξ)

theorem windowAmbiguity_factorization_mixed (hd) (h) (ξ) :
    ambiguityRep (windowH h) (windowH h) ξ = PH h ξ * Complex.ofReal (Real.exp (-(gaussQuad ξ)))
```

by `ambiguityRep_sum_sum` and `ambiguityRep_hermite`, `Finset.sum_mul`.  About 25 lines.

**5d. Polynomiality.**  Make `PhiPhaseToCPoly`, `PhiPhaseToCPoly_eval` public.

```lean
theorem PH_isPolynomial (hd) (h) : IsPhaseSpacePolynomial (PH h)
-- witness `∑ q ∈ h.support, ∑ q' ∈ h.support, MvPolynomial.C (…) * PhiPhaseToCPoly q' q`,
-- `MvPolynomial.eval_sum`, `eval_mul`, `eval_C`, `PhiPhaseToCPoly_eval`
```

About 20 lines.

**5e. The witness at the origin** (abstract route; see the estimate in the conversation of
2026-09-17).

```lean
theorem ambiguityRep_self_zero (w : L2Real d) : ambiguityRep w w (0, 0) = inner ℂ w w
-- unfold `ambiguityRep`; `zero_smul`, `add_zero`, `sub_zero`, `inner_zero_left`, `mul_zero`,
-- `Complex.exp_zero`, `mul_one`; then `MeasureTheory.L2.inner_def`, `integral_congr_ae`,
-- pointwise `inner (w t) (w t) = star (w t) * w t` (`RCLike.inner_apply`, `mul_comm`)

theorem windowH_ne_zero (hnonzero : h ≠ 0) : windowH h ≠ 0
-- `realHermiteTensorL2_orthonormal.linearIndependent`, `linearIndependent_iff'` on
-- `h.support` with coefficients `weight h`; `weight_ne_zero` at some `q ∈ h.support`

theorem PH_zero_ne (hd) (hnonzero : h ≠ 0) : PH h (0, 0) ≠ 0
-- `windowAmbiguity_factorization_mixed` at `(0,0)`; `gaussQuad (0,0) = 0` (`norm_zero`);
-- `ambiguityRep_self_zero`, `inner_self_eq_zero`, `windowH_ne_zero`
```

About 45 lines.

**5f. Dense nonvanishing.**  Make `dense_ne_zero_of_phaseSpace_polynomial` public.

```lean
theorem windowAmbiguity_dense_nonvanishing_mixed (hd) (hnonzero : h ≠ 0) :
    Dense {ξ : PhaseSpace d | ambiguityRep (windowH h) (windowH h) ξ ≠ 0}
```

Copy of `windowAmbiguity_dense_nonvanishing` with 5c–5e.  About 12 lines.

## 6. The chain

**6a. Generalise in place** `spectrogram_eq_of_equal_modulus_to_ambiguity_eq`
(`ExactModulusRecovery.lean:7927`) to an arbitrary window: replace `(kappa)` by
`(hwin : L2Real d) (hdense : Dense {ξ | ambiguityRep hwin hwin ξ ≠ 0})`; its proof already works
with a local `hwin` and uses the level only for `hs_dense`.  Keep the level version as the
instance `hwin := varphiKappa kappa`, `hdense := windowAmbiguity_dense_nonvanishing hd kappa`.

**6b.** (`MixedLevel.lean`)

```lean
theorem exact_modulus_recovery_mixed (hd : 0 < d) (h) (hnonzero : h ≠ 0) {U V : Coeffs d}
    (hmod : ∀ z, ‖toFunH h U z‖ = ‖toFunH h V z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  -- equal STFT moduli: `stft_model_modulus_mixed` twice and `hmod (phaseToC ξ)`
  -- equal ambiguities: `spectrogram_eq_of_equal_modulus_to_ambiguity_eq` (6a) with
  --   `windowAmbiguity_dense_nonvanishing_mixed hd hnonzero`
  -- the phase: `ambiguity_eq_to_coeffs_phase hd`
```

About 20 lines.  Note what is **not** needed: neither continuity of `toFunH` nor the zero-case
split of `exact_modulus_recovery_coeffs_ae` (the hypothesis is already pointwise, and
`ambiguity_eq_to_coeffs_phase` handles `U = 0` internally through `hermiteExpansion`), nor any
`L²(γ)` orthogonality of the `Φ_{n,q}` across levels, which the development does not have.

**6c. Bridge.**  `ContinuousPhaseRetrieval/ContinuousPR.lean`: keep `toCoeffs`, restate
`exactModulusRecovery` as in Section 0, `toFun_toCoeffs` becomes
`toFunH h (toCoeffs F) z = DiscretePR.polyanalyticEval h F z := rfl`.
`DiscretePhaseRetrieval/ContinuousPR.lean`: `continuous_phase_retrieval hd h hnonzero F G h`, same
proof (the coefficient identity is transported through `polyanalyticEval h`, `tsum_mul_left`).

## 7. Bookkeeping

* `PROVENANCE.md` is not updated (decision of 2026-09-17: the folder is an independently
  maintained fork; the closing note is added by `PLAN-RemovePhantomLevel.md`).
* `README.md` (root table row `ContinuousPhaseRetrieval/`, "the main theorem" list) and
  `DiscretePhaseRetrieval/CLAIMS.md` row CPR: cite `exact_modulus_recovery_mixed`.
* `Check.lean`: `#print axioms DiscretePR.continuous_phase_retrieval` stays; add
  `example (n q) (z) : DiscretePR.Ψ n (Finsupp.single q 1) z = DiscretePR.Φ n q z := by simp [DiscretePR.Ψ]`.
* Expected axioms unchanged: `propext`, `Classical.choice`, `Quot.sound`.

## 8. Order of work and size

| step | new lines (est.) | blocks |
|---|---|---|
| 0 `PLAN-RemovePhantomLevel.md` (renamings, dropped parameters) | 0 new, ~600 edited | — |
| 2 definitions, `hnorm_pos`, `weight_ne_zero` | 30 | — |
| 3 linearity in the window | 60 | — |
| 4a in-place generalisation, de-privatise | 10 | 0 |
| 4b–4c mixed model and modulus | 65 | 2, 3, 4a |
| 5a ambiguity from STFT | 25 | — |
| 5b–5d cross ambiguities, factorisation, polynomiality | 65 | 3, 4a, 5a |
| 5e–5f witness, density | 57 | 5c, 5d |
| 6a in-place generalisation | 5 | 0 |
| 6b chain, 6c bridges | 50 | all |

About 370 new lines in total.  Steps 2–3, 5a are independent of step 0 and of each other; the
whole folder is built once at the end (`lake build ContinuousPhaseRetrieval`, then `Check`
together with `PLAN-MixedLevel-Main.md`).
