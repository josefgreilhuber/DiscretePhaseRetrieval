# Plan: the Hermite functions are an orthonormal basis of `L²(ℝ^d)`

**Status (2026-09-17): executed.**  `ContinuousPhaseRetrieval/ModulusRecovery/HermiteBasis.lean` (581 lines) builds; `hermiteExpansion_surjective`, `hermiteExpansion_hermiteCoeffs`, `realHermiteTensorL2_span_dense`, `hermiteHilbertBasis` depend on the three standard axioms.  Deviations: L2 by AM–GM against `Real.summable_pow_div_factorial` instead of the ratio test; L3's product identity by a cofinality/limit-uniqueness argument (`tendsto_piFinset_range_atTop`) instead of induction on `d`; one extra lemma `summable_norm_realHermiteGenerating_term` (absolute convergence of the one-dimensional Taylor series, by the doubling trick); L5's majorant by AM–GM with `integral_norm_sq_realHermiteTensorRep`; L7 and L8 merged into `eq_zero_of_inner_realHermiteTensorL2_eq_zero`; bonus `hermiteExpansion_bijective`.  Original text follows.  Needed by the STFT corollary `STFT.lean`
(every `f ∈ L²(ℝ^d)` must be a Hermite expansion).  One new file,
`ContinuousPhaseRetrieval/ModulusRecovery/HermiteBasis.lean`, importing
`ContinuousPhaseRetrieval.ModulusRecovery.ExactModulusRecovery`; namespace `ModulusRecovery`.

## 0. Target

The development already has the orthonormal family and its expansion map
(`ExactModulusRecovery.lean`):

```lean
def realHermite1D (n : ℕ) (t : ℝ) : ℂ                       -- ψ_n = (2ⁿ n! √π)^{-1/2} H_n(t) e^{-t²/2}
def realHermiteTensorRep (α : Idx d) : RealVec d → ℂ         -- ψ_α(t) = ∏ᵢ ψ_{αᵢ}(tᵢ)
def realHermiteTensorL2 (α : Idx d) : L2Real d               -- its class in L²(ℝ^d)
theorem realHermiteTensorL2_orthonormal : Orthonormal ℂ (realHermiteTensorL2 (d := d))
def hermiteExpansion (U : Coeffs d) : L2Real d := ∑' α, coeffAt U α • realHermiteTensorL2 α
theorem hermiteExpansion_injective : Function.Injective (hermiteExpansion (d := d))
```

To prove, in the new file:

```lean
/-- The Hermite functions span a dense subspace of `L²(ℝ^d)`. -/
theorem realHermiteTensorL2_span_dense (d : ℕ) :
    (Submodule.span ℂ (Set.range (realHermiteTensorL2 (d := d)))).topologicalClosure = ⊤

/-- The Hermite functions as a Hilbert basis of `L²(ℝ^d)`. -/
def hermiteHilbertBasis (d : ℕ) : HilbertBasis (Idx d) ℂ (L2Real d) :=
  HilbertBasis.mk realHermiteTensorL2_orthonormal (by rw [realHermiteTensorL2_span_dense])
theorem hermiteHilbertBasis_apply (α : Idx d) : hermiteHilbertBasis d α = realHermiteTensorL2 α

/-- The Hermite coefficients of `f`, as a square-summable family. -/
def hermiteCoeffs (f : L2Real d) : Coeffs d
theorem coeffAt_hermiteCoeffs (f : L2Real d) (α) :
    coeffAt (hermiteCoeffs f) α = inner ℂ (realHermiteTensorL2 α) f
theorem hermiteExpansion_hermiteCoeffs (f : L2Real d) : hermiteExpansion (hermiteCoeffs f) = f
theorem hermiteExpansion_surjective : Function.Surjective (hermiteExpansion (d := d))
```

## 1. Why not Stone–Weierstrass

Mathlib has both ingredients you asked about: Stone–Weierstrass
(`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`,
`polynomialFunctions_closure_eq_top`, `Mathlib/Topology/ContinuousMap/{StoneWeierstrass,Weierstrass}.lean`)
and density of continuous functions in `Lp` (`BoundedContinuousFunction.toLp_denseRange`,
`MeasureTheory.Memℒp.exists_hasCompactSupport_eLpNorm_sub_le`,
`Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`).  But they do not give completeness of
the Hermite functions by themselves: Weierstrass approximates a compactly supported `g` by a
polynomial `p` uniformly on a ball `B`, and `p(x) e^{-|x|²/2}` then approximates `g` on `B`, but
nothing controls `p(x) e^{-|x|²/2}` outside `B`, where the polynomial is huge.  Every textbook
proof closes this gap with a Fourier or analyticity argument, at which point Stone–Weierstrass is
no longer needed.  The elementary proof below uses only the generating function of the Hermite
functions (already in the development), one interchange of sum and integral, and the injectivity
of the Fourier transform on `L¹ ∩ L²` (already in the development).  Density of `C_c` is not used.

## 2. The proof

Let `G(t, u) = π^{-1/4} exp(−t²/2 + √2 t u − u²/2)` (`realHermiteGenerating t u`).  By definition
`ψ_n(t) = (√n!/n!) ∂ᵤⁿ G(t, 0)`, so the Taylor series of the entire function `u ↦ G(t, u)` reads

```
G(t, u) = ∑_n ψ_n(t) uⁿ / √n!            (pointwise, absolutely convergent).      (1)
```

For `t, u ∈ ℂ^d` put `G_d(t, u) = ∏ᵢ G(tᵢ, uᵢ) = ∑_α ψ_α(t) u^α / √α!` (product of `d` absolutely
convergent series).  For `f ∈ L²(ℝ^d)`, Cauchy–Schwarz gives `∫ |f ψ_α| ≤ ‖f‖₂ ‖ψ_α‖₂ = ‖f‖₂`, and
`∑_α |u^α|/√α! = ∏ᵢ ∑_n |uᵢ|ⁿ/√n! < ∞`, so sum and integral may be interchanged:

```
∫ conj(f(t)) G_d(t, u) dt = ∑_α ⟪ψ_α, f⟫ u^α / √α!.                                   (2)
```

Now let `f ⟂ ψ_α` for all `α`.  Then (2) vanishes for every `u`.  Take `u = i ξ/√2` with `ξ ∈ ℝ^d`:
`−u²/2 = ξ²/4` and `√2 t u = i t ξ`, so

```
G_d(t, iξ/√2) = π^{-d/4} e^{|ξ|²/4} e^{-|t|²/2} e^{i⟨t, ξ⟩},                             (3)
```

hence `∫ conj(f(t)) e^{-|t|²/2} e^{i⟨t,ξ⟩} dt = 0` for all `ξ`, i.e. the Fourier transform of
`g := conj(f) e^{-|t|²/2}` vanishes identically (at `w = −ξ/(2π)` in Mathlib's normalisation
`𝓕 g w = ∫ e^{−2πi⟨t,w⟩} g(t) dt`).  `g ∈ L¹ ∩ L²` (product of two `L²` functions; bounded times
`L²`), so `g = 0` a.e. by Fourier injectivity, and since the Gaussian never vanishes, `f = 0` a.e.
So the orthogonal complement of the span is trivial, the span is dense, and
`HilbertBasis.mk` turns the orthonormal family into a Hilbert basis; its expansion
`f = ∑_α ⟪ψ_α, f⟫ ψ_α` is `hermiteExpansion` of the coefficient family `α ↦ ⟪ψ_α, f⟫`.

## 3. Lemmas (in order), with the Mathlib and project inputs

| # | statement | inputs | lines |
|---|---|---|---|
| L1 | `realHermiteGenerating_eq_tsum (t : ℝ) (u : ℂ) : realHermiteGenerating t u = ∑' n, (u ^ n / (Real.sqrt n.factorial : ℂ)) * realHermite1D n t` and its `HasSum` form | `hasSum_taylorSeries_of_entire` / `taylorSeries_eq_of_entire'` (`Mathlib/Analysis/Complex/TaylorSeries.lean`, series `∑ (n!)⁻¹ * iteratedDeriv n f 0 * u^n`); `u ↦ G t u` is entire (`Differentiable.cexp` of a polynomial); unfold `realHermite1D` and cancel `(n!)⁻¹ · (n!/√n!) = 1/√n!` | 30 |
| L2 | `summable_pow_div_sqrt_factorial (r : ℝ) : Summable (fun n => r ^ n / Real.sqrt n.factorial)` (for `0 ≤ r`), and the complex-norm version | ratio test `summable_of_ratio_test_tendsto_lt_one` (ratio `r/√(n+1) → 0`) | 25 |
| L3 | products of series over `Fin d → ℕ`: `summable_pi_prod (h0 : ∀ i n, 0 ≤ g i n) (hs : ∀ i, Summable (g i)) : Summable (fun α : Fin d → ℕ => ∏ i, g i (α i))`, `tsum_pi_prod : ∑' α, ∏ i, g i (α i) = ∏ i, ∑' n, g i n`, and the complex version under summable norms | induction on `d` with `Equiv.piFinSucc`, `Summable.mul_of_nonneg`, `tsum_mul_tsum_of_summable_norm`, `summable_mul_of_summable_norm`; the same argument exists in the project as `DiscretePR.tsum_prod_le` (`DiscretePhaseRetrieval/KernelBound.lean`, private) and `phiMajorant_multi_sq_summable` (`TensorBasis.lean`), which may be copied but not imported (layering) | 60 |
| L4 | `tensorGenerating (t : RealVec d) (u : Fin d → ℂ) : ℂ := ∏ i, realHermiteGenerating (t i) (u i)` and `tensorGenerating_eq_tsum : tensorGenerating t u = ∑' α, (∏ i, u i ^ α i / Real.sqrt (α i).factorial) * realHermiteTensorRep α t` | L1, L3, `realHermiteTensorRep` unfolds to `∏ i, realHermite1D (α i) (t i)`, `Finset.prod_mul_distrib` | 30 |
| L5 | `integral_conj_mul_tensorGenerating (f : L2Real d) (u) : ∫ t, star (f t) * tensorGenerating t u = ∑' α, (∏ i, u i ^ α i / Real.sqrt (α i).factorial) * inner ℂ (realHermiteTensorL2 α) f` | `integral_tsum_of_summable_integral_norm` (`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`); the bound `∫ ‖f ψ_α‖ ≤ ‖f‖ · 1` by Cauchy–Schwarz (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` or `norm_inner_le_norm` after L2 identification); the inner product as an integral: `realHermiteTensorL2_inner_eq_integral_of_memLp`, `varphiKappa_coe_ae_eq_realHermiteTensorRep` (a.e. identification of the `Lp` class with `realHermiteTensorRep`); L2, L3 for the summable majorant `‖f‖ ∏ᵢ ∑ₙ ‖uᵢ‖ⁿ/√n!` | 70 |
| L6 | `tensorGenerating_imaginary (t : RealVec d) (ξ : RealVec d) : tensorGenerating t (fun i => Complex.I * ξ i / Real.sqrt 2) = ((Real.pi ^ (-(d : ℝ)/4) * Real.exp (‖ξ‖ ^ 2 / 4) : ℝ) : ℂ) * Real.exp (-‖t‖ ^ 2 / 2) * Complex.exp (Complex.I * (inner ℝ t ξ : ℝ))` (constant nonzero) | unfold `realHermiteGenerating`; `Finset.prod_mul_distrib`, `Complex.exp_sum`, `EuclideanSpace.norm_eq`, `PiLp.inner_apply`/`real_inner_eq_re_inner`; algebra in the exponent | 35 |
| L7 | `fourierIntegral_conj_mul_gaussian_eq_zero (f : L2Real d) (hf : ∀ α, inner ℂ (realHermiteTensorL2 α) f = 0) : ∀ w, 𝓕 (fun t => star (f t) * Real.exp (-‖t‖ ^ 2 / 2)) w = 0` | L5 at `u = iξ/√2` (all terms vanish), L6 to read off the integral, then `ξ := −2π w`; `Real.fourierIntegral_real_eq`/`VectorFourier.fourierIntegral` unfolded with `Real.fourierChar_apply` (`𝐞 x = exp(2πi x)`); `integral_const_mul`, the nonzero constant cancelled | 45 |
| L8 | `eq_zero_of_inner_realHermiteTensorL2_eq_zero (f : L2Real d) (hf : ∀ α, inner ℂ (realHermiteTensorL2 α) f = 0) : f = 0` | L7; **de-privatise** `fourier_l1_l2_eq_zero_ae` (`ExactModulusRecovery.lean:8026`: `Integrable h → MemLp h 2 volume → (∀ ξ, 𝓕 h ξ = 0) → h =ᵐ 0`); integrability of `star f · Gaussian`: `MemLp.integrable_mul` from `Lp.memLp f` and `MemLp` of the Gaussian (`integrable_cexp_neg_mul_sq_norm_add` / `memLp_two_iff_integrable_sq`); `MemLp 2` of the product: bounded × `L²` (`MemLp.mul` with the `L^∞` Gaussian, or `MemLp.of_le`); conclude `f =ᵐ 0` since `Real.exp _ ≠ 0`, then `Lp.eq_zero_iff_ae_eq_zero` | 45 |
| L9 | `realHermiteTensorL2_span_dense` | `Submodule.topologicalClosure_eq_top_iff` (`Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`: closure `= ⊤ ↔ Kᗮ = ⊥`), `Submodule.eq_bot_iff`, membership in the orthogonal of a span via the generators (`Submodule.mem_orthogonal`, `Submodule.span_induction` or `Submodule.inner_right_of_mem_orthogonal` with `Submodule.subset_span`), L8 | 25 |
| L10 | `hermiteHilbertBasis`, `hermiteHilbertBasis_apply`, `hermiteCoeffs`, `coeffAt_hermiteCoeffs`, `hermiteExpansion_hermiteCoeffs`, `hermiteExpansion_surjective` | `HilbertBasis.mk`, `HilbertBasis.coe_mk`, `HilbertBasis.repr_apply_apply` (`b.repr f α = ⟪b α, f⟫`), `HilbertBasis.hasSum_repr` (`HasSum (fun α => b.repr f α • b α) f`); square-summability of the coefficients from `lp.memℓp (b.repr f)` with the `p = 2` conversion `rpow 2 = pow 2` exactly as in `DiscretePolyFock.toCoeffs` (`ContinuousPhaseRetrieval/ContinuousPR.lean`); `hermiteExpansion` unfolds to the same `tsum`, `HasSum.tsum_eq` | 45 |

About 410 lines.  Steps L1–L4 and L6 are independent of each other; L5 needs L2–L4; L7 needs
L5, L6; L8 needs L7; L9, L10 follow.

## 4. Remarks for the executor

* Index conventions: `Idx d = Fin d → ℕ`; `RealVec d = EuclideanSpace ℝ (Fin d)`, coordinates
  `t i`; `L2Real d = Lp ℂ 2 volume`; coercion `(f : RealVec d → ℂ)` of an `Lp` element is defined
  only a.e., so every pointwise identity about `f` is stated `=ᵐ[volume]` or under an integral.
* `realHermiteTensorL2 α` is `varphiKappa α` by definition (`rfl`); the a.e. description of its
  coercion is `varphiKappa_coe_ae_eq_realHermiteTensorRep`.
* Mathlib's `𝓕` on `RealVec d` is `Real.fourierIntegral` with kernel `e^{−2πi⟨t,w⟩}`; the
  development's private `fourier_l1_l2_eq_zero_ae` is stated for exactly this `𝓕` on a finite-
  dimensional real inner product space, so it applies to `RealVec d` directly.
* Only `ExactModulusRecovery.lean` is touched besides the new file, and only to remove one
  `private`.  No statement of the development changes.
* Verification: `lake build ContinuousPhaseRetrieval.ModulusRecovery.HermiteBasis` with no
  `sorry`; `#print axioms ModulusRecovery.hermiteExpansion_surjective` gives the three standard
  axioms.  Update `README.md` (row `ContinuousPhaseRetrieval/`) and the "proof status" paragraph of
  `STFT.lean` (Hermite completeness is then available; the Hermite expansion of the window
  `h(x) e^{−|x|²/2}` remains the other missing input of the corollary).

## 5. Decisions taken in this plan

* **Route:** generating function + Fourier injectivity, not Stone–Weierstrass (Section 1).
* **Form of the result:** both the `HilbertBasis` and the explicit inverse `hermiteCoeffs` of
  `hermiteExpansion`; the corollary `STFT.lean` will use the latter.
* **Dependency direction:** the new file sits after `ExactModulusRecovery.lean` because the Hermite
  family and the Fourier lemma live there; the product-of-series lemma L3 is re-proved locally
  rather than imported from `DiscretePhaseRetrieval/` to keep the layering acyclic and clean.
