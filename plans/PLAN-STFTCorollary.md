# Plan: proving the STFT corollary `STFTDiscretePhaseRetrieval` (`STFT.lean`)

**Status (2026-09-17): executed.**  Sections 2–4 in `ContinuousPhaseRetrieval/ModulusRecovery/WindowExpansion.lean` (496 lines), Section 5 in `STFT.lean` (about 90 lines); `STFTDiscretePhaseRetrieval` depends on the three standard axioms (`Check.lean`).  Deviations: `phaseToCInv` uses `WithLp.toLp 2`; `phaseToC_injective` is derived from `phaseDist_eq`; the `d`-dimensional expansion goes through a private submodule `hermiteSpan d` and `Finsupp.mem_span_range_iff_exists_finsupp`; `gaussWindow_ne_zero` takes `h` implicit; extra helpers `gamma_eq_DiscretePR_gamma` (`rfl`), `signedConj_apply`, `ofCoeffs_apply`.  Original text follows.  Depends on `PLAN-HermiteCompleteness.md`
(the file `HermiteBasis.lean`).  Two further files carry the rest; `STFT.lean` then assembles.

## 0. Statement (in `STFT.lean`, vocabulary of `Definitions.lean`)

```lean
theorem STFTDiscretePhaseRetrieval (d : ℕ) (hd : 0 < d) (h : MvPolynomial (Fin d) ℝ)
    (hnonzero : h ≠ 0) :
    ∃ S : Set (RealVec d × RealVec d),
      UniformlyDiscretePhase (4 * Real.sqrt d / 10 ^ 7) S ∧
        ∀ f g : L2Real d,
          (∀ x ξ, (x, ξ) ∈ S → ‖stft (gaussWindow h) f x ξ‖ = ‖stft (gaussWindow h) g x ξ‖) →
            ∃ θ : ℂ, ‖θ‖ = 1 ∧ f = θ • g
```

`DiscretePR.stft w f x ξ = ModulusRecovery.stftRep w f (x, ξ)`, `DiscretePR.RealVec = ModulusRecovery.RealVec`,
`DiscretePR.L2Real = ModulusRecovery.L2Real` are all `rfl` (identical bodies).

## 1. The proof, mathematically

Write `w = gaussWindow h = h(x) e^{−|x|²/2}`, `T(x, ξ) = (x − 2πi ξ)/√2` (`phaseToC`), `ψ_α` for
the Hermite functions (`realHermiteTensorL2 α`).

1. **Finite Hermite expansion of the window.**  `w = ∑_{α} c_α ψ_α` for a finitely supported
   `c ≠ 0` (Section 3).  Put `h' := (α ↦ (−1)^{|α|} conj(c_α))`, a finitely supported family with
   `h' ≠ 0`.  Then the mixed window of `MixedLevel.lean` is `windowH h' = ∑_α weight h' α • ψ_α`
   with `weight h' α = (−1)^{|α|} conj(h'_α)/‖h'‖ = c_α/‖c‖`, i.e. `windowH h' = ‖c‖⁻¹ • w`.
2. **The sampling set.**  Apply `DiscretePhaseRetrieval_proved d hd h' _` to get `S_ℂ ⊆ ℂ^d`,
   `UniformlyDiscrete δ S_ℂ`, `PhaseRetrievalSet (PolyFockSpace h') S_ℂ`, `δ = 4√d/10⁷`.  Put
   `S := {(x, ξ) | T(x, ξ) ∈ S_ℂ}`.  `T` is a bijection and `phaseDist x ξ x' ξ' = euclideanDist (T(x,ξ)) (T(x',ξ'))`,
   so `UniformlyDiscretePhase δ S`.
3. **Phase retrieval.**  Let `f, g ∈ L²` with equal STFT moduli on `S`.  By completeness
   `f = hermiteExpansion U`, `g = hermiteExpansion V` (`U := hermiteCoeffs f`, …).  Scaling the
   window by `‖c‖⁻¹ > 0` does not change the equality of moduli (`stftRep_window_smul`), so by
   `stft_model_modulus_mixed`, `gaussWeight (x,ξ) · ‖toFunH h' U (T(x,ξ))‖ = gaussWeight (x,ξ) · ‖toFunH h' V (T(x,ξ))‖`
   on `S`, i.e. `‖toFunH h' U z‖ = ‖toFunH h' V z‖` for all `z ∈ S_ℂ` (every `z` is `T(x,ξ)` with
   `(x,ξ) ∈ S`).  The functions `toFunH h' U = polyanalyticEval h' (ofCoeffs U)` lie in
   `PolyFockSpace h'` (Section 4), so the main theorem gives `θ` with
   `toFunH h' U = θ • toFunH h' V` on all of `ℂ^d`; in particular the moduli agree everywhere,
   and `exact_modulus_recovery_mixed hd h' _` gives `V = θ' • U`, whence
   `g = hermiteExpansion V = θ' • hermiteExpansion U = θ' • f` (`hermiteExpansion_smul`).
   (Using `exact_modulus_recovery_mixed` for the last step avoids needing injectivity of
   `toFunH`, which the development does not have.)

## 2. `ModulusRecovery/WindowExpansion.lean` — phase-space geometry (new file, imports `MixedLevel`, `Definitions`)

```lean
theorem phaseToC_injective : Function.Injective (phaseToC (d := d))
-- real and imaginary parts: `x i = √2 Re (phaseToC (x,ξ) i)`, `ξ i = −√2 Im (…)/(2π)`
def phaseToCInv (z : Cd d) : RealVec d × RealVec d      -- the inverse, coordinatewise
theorem phaseToC_phaseToCInv (z) : phaseToC (phaseToCInv z) = z
theorem phaseDist_eq (x ξ x' ξ' : RealVec d) :
    DiscretePR.phaseDist x ξ x' ξ' = DiscretePR.euclideanDist (phaseToC (x, ξ)) (phaseToC (x', ξ'))
-- `euclideanDist`, `phaseDist` unfold to square roots of sums; `EuclideanSpace.norm_eq`,
-- `Complex.sq_norm`/`Complex.normSq_apply` on `((a − 2πi b)/√2)`; `Finset.sum_add_distrib`, `Finset.mul_sum`
```

About 70 lines.

## 3. `ModulusRecovery/WindowExpansion.lean` — the window as a finite Hermite combination

One-dimensional triangularity.  The development has
`realHermiteGenerating_iteratedDeriv_zero_expansion_monomial` (`ExactModulusRecovery.lean:2574`) and
`realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff` (`:2173`):
`∂ᵤⁿ G(t, 0) = ∑_{k ≤ n} c_{n,k} tᵏ e^{−t²/2}` with `c_{n,k} = π^{−1/4} (√2)^k · (Polynomial.hermite n).coeff k`,
so with `realHermite1D n t = (√n!/n!) ∂ᵤⁿ G(t,0)` and Mathlib's `Polynomial.coeff_hermite_self`
(`= 1`), `coeff_hermite_of_lt` (`= 0` for `k > n`):
`ψ_n(t) = a_n tⁿ e^{−t²/2} + ∑_{k<n} (…) tᵏ e^{−t²/2}`, `a_n = (√n!/n!) π^{−1/4} (√2)ⁿ ≠ 0`.

```lean
/-- `tⁿ e^{−t²/2}` is a finite combination of `ψ_0, …, ψ_n` (pointwise, as functions `ℝ → ℂ`). -/
theorem monomialGaussian_mem_span (n : ℕ) :
    ∃ c : Fin (n + 1) → ℂ, ∀ t : ℝ,
      (t : ℂ) ^ n * Complex.exp (-(t : ℂ) ^ 2 / 2) = ∑ k, c k * realHermite1D k t
-- strong induction on `n`: solve the leading term
```

About 60 lines.  Tensor and polynomial:

```lean
/-- `x^β e^{−|x|²/2}` on `ℝ^d` as a finite combination of the `ψ_α`, `α ≤ β`. -/
theorem monomialGaussian_tensor_mem_span (β : Fin d → ℕ) :
    ∃ c : (Fin d → ℕ) →₀ ℂ, ∀ x : RealVec d,
      (∏ i, (x i : ℂ) ^ β i) * Real.exp (-‖x‖ ^ 2 / 2) = ∑ α ∈ c.support, c α * realHermiteTensorRep α x
-- `Finset.prod_univ_sum` (product of sums = sum over `Fintype.piFinset`), `EuclideanSpace.norm_eq`,
-- `Complex.exp_sum`/`Real.exp_sum` to split the Gaussian, `realHermiteTensorRep` unfolds to the product

/-- The window `h(x) e^{−|x|²/2}` as a finite combination of the `ψ_α`, first pointwise
(`MvPolynomial.eval` as a finite sum of monomials, `MvPolynomial.as_sum`/`eval_eq`), then in `L²`. -/
theorem gaussWindow_eq_sum (h : MvPolynomial (Fin d) ℝ) :
    ∃ c : (Fin d → ℕ) →₀ ℂ,
      (∀ x, ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * Real.exp (-‖x‖ ^ 2 / 2)
          = ∑ α ∈ c.support, c α * realHermiteTensorRep α x) ∧
      DiscretePR.gaussWindow h = ∑ α ∈ c.support, c α • realHermiteTensorL2 α
-- the pointwise identity gives `MemLp` of the window function (a.e. equal to a finite sum of
-- `MemLp` functions: `realHermiteTensorRep_memLp_of_realHermite1D_memLp`, `memLp_finset_sum`), so the
-- `if` in `gaussWindow` takes its `MemLp` branch (`dif_pos`); then `Lp.ext`/`MemLp.toLp_eq_toLp_iff`
-- with `Lp.coeFn_sum`, `Lp.coeFn_smul`, `varphiKappa_coe_ae_eq_realHermiteTensorRep`

theorem gaussWindow_ne_zero (hnonzero : h ≠ 0) : DiscretePR.gaussWindow h ≠ 0
-- a nonzero real polynomial is nonzero at some point (`MvPolynomial.funext` fails for `h ≠ 0`, or
-- `MvPolynomial.eq_zero_of_eval_zero`-type lemma over the infinite field `ℝ`); the window function is
-- continuous and nonzero there, hence not a.e. zero for Lebesgue measure
-- (`Continuous.ae_eq_iff_eq` with `IsOpenPosMeasure`); `Lp.eq_zero_iff_ae_eq_zero`
```

About 130 lines.  Then the signed family and the mixed window:

```lean
/-- The level weights of a coefficient family: `h'_α = (−1)^{|α|} conj(c_α)`. -/
def signedConj (c : (Fin d → ℕ) →₀ ℂ) : (Fin d → ℕ) →₀ ℂ :=
  Finsupp.onFinset c.support (fun α => (-1 : ℂ) ^ (∑ i, α i) * star (c α)) (by …)
theorem signedConj_support (c) : (signedConj c).support = c.support
theorem signedConj_ne_zero (hc : c ≠ 0) : signedConj c ≠ 0
theorem hnorm_signedConj (c) : hnorm (signedConj c) = hnorm c        -- `norm_star`, `norm_pow`, `norm_neg`
theorem weight_signedConj (c) (α) : weight (signedConj c) α = c α / (hnorm c : ℂ)   -- `star_weight_mul_sign`-style algebra
theorem windowH_signedConj (c) : windowH (signedConj c) = ((hnorm c : ℝ)⁻¹ : ℂ) • ∑ α ∈ c.support, c α • realHermiteTensorL2 α
```

About 50 lines.

## 4. `ModulusRecovery/WindowExpansion.lean` — the mixed-level functions lie in `PolyFockSpace`

```lean
/-- A coefficient family as an element of the comparator's `ℓ²` (inverse of `toCoeffs`). -/
def ofCoeffs (U : Coeffs d) : DiscretePR.PolyFock d := ⟨U.coeff, memℓp_gen …⟩   -- `p = 2` conversion as in `toCoeffs`
theorem toFunH_eq_polyanalyticEval (h') (U) : toFunH h' U = DiscretePR.polyanalyticEval h' (ofCoeffs U) := rfl  -- or `funext; rfl`
theorem memLp_toFun (hd) (κ) (U) : MemLp (toFun κ U) 2 (gamma_d d) := (l2_tsum_represents_toFun hd κ U).choose  -- `TensorBasis.lean:1015`
theorem memLp_toFunH (hd) (h') (U) : MemLp (toFunH h' U) 2 (gamma_d d)          -- `toFunH_eq_finsetSum`, `memLp_finset_sum`, `MemLp.const_mul`
theorem continuous_toFunH (hd) (h') (U) : Continuous (toFunH h' U)              -- `toFunH_eq_finsetSum`, `continuous_toFun`
theorem toFunH_mem_polyFockSpace (hd) (h') (U) : toFunH h' U ∈ DiscretePR.PolyFockSpace h'
-- `gamma_d d = DiscretePR.γ` is `rfl` (identical bodies, `PROVENANCE.md`); the witness is `ofCoeffs U`
```

About 60 lines.

## 5. `STFT.lean` — assembly (imports `Main`, `HermiteBasis`, `WindowExpansion`)

Follow Section 1 literally: obtain `c` from `gaussWindow_eq_sum`, `hc : c ≠ 0` from
`gaussWindow_ne_zero` (if `c = 0` the sum is `0`); `h' := signedConj c`; the main theorem for `h'`;
`S := {p | phaseToC p ∈ S_ℂ}` (as `Set (RealVec d × RealVec d)`); separation by `phaseDist_eq` and
`phaseToC_injective`; for `f g`: `U := hermiteCoeffs f`, `V := hermiteCoeffs g`, rewrite `f`, `g`
by `hermiteExpansion_hermiteCoeffs`; moduli on `S_ℂ` via `phaseToC_phaseToCInv`,
`windowH_signedConj`, `stftRep_window_smul` (the scalar `‖c‖⁻¹` is real, `star` of it is itself,
`norm_smul`/`norm_mul` with `‖c‖⁻¹ ≠ 0`), `stft_model_modulus_mixed`, `gaussWeight_pos`;
membership via `toFunH_mem_polyFockSpace`; the main theorem's `θ`; `exact_modulus_recovery_mixed`;
`hermiteExpansion_smul`.  About 90 lines.  The `stft`/`stftRep` and `L2Real`/`RealVec`
identifications are `rfl`.

## 6. Verification and bookkeeping

`lake build STFT` with no `sorry`; add `#print axioms DiscretePR.STFTDiscretePhaseRetrieval` to
`Check.lean` (expected: the three standard axioms) and `import STFT` there; `README.md`: the
folder is `sorry`-free again except the comparator; `STFT.lean` module docstring: drop the
"proof status" paragraph; `DiscretePhaseRetrieval/CLAIMS.md`: one row for the corollary.
