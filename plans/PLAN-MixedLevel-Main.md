# Plan: the main theorem for the mixed-level spaces `𝓕_h` (everything outside `ContinuousPhaseRetrieval/`)

**Status (2026-09-17): executed and complete.**  `lake build` and `lake build Check` pass; `DiscretePhaseRetrieval_proved` (renamed from `PolyDiscreteSPR_proved`, comparator `DiscretePhaseRetrieval`) has the comparator's statement and the three standard axioms.  Deviations: `blockSep_ge` needs `hnonzero : h ≠ 0` (for `g = 0` the space is `⊥` and `blockSep = 0`); `hnorm_sq` needs no `hg`; `tailConstH d h = ∑ q ∈ h.support, tailConst d ‖q‖₁`; the corollary `DiscretePhaseRetrieval_single` was added.  Original text follows.  The continuous-phase-retrieval input is planned separately in
`PLAN-MixedLevel-ContinuousPR.md` (executed together with `PLAN-RemovePhantomLevel.md`, the
removal of the phantom level index from that folder's coefficient types); the plans meet in
`DiscretePhaseRetrieval/ContinuousPR.lean`.
Until both are executed, `lake build` fails from `DiscretePhaseRetrieval/Defs.lean` on (the
level-`κ` statements no longer match `Definitions.lean`); `lake build Definitions Showcase`
succeeds.

## 0. What changed and what has to change

`Definitions.lean` (namespace `DiscretePR`, imports only Mathlib) now has, in place of the
level-`κ` space `𝓕^d_q`:

```lean
def Ψ (n : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) (z : Fin d → ℂ) : ℂ :=
  (((Real.sqrt (∑ q ∈ h.support, ‖h q‖ ^ 2)) : ℂ)⁻¹) * ∑ q ∈ h.support, h q * Φ n q z
def polyanalyticEval (h : (Fin d → ℕ) →₀ ℂ) (F : PolyFock d) (z : Fin d → ℂ) : ℂ :=
  ∑' n : Fin d → ℕ, coeff F n * Ψ n h z
def PolyFockSpace (h : (Fin d → ℕ) →₀ ℂ) : Set ((Fin d → ℂ) → ℂ) :=
  { f | MemLp f 2 γ ∧ Continuous f ∧ ∃ F : PolyFock d, f = polyanalyticEval h F }
```

`HermitePoly`, `Φ`, `γ`, `PolyFock`, `coeff`, `euclideanDist`, `UniformlyDiscrete`,
`PhaseRetrievalSet` are unchanged.  `Showcase.lean` repeats all of this in
`DiscretePR_Showcase` and states

```lean
theorem DiscretePhaseRetrieval (d : ℕ) (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0) :
    ∃ S : Set (Fin d → ℂ),
      UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧ PhaseRetrievalSet (PolyFockSpace h) S
```

with the same separation as before.  Target: `DiscretePR.DiscretePhaseRetrieval_proved` in `Main.lean`
with this statement, `Check.lean` unchanged and passing.

The proof of the paper goes through with `L = ‖q‖₁` replaced by `L = max {‖q‖₁ : h_q ≠ 0}`,
and the paper's estimates for `Φ_{n,q}` transferred to `Ψ_{n,h}` by Cauchy–Schwarz over the
finitely many levels in the support.  In Lean, the level `κ` enters the existing files in exactly
three ways, each with its replacement:

| use of `κ` | where | replacement |
|---|---|---|
| the basis `Φ α κ` in the coefficient model (`polyanalyticEval κ`, `summable_Phi_sq κ`, kernel and tail bounds) | `KernelBound`, `Coefficients`, `TailBound`, `Limit`, `Main` | `Ψ α h`; kernel/tail bounds for `Ψ` from those for `Φ · q`, `q ∈ h.support` (Sections 2, 4) |
| the polynomial `Psihat α κ ∈ ℂ[z, z̄]`, the space `VqN κ N`, degree `N + ‖κ‖₁` | `Defs`, `Bridge`, `Polynomials`, `BlockNorming`, `BlockEstimate` | `PsihatH α h`, `VhN h N`, degree `N + L` (Sections 1, 3) |
| the thresholds `3‖κ‖₁ ≤ N`, `‖κ‖₁ + 9 ≤ N`, `max (3‖κ‖₁) (‖κ‖₁+9)` | `TailBound`, `BlockEstimate`, `Main` | the same with `L = levelBound h` |

Files that do not change: `Auxiliary.lean`, `Annulus.lean`, everything in `PolyFock/`,
`DiscreteNorming/`, `Remez/`, `VCInequality/`, `Warren/`, `Check.lean`, `PolyFock/Check.lean`.
In particular `PolyFock.tail_bound` (Lemma 3.1) is used per level exactly as now: its
`tailKernelDiag L N z` already sums over **all** `q` with `‖q‖₁ = L`.

The hypothesis `hnonzero : h ≠ 0` is needed at two places only: `1 ≤ dim VhN h N` (Section 3, for
Proposition 2.1) and continuous phase retrieval (the other plan).  All estimates hold for every
`h` (for `g = 0` both sides vanish, Lean's `(√0)⁻¹ = 0`).

## 1. `DiscretePhaseRetrieval/Defs.lean`

Add, before the existing definitions:

```lean
/-- `L = max {‖q‖₁ : q ∈ supp g}`, the paper's `L` with `h_q = 0` for `‖q‖₁ > L`. -/
def levelBound (h : (Fin d → ℕ) →₀ ℂ) : ℕ := h.support.sup size
theorem size_le_levelBound {h} {q} (hq : q ∈ h.support) : ‖q‖₁ ≤ levelBound h :=
  Finset.le_sup hq

/-- `‖h‖ = (∑ |h_q|²)^{1/2}`, the normalisation of `Ψ`. -/
def hnorm (h : (Fin d → ℕ) →₀ ℂ) : ℝ := Real.sqrt (∑ q ∈ h.support, ‖h q‖ ^ 2)
theorem hnorm_pos {h} (hnonzero : h ≠ 0) : 0 < hnorm h
  -- `Finsupp.support_nonempty_iff.mpr hg`, `Finset.sum_pos'` (some `‖h q‖ ^ 2 > 0`), `Real.sqrt_pos`
theorem hnorm_sq {h} (hnonzero : h ≠ 0) : hnorm h ^ 2 = ∑ q ∈ h.support, ‖h q‖ ^ 2  -- `Real.sq_sqrt`

/-- `Ψ_{α,h}` as a polynomial in `ℂ[z, z̄]`. -/
def PsihatH (α : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) : P d :=
  MvPolynomial.C ((hnorm h : ℂ)⁻¹) * ∑ q ∈ h.support, MvPolynomial.C (h q) * Psihat α q
```

Replace `truncPoly κ N F`, `VqN κ N`, `blockSep d κ N` by

```lean
def truncPoly (h) (N : ℕ) (F : PolyFock d) : P d := ∑ α ∈ box d N, MvPolynomial.C (F α) * PsihatH α h
def VhN (h) (N : ℕ) : Submodule ℂ (P d) :=
  Submodule.span ℂ (Set.range fun α : box d N ↦ PsihatH (α : Fin d → ℕ) h)
def blockSep (d : ℕ) (h) (N : ℕ) : ℝ :=
  DiscreteNorming.deltaPaper d (annulus d mu N) * (Module.finrank ℂ (VhN h N) : ℝ) ^ (-(1 / (2 * d : ℝ)))
```

(`mu`, `ofC`, `box`, `truncate`, `annulus` unchanged.)  Update the module docstring.

## 2. `Bridge.lean`, `KernelBound.lean`: the basis `Ψ` pointwise

`Bridge.lean`: keep `Phi_eq_ev`; add

```lean
theorem Psi_eq_ev (α) (h) (z) : Ψ α h z = ev z (PsihatH α h)
-- `PsihatH`, `map_mul`, `map_sum`, `ev_C`, `Phi_eq_ev`; unfold `Ψ`, `hnorm`
```

`KernelBound.lean`: keep `sum_sq_phi_le`, `kernel_bound κ`, `summable_Phi_sq κ` (single level,
used per `q ∈ h.support`).  Add at the end:

```lean
/-- Cauchy–Schwarz over the support: `‖Ψ_{α,h}(z)‖² ≤ ∑_{q ∈ supp g} ‖Φ_{α,q}(z)‖²`. -/
theorem sq_norm_Psi_le (α) (h) (z) : ‖Ψ α h z‖ ^ 2 ≤ ∑ q ∈ h.support, ‖Φ α q z‖ ^ 2
-- `Ψ`, `norm_mul`, `mul_pow`, `norm_inv`, `norm_sum_le`, `norm_mul`,
-- `Finset.sum_mul_sq_le_sq_mul_sq h.support (‖h ·‖) (‖Φ α · z‖)`; the factor
-- `(∑ ‖h q‖²)⁻¹ · (∑ ‖h q‖²) ≤ 1` (`inv_mul_le_one`-type, both cases `= 0` / `> 0`)

theorem summable_Psi_sq (h) (z) : Summable fun α ↦ ‖Ψ α h z‖ ^ 2
-- `Summable.of_nonneg_of_le` with `sq_norm_Psi_le` and `summable_sum` of `summable_Phi_sq q z`

/-- K for `Ψ`: `∑_α ‖Ψ_{α,h}(z)‖² ≤ C (1 + |z|²)^{4L} e^{|z|²}`, `L = levelBound h`. -/
theorem kernel_bound_mixed (h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin d → ℂ,
      ∑' α, ‖Ψ α h z‖ ^ 2
        ≤ C * (1 + euclideanDist z 0 ^ 2) ^ (4 * levelBound h) * Real.exp (euclideanDist z 0 ^ 2)
-- choose `C_q` by `kernel_bound q` for each `q ∈ h.support` (`Classical.choose` over the finset,
-- or `Finset.sum` of chosen constants), `C := ∑ q ∈ h.support, C_q`;
-- `tsum_le_of_sum_le`/`Summable.tsum_le_tsum` with `sq_norm_Psi_le`, `tsum_finsetSum` (swap),
-- `(1+t)^{4‖q‖₁} ≤ (1+t)^{4L}` by `pow_le_pow_right₀ (by linarith) (by omega)` and
-- `size_le_levelBound`; `Finset.sum_mul`
```

About 70 lines.  (`kernel_bound` and `summable_Phi_sq` keep their names; the `Ψ` versions get the
suffix `_mixed` / the name `summable_Psi_sq`.)

## 3. `Polynomials.lean`: the spaces `VhN h N`

Keep `mem_box`, `card_box`, `totalDegree_Psihat_le`, `choose_le_pow_mul_exp`.  Replace the
`κ` statements:

```lean
theorem totalDegree_PsihatH_le (α) (h) : (PsihatH α h).totalDegree ≤ ‖α‖₁ + levelBound h
-- `totalDegree_mul`, `totalDegree_C`, `totalDegree_finsetSum_le`, per term
-- `totalDegree_Psihat_le α q` and `size_le_levelBound hq`

theorem totalDegree_le_of_mem_VhN {h} {N} {F : P d} (hF : F ∈ VhN h N) :
    F.totalDegree ≤ N + levelBound h        -- same `span_induction` as now

/-- `PsihatH α h ≠ 0` for `h ≠ 0`: pairing with one `Psihat α q₀`, `q₀ ∈ supp g`, under the
Fock form recovers `(hnorm h)⁻¹ h_{q₀} ≠ 0` (`form_Psihat` is orthonormality over all pairs). -/
theorem form_PsihatH_Psihat (α) (h) (q₀) :
    form (PsihatH α h) (Psihat α q₀) = (hnorm h : ℂ)⁻¹ * (if q₀ ∈ h.support then h q₀ else 0)
-- `PsihatH`, `← MvPolynomial.smul_eq_C_mul`, `form_smul_left`, `form_add_left` over the finset
-- (`Finset.sum` version: induction or `form` as an additive map in the left slot),
-- `form_Psihat α q α q₀` = `if α = α ∧ q = q₀ then 1 else 0`, `Finset.sum_ite_eq`
theorem PsihatH_ne_zero {h} (hnonzero : h ≠ 0) (α) : PsihatH α h ≠ 0
-- pick `q₀ ∈ h.support` (`Finsupp.support_nonempty_iff`), `form_zero_left`, `hnorm_pos`

theorem one_le_finrank_VhN {h} (hnonzero : h ≠ 0) (N) : 1 ≤ Module.finrank ℂ (VhN h N)
theorem finrank_VhN_le (h) (N) : Module.finrank ℂ (VhN h N) ≤ (N + d).choose d
```

The form is only used in the **left** slot, so whether `form` is bilinear or sesquilinear in
the right slot is irrelevant (it need not be checked).  About 50 lines net.

## 4. `Coefficients.lean`, `TailBound.lean`: the series and its tail

`Coefficients.lean`: mechanical.  `κ : Fin d → ℕ` becomes `h : (Fin d → ℕ) →₀ ℂ`, `Φ α κ` becomes
`Ψ α h`, `summable_Phi_sq κ z` becomes `summable_Psi_sq h z`, `Phi_eq_ev` in `eval_truncate`
becomes `Psi_eq_ev`, `truncPoly_mem` with `VhN`.  Statements after the change:

```lean
theorem summable_eval (h) (F) (z) : Summable fun α ↦ coeff F α * Ψ α h z
theorem eval_le (h) (F) (z) : ‖polyanalyticEval h F z‖ ^ 2 ≤ ‖F‖ ^ 2 * ∑' α, ‖Ψ α h z‖ ^ 2
theorem eval_truncate_eq_sum (h) (N) (F) (z) :
    polyanalyticEval h (truncate N F) z = ∑ α ∈ box d N, coeff F α * Ψ α h z
theorem eval_truncate (h) (N) (F) (z) : polyanalyticEval h (truncate N F) z = ev z (truncPoly h N F)
theorem truncPoly_mem (h) (N) (F) : truncPoly h N F ∈ VhN h N
theorem tail_eval_le (h) (N) (F) (z) : … ≤ ‖F‖ ^ 2 * ∑' α, (if N < ‖α‖₁ then ‖Ψ α h z‖ ^ 2 else 0)
theorem tendsto_truncate (h) (F) (z) : Tendsto (fun N ↦ polyanalyticEval h (truncate N F) z) atTop (𝓝 (polyanalyticEval h F z))
```

No new lines beyond renaming.

`TailBound.lean`: keep `summable_tail_family`, `tail_le_tailKernelDiag κ` (per level),
`abs_sq_sub_sq_le`.  Add the mixed tail and a uniform constant:

```lean
/-- The tail of the `Ψ` series is dominated by the tails of the level-`q` series, `q ∈ supp g`. -/
theorem tail_le_tailKernelDiag_mixed (h) (N) (z) :
    ∑' α, (if N < ‖α‖₁ then ‖Ψ α h z‖ ^ 2 else 0)
      ≤ ∑ q ∈ h.support, tailKernelDiag (‖q‖₁) N z
-- `sq_norm_Psi_le` inside the `if`, `Summable.tsum_le_tsum`, `tsum_finsetSum` (swap), then
-- `tail_le_tailKernelDiag q N z` termwise

/-- `C_g = |supp g| · max_{q ∈ supp g} tailConst d ‖q‖₁`, so that every level of the support
obeys the single-level tail bound with `L = levelBound h` (`tailConst d ‖q‖₁ ≤ C_g / |supp g|`). -/
def tailConstH (d) (h) : ℝ := h.support.card * (h.support.sup' … (fun q ↦ tailConst d ‖q‖₁))
-- or simply `∑ q ∈ h.support, tailConst d ‖q‖₁` (nonnegative terms), which is easier to use

theorem tail_bound_mixed (hd : 0 < d) (h) {N} (hN3 : 3 * levelBound h ≤ N)
    (hN9 : levelBound h + 9 ≤ N) (z) (hz : Real.exp 1 * euclideanDist z 0 ^ 2 < N) :
    ∑ q ∈ h.support, tailKernelDiag (‖q‖₁) N z
      ≤ tailConstH d h * (N : ℝ) ^ levelBound h
          * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * levelBound h)
          / (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)
-- per `q`: `PolyFock.tail_bound` (with `[NeZero d]` from `hd`, `3‖q‖₁ ≤ 3L ≤ N`, `‖q‖₁ + 9 ≤ N`),
-- then `N^{‖q‖₁} ≤ N^L` (`pow_le_pow_right₀`, `1 ≤ N`) and
-- `θ^{N − 2‖q‖₁} ≤ θ^{N − 2L}` (`pow_le_pow_of_le_one`, `0 ≤ θ < 1`, `N − 2L ≤ N − 2‖q‖₁`);
-- `Finset.sum_le_sum`, `Finset.sum_mul`
```

Then `truncation_error hd h hN3 hN9 F z hz` and `modulus_error hd h` keep their present
proofs with `tailConst d ‖κ‖₁ ↦ tailConstH d h`, `‖κ‖₁ ↦ levelBound h`,
`tail_le_tailKernelDiag κ` + `PolyFock.tail_bound` ↦ `tail_le_tailKernelDiag_mixed` +
`tail_bound_mixed`.  Statement of the result used downstream:

```lean
theorem modulus_error (hd : 0 < d) (h) :
    ∃ C : ℝ, ∃ c : ℕ, 0 ≤ C ∧ ∀ N : ℕ, max (3 * levelBound h) (levelBound h + 9) ≤ N →
      ∀ (F : PolyFock d) (z), euclideanDist z 0 ≤ mu * Real.sqrt N →
        |‖polyanalyticEval h F z‖ ^ 2 - ‖polyanalyticEval h (truncate N F) z‖ ^ 2|
          ≤ C * (N : ℝ) ^ c * Real.exp ((mu ^ 2 / 2 + 1 / 2 + Real.log mu) * N) * ‖F‖ ^ 2
```

About 80 new lines.

## 5. `BlockNorming.lean`, `BlockEstimate.lean`, `Limit.lean`: the blocks

`BlockNorming.lean`:

```lean
theorem block_norming (hd : 0 < d) (h) (hnonzero : h ≠ 0) {N : ℕ} (hN : 0 < N) :
    ∃ S : Finset (Fin d → ℂ), (∀ z ∈ S, ofC z ∈ annulus d mu N) ∧
      (∀ z ∈ S, ∀ w ∈ S, z ≠ w → blockSep d h N ≤ euclideanDist z w) ∧
      ∀ F ∈ VhN h N, ∀ G ∈ VhN h N, ∀ z, euclideanDist z 0 < mu * Real.sqrt N → ∃ w ∈ S,
        |‖ev z F‖ ^ 2 - ‖ev z G‖ ^ 2|
          ≤ Real.exp (4 * (N + levelBound h)) * |‖ev w F‖ ^ 2 - ‖ev w G‖ ^ 2|
theorem blockSep_ge (hd : 0 < d) (h) {N : ℕ} (hN : 16 * d ≤ N) :
    4 * mu * Real.sqrt d / 10 ^ 5 ≤ blockSep d h N
```

`block_norming`: `discrete_norming_explicit` with `𝒱 := VhN h N`, `n := N + levelBound h`
(`totalDegree_le_of_mem_VhN`), `hN := one_le_finrank_VhN hg N`; otherwise verbatim.
`blockSep_ge`: verbatim (uses `finrank_VhN_le` and P4 only; no `hg`).

`BlockEstimate.lean`: `exponent_neg`, `block_arith` unchanged;

```lean
theorem block_estimate (hd : 0 < d) (h) (hnonzero : h ≠ 0) :
    ∃ C : ℝ, ∃ c : ℕ, 0 ≤ C ∧ ∀ N : ℕ, max (3 * levelBound h) (levelBound h + 9) ≤ N → 0 < N →
      ∀ S : Finset (Fin d → ℂ), (∀ z ∈ S, ofC z ∈ annulus d mu N) →
        (∀ F ∈ VhN h N, ∀ G ∈ VhN h N, ∀ z, euclideanDist z 0 < mu * Real.sqrt N → ∃ w ∈ S,
          |‖ev z F‖ ^ 2 - ‖ev z G‖ ^ 2|
            ≤ Real.exp (4 * (N + levelBound h)) * |‖ev w F‖ ^ 2 - ‖ev w G‖ ^ 2|) →
        ∀ (F G : PolyFock d) (z), euclideanDist z 0 < mu * Real.sqrt N → ∃ w ∈ S, …
```

with `e^{4‖κ‖₁}` merged into `C` exactly as now (`‖κ‖₁ ↦ levelBound h`).  Whether `hg` is
needed here depends on whether the statement is kept in the present "given a norming set"
form (then no `hg`); keep that form and drop `hg`.

`Limit.lean`: `norm_eq_of_blocks h F G Nseq …` — rename only (`tendsto_truncate h`).
`annuli_far`, `union_separated`, `mu_pos` unchanged.

## 6. `ContinuousPR.lean` (discrete side), `Main.lean`

`DiscretePhaseRetrieval/ContinuousPR.lean`: as specified in `PLAN-MixedLevel-ContinuousPR.md`
Section 6c:

```lean
theorem continuous_phase_retrieval {d : ℕ} (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0)
    (F G : PolyFock d) (h : ∀ z, ‖polyanalyticEval h F z‖ = ‖polyanalyticEval h G z‖) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧ polyanalyticEval h F = θ • polyanalyticEval h G
```

`Main.lean`:

```lean
theorem DiscretePhaseRetrieval_proved (d : ℕ) (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0) :
    ∃ S : Set (Fin d → ℂ),
      UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧ PhaseRetrievalSet (PolyFockSpace h) S
```

Proof: the present one with `‖q‖₁ ↦ levelBound h` in `A` and `hN1`, `block_estimate hd h`,
`block_norming hd h hnonzero`, `blockSep_ge hd h`, `norm_eq_of_blocks h`, and
`continuous_phase_retrieval hd h hnonzero F G`.  Update the module docstring (`L = levelBound h`).

Optional corollary, worth adding to `Main.lean` since the paper states the single-level case:

```lean
/-- The true polyanalytic Fock space `𝓕^d_q` is the case `g = single q 1`. -/
theorem DiscretePhaseRetrieval_single (d : ℕ) (hd : 0 < d) (q : Fin d → ℕ) :
    ∃ S : Set (Fin d → ℂ), UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧
      PhaseRetrievalSet (PolyFockSpace (Finsupp.single q 1)) S :=
  DiscretePhaseRetrieval_proved d hd _ (Finsupp.single_ne_zero.mpr one_ne_zero)
```

`Check.lean`: unchanged (the `example` compares the two statements; `#print axioms` lines
stay).  Add the sanity example `Ψ n (Finsupp.single q 1) z = Φ n q z := by simp [Ψ]`.

## 7. Documentation and the git copy

* `DiscretePhaseRetrieval/CLAIMS.md`: rewrite the header for `𝓕_h`; rows P0 (add `Psi_eq_ev`),
  P1 (`totalDegree_PsihatH_le`), P2–P3 (`VhN`, `PsihatH_ne_zero`), W (`summable_Psi_sq`,
  `summable_eval`), K (`sq_norm_Psi_le`, `kernel_bound_mixed`), T (`tail_le_tailKernelDiag_mixed`,
  `tail_bound_mixed`, `tailConstH`), B1–C (`h`, `levelBound h`), CPR, M.
* `README.md`: the "main theorem" paragraph and the `PolyFock/` row ("for the basis `Φ`"; the
  mixed basis `Ψ` lives in `Definitions.lean`, its estimates in `DiscretePhaseRetrieval/`).
* `plans/PLAN-MainTheorem.md`: add a status line pointing here.
* The git checkout `DiscreteFock/PolyFockComplete2` (branch `polyfockcomplete2`) was identical to
  this folder before this change and has **not** been touched; copy the folder over (excluding
  `.lake`) and commit once `lake build Check` passes.

## 8. Order of work

Build order is the import order; every step is compilable on its own once the previous ones are:

1. `Defs.lean` (Section 1) — `lake build DiscretePhaseRetrieval.Defs`
2. `Bridge.lean`, `KernelBound.lean` (Section 2)
3. `Polynomials.lean` (Section 3)
4. `Coefficients.lean`, `TailBound.lean` (Section 4)
5. `BlockNorming.lean`, `BlockEstimate.lean`, `Limit.lean` (Section 5)
6. `PLAN-RemovePhantomLevel.md` and `PLAN-MixedLevel-ContinuousPR.md` together
   (`ContinuousPhaseRetrieval/`), then `DiscretePhaseRetrieval/ContinuousPR.lean`
7. `Main.lean`, `lake build Check` (axiom audit: `propext`, `Classical.choice`, `Quot.sound`)
8. Section 7

Steps 1–5 and the other plan are independent and can run in parallel.  Estimated new material
outside `ContinuousPhaseRetrieval/`: about 220 lines (Sections 1–4), the rest renaming.
