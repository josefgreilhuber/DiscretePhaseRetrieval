# Plan: the Gröchenig–Folland convention (weight `e^{−π|z|²}`, Gaussian `e^{−π|t|²}`, kernel `e^{−2πi ξ·t}`)

**Status: superseded.**  The project-wide convention change described here was executed on 2026-09-18 and then reverted by the author: the paper keeps the Fock side in the unit scale (weight `e^{−|z|²}`, main theorem with `4√d/10⁷`) and changes the normalisation only for the STFT corollary (window `h(x) e^{−π|x|²}`, Euclidean distance, `√d/10⁷`).  Of this plan only Section 5 (the dilation bridge, `DiscretePhaseRetrieval/Dilation.lean`) is in use, together with a trimmed `UnitScale.lean` holding `phaseDistUnit`, `UniformlyDiscretePhaseUnit`, `gaussWindowUnit`; `Rescale.lean`, the `Unit` renames of the Fock objects and the public `HermitePoly`/`γ` changes are not.  Former status: executed.  Four sequential batches (4 split in two); full `lake build` and `Check` pass; the three audited theorems depend on `propext`, `Classical.choice`, `Quot.sound`.  Deviations: `dilate` is normalised by `dilateFactor c d = √(c^d)`; the window identity is stated as `dilate_gaussWindowUnit` with the consequences `stft_gaussWindow`, `norm_stft_gaussWindow`; the dilation parameter is the named constant `sqrtTwoPi`; four `private`s removed in `WindowExpansion.lean` so that the unit window's `MemLp` can be dilated.  Public statements move to the Gröchenig–Folland convention;
the separation constant of both theorems becomes `√d / 10⁷`.

## 0. Design decision: rescaling bridges, not a re-derivation

The proof machinery (`PolyFock/`, `DiscretePhaseRetrieval/`, `ContinuousPhaseRetrieval/`,
about 30 000 lines) is written for the *unit scale*: Fock weight `π^{−d} e^{−|z|²}`, Hermite
functions `ψₙ(t) = (2ⁿ n! √π)^{−1/2} Hₙ(t) e^{−t²/2}`, kernel `e^{−2πi ξ·t}`, basis
`φ_{m,n}(z, z̄) = (m! n!)^{−1/2} H_{m,n}(z, z̄)`.  The Gröchenig–Folland objects are unitary
rescalings of these:

* Fock side: `z = √π w`.  The weight `e^{−π|w|²} dw` is the image of `π^{−d} e^{−|z|²} dz`
  under `z ↦ z/√π` (Jacobian `π^d` cancels `π^{−d}`), and the new basis is
  `φ^π_{m,n}(w) = (m! n!)^{−1/2} H_{m,n}(√π w, √π w̄) = φ_{m,n}(√π w)`.
* Real side: `t = s/√(2π)`.  The new Hermite functions are `hₙ(t) = (2π)^{1/4} ψₙ(√(2π) t)`, i.e.
  `hₙ = D ψₙ` for the unitary dilation `(Df)(t) = (2π)^{d/4} f(√(2π) t)` of `L²(ℝ^d)`; the STFT
  transforms as `V_{Dg}(Df)(x, ξ) = V_g f(√(2π) x, ξ/√(2π))`.
* Phase-space map: the unit-scale map `T(x, ξ) = (x − 2πi ξ)/√2` composed with these
  rescalings is `w = x − iξ`, an isometry.  So the unit-scale `phaseDist` becomes the Euclidean
  distance, and separations divide by `√π` on the Fock side: `4√d/10⁷` becomes
  `4√d/(√π 10⁷) ≥ √d/10⁷` (as `√π ≤ 4`), which is why the new constant is `√d/10⁷`.

Therefore: **the public definitions (`Definitions.lean`, `Showcase.lean`) and both theorems
adopt the new convention; the machinery keeps the unit scale, renamed with the suffix `Unit`
and moved to one Mathlib-only file; two explicit bridges (about 350 lines) derive the public
theorems from the unit-scale ones.**  Re-deriving the machinery in the `π`-scale would mean
re-proving thousands of lines of explicit constants (`√2` appears 508 times and `2π` 426 times
in `ExactModulusRecovery.lean` alone) for the same public statements; the bridge route gives
the public statements now, and a later in-place re-derivation, if ever wanted, changes nothing
public.  Both routes leave `Check.lean`'s guarantee intact: the proved theorems have the
comparator's statements, on the three standard axioms.

## 1. `Definitions.lean` (public, imports only Mathlib, namespace `DiscretePR`)

Unchanged: `PolyFock`, `coeff`, `euclideanDist`, `UniformlyDiscrete`, `PhaseRetrievalSet`,
`RealVec`, `L2Real`, `stft`.  Changed:

```lean
/-- `φ_{m,n}(z, z̄) = (m! n!)^{-1/2} H_{m,n}(√π z, √π z̄)`: the complex Hermite basis of
`L²(ℂ, e^{−π|z|²} dz)` (Gröchenig–Folland normalisation; `H_{m,n}` the classical complex
Hermite polynomial). -/
def HermitePoly (m n : ℕ) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) : ℂ)⁻¹) *
    ∑ r ∈ Finset.range (min m n + 1),
      ((-1 : ℂ) ^ r) * (Nat.factorial r : ℂ) * (Nat.choose m r : ℂ) * (Nat.choose n r : ℂ) *
        ((Real.sqrt Real.pi : ℂ) * z) ^ (m - r) * ((Real.sqrt Real.pi : ℂ) * star z) ^ (n - r)
-- Φ, Ψ, polyanalyticEval, PolyFockSpace: same text as now, on top of the new HermitePoly
def gaussianDensity (z : Fin d → ℂ) : ℝ := Real.exp (-Real.pi * ∑ i, ‖z i‖ ^ 2)   -- no 1/π^d
def γ : Measure (Fin d → ℂ) := volume.withDensity fun z => ENNReal.ofReal (gaussianDensity z)
/-- ε-uniformly discrete subsets of phase space, Euclidean distance on ℝ^d × ℝ^d. -/
def UniformlyDiscretePhase (ε : ℝ) (S : Set (RealVec d × RealVec d)) : Prop :=
  ∀ x ξ, (x, ξ) ∈ S → ∀ x' ξ', (x', ξ') ∈ S → (x, ξ) ≠ (x', ξ') →
    ε ≤ Real.sqrt (‖x - x'‖ ^ 2 + ‖ξ - ξ'‖ ^ 2)
/-- The window `h(x) e^{−π|x|²}`. -/
def gaussWindow (h : MvPolynomial (Fin d) ℝ) : L2Real d :=   -- same `if MemLp` pattern
  … ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * Real.exp (-Real.pi * ‖x‖ ^ 2) …
```

`phaseDist` is deleted.  Module docstrings: state the convention and cite Gröchenig,
*Foundations of Time-Frequency Analysis*, Ch. 3, and Folland, *Harmonic Analysis in Phase Space*,
Ch. 1.  `Showcase.lean` repeats the main-theorem definitions verbatim; both theorems read

```lean
theorem DiscretePhaseRetrieval (d : ℕ) (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0) :
    ∃ S : Set (Fin d → ℂ), UniformlyDiscrete (Real.sqrt d / 10 ^ 7) S ∧ PhaseRetrievalSet (PolyFockSpace h) S
theorem STFTDiscretePhaseRetrieval (d : ℕ) (hd : 0 < d) (h : MvPolynomial (Fin d) ℝ) (hnonzero : h ≠ 0) :
    ∃ S : Set (RealVec d × RealVec d), UniformlyDiscretePhase (Real.sqrt d / 10 ^ 7) S ∧
      ∀ f g : L2Real d, (∀ x ξ, (x, ξ) ∈ S → ‖stft (gaussWindow h) f x ξ‖ = ‖stft (gaussWindow h) g x ξ‖) →
        ∃ θ : ℂ, ‖θ‖ = 1 ∧ f = θ • g
```

## 2. `DiscretePhaseRetrieval/UnitScale.lean` (new, imports `Definitions`, namespace `DiscretePR`)

The *current* definitions, verbatim, with the suffix `Unit`: `HermitePolyUnit`, `ΦUnit`,
`ΨUnit`, `gaussianDensityUnit` (with `1/π^d`), `γUnit`, `polyanalyticEvalUnit`,
`PolyFockSpaceUnit`, `phaseDistUnit`, `UniformlyDiscretePhaseUnit`, `gaussWindowUnit`
(`h(x) e^{−|x|²/2}`).  Docstring: "the unit-scale objects in which the proofs are carried out;
`Rescale.lean` and `Dilation.lean` relate them to the public ones".

## 3. Mechanical renames (proofs unchanged)

* `PolyFock/*`, `DiscretePhaseRetrieval/*` (all files but `UnitScale`, `Rescale`, `Dilation`,
  `Main`): `import Definitions` → `import DiscretePhaseRetrieval.UnitScale` where the basis is
  used; `HermitePoly` → `HermitePolyUnit`, `Φ` → `ΦUnit`, `Ψ` → `ΨUnit`, `γ` → `γUnit`,
  `gaussianDensity` → `gaussianDensityUnit`, `polyanalyticEval` → `polyanalyticEvalUnit`,
  `PolyFockSpace` → `PolyFockSpaceUnit`; `open DiscretePR (Φ)` → `open DiscretePR (ΦUnit)`, etc.
  `euclideanDist`, `UniformlyDiscrete`, `PhaseRetrievalSet`, `PolyFock`, `coeff`, `size` unchanged.
* `ContinuousPhaseRetrieval/`: `MixedLevel.lean` (`DiscretePR.Ψ` → `ΨUnit`),
  `ContinuousPR.lean` (`polyanalyticEval` → `polyanalyticEvalUnit`), `WindowExpansion.lean`
  (`gaussWindow` → `gaussWindowUnit`, `phaseDist` → `phaseDistUnit`, `polyanalyticEval`,
  `PolyFockSpace`, `γ` → `Unit`), `DiscretePhaseRetrieval/ContinuousPR.lean` (`polyanalyticEvalUnit`).
  `HermiteBasis.lean` mentions none of them (check).
* `Main.lean`: the present theorem becomes `DiscretePhaseRetrieval_unit` (statement with
  `PolyFockSpaceUnit`, constant `4 * Real.sqrt d / 10 ^ 7`), plus the coefficient-level form
  its proof already establishes, which the bridge needs (no `MemLp`/continuity of the unit-scale
  function is then required):
  ```lean
  theorem DiscretePhaseRetrieval_unit_coeff (d) (hd) (h) (hnonzero) :
      ∃ S : Set (Fin d → ℂ), UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧
        ∀ F G : PolyFock d, (∀ s ∈ S, ‖polyanalyticEvalUnit h F s‖ = ‖polyanalyticEvalUnit h G s‖) →
          ∃ θ : ℂ, ‖θ‖ = 1 ∧ polyanalyticEvalUnit h F = θ • polyanalyticEvalUnit h G
  ```
  (factor the present proof so that both follow from it).  `DiscretePhaseRetrieval_single` is
  restated for the public theorem at the end (Section 4).
* `STFT.lean`: the present theorem and proof become `STFTDiscretePhaseRetrieval_unit` (stated
  with `gaussWindowUnit`, `UniformlyDiscretePhaseUnit`, constant `4√d/10⁷`).

## 4. `DiscretePhaseRetrieval/Rescale.lean` (new): the Fock-side bridge and the public main theorem

```lean
theorem HermitePoly_eq_unit (m n z) : HermitePoly m n z = HermitePolyUnit m n ((Real.sqrt Real.pi : ℂ) * z)
-- unfold both; `star_mul`, `Complex.conj_ofReal`, `mul_pow`; termwise
theorem Φ_eq_unit (n q) (w : Fin d → ℂ) : Φ n q w = ΦUnit n q ((Real.sqrt Real.pi : ℂ) • w)
theorem Ψ_eq_unit (n h w) : Ψ n h w = ΨUnit n h ((Real.sqrt Real.pi : ℂ) • w)
theorem polyanalyticEval_eq_unit (h F w) : polyanalyticEval h F w = polyanalyticEvalUnit h F ((Real.sqrt Real.pi : ℂ) • w)
theorem euclideanDist_smul (c : ℂ) (x y) : euclideanDist (c • x) (c • y) = ‖c‖ * euclideanDist x y
theorem sqrt_pi_le_four : Real.sqrt Real.pi ≤ 4        -- `Real.pi_le_four`, `Real.sqrt_le_sqrt`, `√16 = 4`
```

`Main.lean`, public theorem `DiscretePhaseRetrieval_proved`: from `DiscretePhaseRetrieval_unit_coeff`
obtain `S₀`; put `S := (fun z => ((Real.sqrt Real.pi : ℂ)⁻¹) • z) '' S₀`.  Separation: for
`w = c⁻¹ • z`, `w' = c⁻¹ • z'`, `euclideanDist w w' = c⁻¹ euclideanDist z z' ≥ 4√d/(c 10⁷) ≥ √d/10⁷`
with `c = √π ≤ 4`.  Phase retrieval: for `f, g ∈ PolyFockSpace h` obtain `F, G`; on `S` the
moduli of `polyanalyticEvalUnit h F (c • w)` agree, i.e. on `S₀`; the coefficient-level theorem
gives `θ`; compose with `w ↦ c • w`.  `DiscretePhaseRetrieval_single` as before.

## 5. `DiscretePhaseRetrieval/Dilation.lean` (new): the real-side bridge and the public STFT theorem

Imports `Definitions`, `DiscretePhaseRetrieval.UnitScale`,
`ContinuousPhaseRetrieval.ModulusRecovery.ImportedAnalyticInputs` (for `stftRep`) — or state
everything with `DiscretePR.stft`.

```lean
/-- `(D_c f)(t) = c^{d/2} f(c t)`, the unitary dilation of `L²(ℝ^d)` (`c > 0`). -/
def dilate (c : ℝ) (f : L2Real d) : L2Real d
theorem dilate_coe (hc : 0 < c) (f) : (dilate c f : RealVec d → ℂ) =ᵐ[volume] fun t => ((c ^ ((d : ℝ)/2) : ℝ) : ℂ) * f (c • t)
-- MemLp of `t ↦ f (c • t)`: `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` (the map
-- `c • ·` pushes `volume` to a constant multiple), `memLp_map_measure_iff`, `QuasiMeasurePreserving.ae_eq_comp`
theorem dilate_smul (c) (θ : ℂ) (f) : dilate c (θ • f) = θ • dilate c f
theorem dilate_dilate_inv (hc : 0 < c) (f) : dilate c (dilate c⁻¹ f) = f
theorem stft_dilate (hc : 0 < c) (w f : L2Real d) (x ξ) :
    stft (dilate c w) (dilate c f) x ξ = stft w f (c • x) (c⁻¹ • ξ)
-- unfold `stft`; `MeasureTheory.Measure.integral_comp_smul` (`∫ F (c • t) = |c^{-d}| ∫ F`), the
-- a.e. descriptions `dilate_coe`, `inner_smul_left`, `Complex.exp` algebra; the factors `c^{d/2}·c^{d/2}·c^{−d}` cancel
/-- The unit-scale window of the rescaled polynomial `h̃(t) = h(t/√(2π))`. -/
def rescalePoly (c : ℝ) (h : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C c * MvPolynomial.X i) h
theorem eval_rescalePoly (c h t) : MvPolynomial.eval t (rescalePoly c h) = MvPolynomial.eval (c • t) h
theorem rescalePoly_ne_zero (hc : c ≠ 0) (hh : h ≠ 0) : rescalePoly c h ≠ 0    -- via `MvPolynomial.funext`
theorem dilate_inv_gaussWindow (h) : dilate (Real.sqrt (2 * Real.pi))⁻¹ (gaussWindow h)
    = (((2 * Real.pi) ^ (-(d : ℝ)/4) : ℝ) : ℂ) • gaussWindowUnit (rescalePoly (Real.sqrt (2 * Real.pi))⁻¹ h)
-- `Lp.ext`, `dilate_coe`, the two `if MemLp` branches (both taken), `exp` algebra `π|t/√(2π)|² = |t|²/2`
theorem phaseDistUnit_scaled (x ξ x' ξ') : phaseDistUnit (c • x) (c⁻¹ • ξ) (c • x') (c⁻¹ • ξ') = Real.sqrt Real.pi * Real.sqrt (‖x - x'‖ ^ 2 + ‖ξ - ξ'‖ ^ 2)   -- with c = √(2π)
```

`STFT.lean`, public theorem `STFTDiscretePhaseRetrieval`: with `c = √(2π)`, apply
`STFTDiscretePhaseRetrieval_unit` to `rescalePoly c⁻¹ h` (nonzero) to get `S₀`; put
`S := {(x, ξ) | (c • x, c⁻¹ • ξ) ∈ S₀}`.  Separation from `phaseDistUnit_scaled` and `√π ≤ 4`.
For `f, g`: `f' := dilate c⁻¹ f`, `g' := dilate c⁻¹ g`; by `stft_dilate` and
`dilate_inv_gaussWindow` (the scalar cancels in the moduli, `stftRep_window_smul`-style or
`stft` linearity in the window — prove `stft (a • w) f x ξ = star a * stft w f x ξ` here or reuse
`ModulusRecovery.stftRep_window_smul` through the `rfl` identification), the hypothesis on `S`
becomes the unit hypothesis on `S₀`; conclude `f' = θ • g'`, then
`f = dilate c f' = θ • dilate c g' = θ • g` (`dilate_dilate_inv`, `dilate_smul`).

## 6. Bookkeeping

`Check.lean` unchanged (names unchanged, three audits).  `README.md`: the convention paragraph
(new), the folder rows (`UnitScale`, `Rescale`, `Dilation`); `DiscretePhaseRetrieval/CLAIMS.md`:
rows M and STFT split into the unit-scale theorem and the bridge; `Definitions.lean`/`STFT.lean`
docstrings; memory note.  Verification: full `lake build`, `lake build Check` (three theorems,
standard axioms), the only `sorry` the comparator's.

## 7. Execution: four sequential batches, one agent each, never two builds at once

The machine cannot run two `lake` builds concurrently (out-of-memory); every batch builds only
its own targets, in import order, and the next batch starts only after the previous one reports.

1. **Batch 1** — `Definitions.lean` (new convention), `DiscretePhaseRetrieval/UnitScale.lean`,
   `Showcase.lean` (new theorem statement, `sorry`).  Build: `lake build Definitions
   DiscretePhaseRetrieval.UnitScale Showcase`.
2. **Batch 2** — renames in `PolyFock/*` and `DiscretePhaseRetrieval/*` (all but `Main`), the unit
   theorem and its coefficient form in `Main.lean`.  Build, in order: `PolyFock.Check`,
   `DiscretePhaseRetrieval.Limit DiscretePhaseRetrieval.BlockEstimate` (the CPR bridge and `Main`
   are built in batch 3).
3. **Batch 3** — renames in `ContinuousPhaseRetrieval/ContinuousPR.lean`, `MixedLevel.lean`,
   `WindowExpansion.lean`, `DiscretePhaseRetrieval/ContinuousPR.lean`; `STFT.lean` unit theorem.
   Build, in order: `ContinuousPhaseRetrieval.ModulusRecovery.WindowExpansion`,
   `ContinuousPhaseRetrieval.ContinuousPR`, `DiscretePhaseRetrieval.ContinuousPR`, `Main`, `STFT`
   (`STFT` still ends with the unit theorem only).
4. **Batch 4** — `Rescale.lean`, `Dilation.lean`, the public theorems in `Main.lean` and
   `STFT.lean`, `Check`, docs.  Build: `DiscretePhaseRetrieval.Rescale`,
   `DiscretePhaseRetrieval.Dilation`, `Main`, `STFT`, `Check`, then one full `lake build`.
