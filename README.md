# The formalisation of the paper

This folder is one Lake library holding the complete formalisation.  The only `sorry`s are the
three challenge declarations in the standalone comparator `Showcase.lean`; their proof bridges
are axiom-audited in `Check.lean`.  In dependency order:

| root | content |
|---|---|
| `Warren/` | algebraic Thom transversality, sharp weak Bézout, polynomial Sard, bounded components of real zero sets, Warren's sign-pattern bound |
| `Remez/` | the 1-D Remez inequality (Bojanov's proof) and the Brudnyi–Ganzburg multivariate Remez inequality (`Remez/Multivariate/`) |
| `VCInequality/` | the relative Vapnik–Chervonenkis inequality, with the Sauer–Shelah form |
| `DiscreteNorming/` | Proposition 2.1 (discrete norming inequality) and Lemma 2.2; claim map in `DiscreteNorming/CLAIMS.md` |
| `PolyFock/` | the polyanalytic Fock kernel: algebraic rotation invariance and tail bounds for the basis `DiscretePR.HermitePoly`/`DiscretePR.Φ` of `Definitions.lean` (`PolyFock/` defines no basis of its own) |
| `ContinuousPhaseRetrieval/` | continuous phase retrieval (`DiscretePolyFock.exactModulusRecovery`) for the mixed-level spaces `𝓕_h`, by the STFT/ambiguity-function argument: a fork (since 2026-09-17, maintained independently) of the earlier development by the author and collaborators, whose origin `ContinuousPhaseRetrieval/PROVENANCE.md` records; the coefficient families `ModulusRecovery.Coeffs d` carry no level, the mixed window and the mixed-level theorem are in `ModulusRecovery/MixedLevel.lean`; `ModulusRecovery/HermiteBasis.lean` proves that the Hermite functions are a Hilbert basis of `L²(ℝ^d)` (`hermiteHilbertBasis`, `hermiteExpansion_surjective`), and `ModulusRecovery/WindowExpansion.lean` expands a polynomial–Gaussian window in Hermite functions and transfers the phase-space geometry, both for the STFT corollary |
| `DiscretePhaseRetrieval/` | the proof of the main theorem (assembled in the top-level `Main.lean`); `Auxiliary.lean` (Mathlib only) holds the size `‖α‖₁` of a multi-index (`DiscretePR.size`, used throughout `PolyFock/` too) and the binomial-tail lemma shared with `Warren/` and `VCInequality/` |

`Warren` → `Remez` → `VCInequality` → `DiscreteNorming` is the chain feeding Proposition 2.1;
`PolyFock` and `ContinuousPhaseRetrieval` are the two other inputs of `DiscretePhaseRetrieval`.

For the main theorem:

* definitions used by the statement (imports only Mathlib): `Definitions.lean` (top level of this folder)
* comparator (imports only Mathlib, namespace `DiscretePR_Showcase`): `Showcase.lean`; it uses
  `MvPolynomial (Fin d) ℂ`, `EuclideanSpace ℂ (Fin d)`, the direct mixed Hermite expansion, and
  the inner-product STFT with the complex window `h(x)e^{−‖x‖²}`
* the coefficient theorem `DiscretePR.DiscretePhaseRetrieval_coefficients` and the function-space theorem `DiscretePR.DiscretePhaseRetrieval_proved`: `Main.lean` (top level)
* its corollary for the short-time Fourier transform, `DiscretePR.STFTDiscretePhaseRetrieval`: `STFT.lean` (top level; statement in the vocabulary of `Definitions.lean`, as in the paper: window `h(x) e^{−π|x|²}`, Euclidean distance on `ℝ^d × ℝ^d`, separation `√d/10⁷`). It is proved first in the unit scale of the Hermite functions of `ContinuousPhaseRetrieval/` (`STFTDiscretePhaseRetrieval_unit`: window `h(x) e^{−|x|²/2}`, distance `phaseDistUnit` of `DiscretePhaseRetrieval/UnitScale.lean`, separation `4√d/10⁷`) and transferred by the unitary dilation `t = s/√(2π)` of `L²(ℝ^d)` (`DiscretePhaseRetrieval/Dilation.lean`), under which the phase-space map becomes `z = √π (x − iξ)` and separations divide by `√π ≤ 4`; the Fock side (weight `e^{−|z|²}`, main theorem with `4√d/10⁷`) is unchanged
* claim map to the paper: `DiscretePhaseRetrieval/CLAIMS.md`
* the Hermite representation bridge proving `DiscretePhaseRetrieval`: `Check.lean`
* the complex polynomial-window and STFT bridge proving `window_MemLp` and
  `STFTPhaseRetrieval`: `STFTComparatorBridge.lean`; it uses the reusable finite-Hermite-window
  theorem `STFTDiscretePhaseRetrieval_unit_of_finite_window` extracted in `STFT.lean`
* the axiom audit of both bridges and the public theorems: `Check.lean`

Plans for each part are in `plans/`.

There are no import-only root files: modules import the specific files they use. In the root
`lakefile.toml` the library's roots list the top-level modules and the module-name prefixes above;
its `globs` are the submodule globs `Warren.+`, …, so `lake build` compiles every file in this
folder, and any single module can be built by name, e.g. `lake build DiscreteNorming.Main`.
The import closure of `Check.lean` is the whole development except `PolyFock/Check.lean`.

## Building

This folder is a Lake project of its own (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`;
package and library name `DiscretePR`). After cloning, fetch Mathlib's prebuilt files once with
`lake exe cache get`, then:

```bash
lake build                                  # everything in this folder
lake build Check     # axiom audit (prints #print axioms)
```

Expected axioms everywhere: `propext`, `Classical.choice`, `Quot.sound`.

A from-scratch build compiles many modules importing large parts of Mathlib. If a machine with
limited memory reports transient `failed to read file … .olean` errors, limit the parallelism
(for instance `LEAN_NUM_THREADS=4 lake build`) or simply run `lake build` again; it resumes where
it stopped.

## Renaming this folder

As a standalone project nothing depends on the folder name at all.

When built from a parent Lake project instead (a `[[lean_lib]]` with `srcDir` pointing here):

No file in this folder mentions the folder's name; the files refer to each other only by module
name (`import DiscreteNorming.Defs`, …). To move or rename the folder, change `srcDir` of the
library entry in the root `lakefile.toml` — nothing else.
