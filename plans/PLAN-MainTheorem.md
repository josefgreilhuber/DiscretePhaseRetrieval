# Plan: the main theorem (`DiscretePhaseRetrieval/`)

*(Historical: the level-`κ` version. Since 2026-09-17 the main theorem is stated for the mixed-level
spaces `𝓕_g` and named `DiscretePhaseRetrieval_proved`; see `PLAN-MixedLevel-Main.md`.)*

**Status (2026-09-03): executed and complete.** All claims proved (see
`DiscretePhaseRetrieval/CLAIMS.md`); `PolyDiscreteSPR_proved` is sorry-free on the standard axioms
and has the comparator's statement verbatim. Step 1 grew `DiscreteNorming` by 7 lines; Step 2
needed 62 recorded tactic-level patches to compile the copied files under v4.31.0-rc2, no
statement or proof rewritten (`ContinuousPhaseRetrieval/PROVENANCE.md`). Deviations from this plan:
`sep_ge` is `blockSep_ge` with hypothesis `16 d ≤ N`; the kernel bound was proved without the
`m ≤ t` / `m ≥ t` case split (a uniform estimate for all `m ≥ k`); `summable_tail_family` made a
change to `PolyFock` unnecessary.

Target: `DiscretePolyFock.PolyDiscreteSPR` in `DiscretePhaseRetrieval/Showcase.lean`
(statement fixed, currently `sorry`):

```lean
theorem PolyDiscreteSPR (d : ℕ) (hd : 0 < d) (κ : Fin d → ℕ) :
    ∃ S : Set (Fin d → ℂ),
      UniformlyDiscrete (4 * Real.sqrt d / 10 ^ 7) S ∧ PhaseRetrievalSet (PolyFockSpace κ) S
```

This is Theorem 1.1 of `Discrete_PR/paper.pdf`, proved as in Section 4 there, with the
separation `4μ√d/10⁵`, `μ = 1/100`, of the paper's proof. The claim map
`DiscretePhaseRetrieval/CLAIMS.md` lists every substantial claim of the proof with the Lean
declaration that proves it; it is updated as the work lands.

Existing inputs (all in this project, sorry-free): `DiscreteNorming.discrete_norming_explicit`
(Proposition 2.1), `PolyFock.tail_bound` (Lemma 3.1, for `tailKernelDiag L N z` with the
explicit constant `tailConst d L`), `PolyFock.Fock.ev`/`Psihat` (the basis `Φ` as polynomials in
`z, z̄`, `ev_Psihat`), the old `ShowcaseBridge.lean` (`DiscretePolyFock.Φ κ α z = PolyFock.Phi α κ z`).

*(Historical plan; state of 2026-09-07: `PolyFock/` no longer defines a basis of its own — it uses
the comparator's `DiscretePR.HermitePoly`/`DiscretePR.Φ` of `Definitions.lean` directly, so
`hermitePoly_eq_phi`/`Phi_eq_Phi` are gone and only `Phi_eq_ev` remains in `Bridge.lean`.)*

## 0. Two facts that shape the plan

**(a) Proposition 2.1 must be generalized before use.** `V_q^N = span{Φ_{n,q} : |n| ≤ N}`
consists of polynomials in `z` and `z̄` (the paper's `Poly_n(ℂ^d)` means this; Section 4 says
`V_q^N` "consists of polynomials of degree at most `N + |q|`"). `DiscreteNorming` takes
`𝒱 : Submodule ℂ (MvPolynomial (Fin d) ℂ)`, holomorphic polynomials. Nothing in its proof uses
holomorphy (C3 only needs that `|F|² − |G|²` is a real polynomial of degree `≤ 2n`; C4 only needs
the evaluation map to be a ring homomorphism; C3' only needs continuity), so Step 1 below
generalizes it to `𝒱 : Submodule ℂ (PolyFock.Fock.P d)`, `P d = MvPolynomial (Fin d ⊕ Fin d) ℂ`,
evaluated by `PolyFock.Fock.ev` (`Sum.inl i ↦ zᵢ`, `Sum.inr i ↦ z̄ᵢ`). The holomorphic version
becomes a special case and is not needed.

**(b) The last step is imported from the old development.** "`|F|² − |G|²` vanishes
identically, implying `F = λG`" (p. 6) is continuous phase retrieval for the true polyanalytic
Fock space, which the paper cites. Decision (author, 2026-09-02): import it from
`DiscreteFock/PolyFockComplete` (`DiscretePolyFock.exactModulusRecovery` in
`DiscretePolyFock/ContinuousPR.lean`), invoked exactly once, through a bridge file with a clean
statement. Mechanics and constraints are in Step 2 below. The old project's own header calls its
analytic definitions "placeholders" and its lemmas are suffixed `_wip`; the bridge makes the
dependence on it explicit and confined, so it can be audited or replaced later without touching
the rest.

## 1. Step 1: generalize `DiscreteNorming` to polynomials in `z, z̄`

Constraint (author): the library may grow by at most a few lines. Changes, in
`DiscreteNorming/Defs.lean`: `diff F G x := ‖ev (toC x) F‖² − ‖ev (toC x) G‖²` for
`F G : P d = MvPolynomial (Fin d ⊕ Fin d) ℂ` (import `PolyFock.Fock.Basic` for `ev`, which sends
`X (inl i) ↦ zᵢ`, `X (inr i) ↦ z̄ᵢ`); `comb`, `ratComb`, `superlevelFamily`, `ratFamily`,
`𝒱` typed over `P d`. In `ComplexPoly.lean`: `psiVar` gets the second case
`inr i ↦ X ⟨i,_⟩ − C I * X ⟨i+d,_⟩` (`Sum.elim`), `eval_psi` uses `ev`, and `psi F` is then
`aeval` over `Fin d ⊕ Fin d`; `totalDegree_aeval_le` already applies (both substituted
polynomials have degree `≤ 1`). `VCBound.lean`: `Φ x j := ev (toC x) (φ j)`; all other files
change only in types, and every theorem name and shape stays. `DiscreteNorming/CLAIMS.md` gets one
line recording the generalization. One agent; must finish before Step 5 (`BlockNorming`).

## 2. Step 2: the continuous-phase-retrieval bridge

Facts (checked 2026-09-02): the import closure of `DiscretePolyFock/ContinuousPR.lean` in
`DiscreteFock/PolyFockComplete` is 11 files, 16 128 lines (`Defs`, `ContinuousPR`,
`ModulusRecovery/{Definitions, ExactModulusRecovery, ImportedAnalyticInputs, TensorBasis,
Hermite/Definitions, Hermite1Dimd/{Definitions, ImportedAnalyticInputs, ProductBasisAndAnnuli},
Hermitek/TrueLevelBasis}`), importing only Mathlib (no `SardMoreira`). It was built with
Lean/Mathlib v4.30.0; this project uses v4.31.0-rc2. The old `Defs.lean` imports only Mathlib
and **re-declares** the comparator's definitions (`HermitePoly`, `Φ`, `PolyFock`,
`polyanalyticEval`, …) in `namespace DiscretePolyFock`, the namespace of the new
`DiscretePhaseRetrieval/Showcase.lean`. The two cannot be imported into one file.

Plan:
* **2a. Copy the closure.** Copy the 11 files verbatim into a new library
  `ContinuousPhaseRetrieval/` (module prefix `ContinuousPhaseRetrieval`, `lakefile.toml` entry, not
  in `defaultTargets`), keeping their `namespace DiscretePolyFock`. Build under v4.31.0-rc2 and
  patch the minimum needed to compile (deprecations, renamed lemmas); record every patch in
  `ContinuousPhaseRetrieval/PROVENANCE.md` together with the source path and a `diff -r` against the
  original. No proof is rewritten; if a lemma cannot be repaired locally, stop and report.
  (A Lake path-dependency on the old project was considered and rejected: it would rebuild the
  old project in place under the new toolchain and drag in its `SardMoreira` requirement.)
* **2b. Rename the comparator's namespace.** `DiscretePhaseRetrieval/Showcase.lean` changes
  `namespace DiscretePolyFock` to `namespace DiscretePR` (two lines, nothing else); this is the
  only edit to the comparator, needed so the bridge can import both.
* **2c. The bridge** `DiscretePhaseRetrieval/ContinuousPR.lean` imports
  `ContinuousPhaseRetrieval.ContinuousPR` and `DiscretePhaseRetrieval.Showcase`, proves
  `DiscretePR.polyanalyticEval = DiscretePolyFock.polyanalyticEval` (the definitions are
  textually identical: `rfl`), and states

  ```lean
  /-- Continuous phase retrieval (imported). -/
  theorem continuous_phase_retrieval (hd : 0 < d) (κ) (F G : DiscretePR.PolyFock d)
      (h : ∀ z, ‖polyanalyticEval κ F z‖ = ‖polyanalyticEval κ G z‖) :
      ∃ θ : ℂ, ‖θ‖ = 1 ∧ polyanalyticEval κ F = θ • polyanalyticEval κ G
  ```

  proved by the single invocation `DiscretePolyFock.exactModulusRecovery hd κ`. This is the
  only place the earlier development is used; `Main.lean` uses `continuous_phase_retrieval` once.
* `Check.lean` prints the axioms of `PolyDiscreteSPR_proved`; expected: the three standard
  axioms (the earlier proof is sorry-free by its own audit), to be confirmed, since this is the
  first time it is checked under this toolchain.

## 3. The objects (`DiscretePhaseRetrieval/Defs.lean`, `Bridge.lean`)

Notation: `L := ∑ i, κ i` (the paper's `|q|`), `|α| := ∑ i, α i`, `μ := 1/100` (a named
constant `mu`), points `z : Fin d → ℂ` (comparator) and `x : Pt d = EuclideanSpace ℝ (Fin (2d))`
(DiscreteNorming), related by `toC` and its inverse `ofC`; `‖z‖₂ := euclideanDist z 0 = PolyFock.rad z`.

```lean
def ofC (z : Fin d → ℂ) : Pt d                       -- x_j = Re z_j, x_{j+d} = Im z_j
theorem toC_ofC, ofC_toC, euclideanDist_eq_dist : euclideanDist z w = dist (ofC z) (ofC w)
theorem rad_eq : PolyFock.rad z = euclideanDist z 0

theorem Phi_eq_ev : Φ κ α z = PolyFock.Fock.ev z (Psihat α κ)      -- basis = polynomial (index swap)

def truncate (N : ℕ) (F : PolyFock d) : PolyFock d   -- coefficients with |α| ≤ N, else 0
theorem norm_truncate_le : ‖truncate N F‖ ≤ ‖F‖
def truncPoly (κ) (N) (F) : P d := ∑ α with |α| ≤ N, C (F α) * Psihat α κ
theorem eval_truncate : polyanalyticEval κ (truncate N F) z = ev z (truncPoly κ N F)   -- F_N ∈ V_q^N
def VqN (κ) (N) : Submodule ℂ (P d) := span {Psihat α κ : |α| ≤ N}
theorem truncPoly_mem : truncPoly κ N F ∈ VqN κ N

def annulus (d) (μ : ℝ) (N : ℕ) : Set (Pt d) := ball 0 (μ√N) \ ball 0 (μ√N / 8)   -- A_{N,μ}
```

## 4. Claims (each its own Lean statement)

Files under `DiscretePhaseRetrieval/`. "Paper" column: where the claim is made.

| # | claim | Lean statement (readable form) | file |
|---|---|---|---|
| P1 | `Φ_{n,q}` is a polynomial in `z, z̄` of degree `|n| + |q|` | `totalDegree_Psihat_le : (Psihat α κ).totalDegree ≤ |α| + |κ|` (from `Hpoly i m n` of degree `≤ m + n`) | `Polynomials.lean` |
| P2 | `V_q^N` consists of polynomials of degree `≤ N + |q|` | `totalDegree_le_of_mem_VqN : F ∈ VqN κ N → F.totalDegree ≤ N + L` | `Polynomials.lean` |
| P3 | `dim V_q^N = C(N+d, d)` (only `1 ≤ dim ≤ C(N+d,d)` is needed: the separation of Prop. 2.1 is monotone in the dimension) | `one_le_finrank_VqN`, `finrank_VqN_le : finrank (VqN κ N) ≤ (N + d).choose d` (needs `#{α : Fin d → ℕ | |α| ≤ N} = C(N+d, d)`, stars and bars; Mathlib `Finset.card_sym` / `Sym` ↔ finsupp) | `Polynomials.lean` |
| P4 | `C(N+d,d) ≤ (N+d)^d e^d / d^d` | `choose_le_pow_mul_exp` | `Polynomials.lean` |
| W | the evaluation series converges absolutely (so `polyanalyticEval` is the genuine sum) | `summable_Phi_sq : Summable (fun α ↦ ‖Φ κ α z‖²)`, `summable_eval : Summable (fun α ↦ F α * Φ κ α z)` (Cauchy–Schwarz in `ℓ²`) | `Coefficients.lean` |
| K | reproducing-kernel bound `|F(z)| ≤ C_{|q|}(1+|z|)^{|q|} e^{|z|²/2} ‖F‖` (paper p. 6; ours has a larger polynomial factor, which is immaterial) | `sum_sq_phi_le : ∃ C, ∀ w, ∑' m, ‖phi m k w‖² ≤ C (1+‖w‖²)^{4k} e^{‖w‖²}` (one variable; split `m ≤ ‖w‖²`, where `r! C(m,r) ≤ m^r ≤ ‖w‖^{2r}` gives `‖φ_{m,k}‖ ≤ C ‖w‖^{m+k}/√(m!)`, and `m ≥ ‖w‖²`, where `PolyFock.sq_norm_phi_le` applies); `kernel_bound : ∃ C, ∀ z, ∑' α, ‖Φ κ α z‖² ≤ C (1+‖z‖₂²)^{4L} e^{‖z‖₂²}` (product); `eval_le : ‖polyanalyticEval κ F z‖² ≤ ‖F‖² · ∑' α, ‖Φ κ α z‖²` | `KernelBound.lean` |
| T | Lemma 3.1 applied to `F − F_N`: `‖F − F_N‖_{L∞(B_{μ√N})} ≤ ‖F‖ ‖K_{L,N}(z,·)‖` | `tail_eval_le : ‖eval F z − eval (truncate N F) z‖² ≤ ‖F‖² · ∑'_{|α|>N} ‖Φ κ α z‖²`; `tail_le_tailKernelDiag : ∑'_{|α|>N} ‖Φ κ α z‖² ≤ PolyFock.tailKernelDiag L N z` (the index set of `tailKernelDiag` contains `{(α, κ)}`); `truncation_error` = the two with `PolyFock.tail_bound` (`3L ≤ N`, `L+9 ≤ N`, `e‖z‖₂² < N`) | `TailBound.lean` |
| E1 | `||z|² − |w|²| ≤ 2 max(|z|,|w|) |z − w|` | `abs_sq_sub_sq_le` | `TailBound.lean` |
| E2 | `‖|F|² − |F_N|²‖_{L∞(B_{μ√N})} ≤ C_{μ,|q|} N^{|q|} exp((μ²/2 + 1/2 + log μ) N) ‖F‖²` (p. 6, with `(eμ²)^{N/2} = e^{(1/2 + log μ)N}`) | `modulus_error : ∃ C c, ∀ N ≥ N₁, ∀ F z, ‖z‖₂ ≤ μ√N → |‖eval F z‖² − ‖eval (truncate N F) z‖²| ≤ C N^c exp((μ²/2 + 1/2 + log μ) N) ‖F‖²` (from K, T, E1; `N₁ := max (3L) (L+9)`) | `TailBound.lean` |
| A1 | `Ω = A_{N,μ}` is bounded, measurable, of positive measure; `Ω̂ = B̄_{μ√N}` | `annulus_measurable`, `annulus_bounded`, `annulus_vol_pos`, `hull_annulus_subset_closedBall`, `ball_subset_hull_annulus` (for `x` in the inner ball: midpoint of `x ± t u`, `u ⟂ x` a unit vector, both in the annulus; needs `2d ≥ 2`) | `Annulus.lean` |
| A2 | `|Ω̂ \ Ω| = 2^{−6d}|Ω̂| ≤ 2^{−4d−2}|Ω̂|` | `annulus_hull_defect : vol (hull Ω \ Ω) ≤ (1/2)^{4d+2} vol (hull Ω)` (`vol (ball r) = r^{2d}|B^{2d}|`, spheres are null) | `Annulus.lean` |
| A3 | `|Ω|/|B^{2d}| ≥ (63/64) μ^{2d} N^d` | `annulus_vol_ge` | `Annulus.lean` |
| B1 | Proposition 2.1 on the block: a `δ`-separated `S_{N,μ} ⊆ A_{N,μ}` with (2): `‖|F|²−|G|²‖_{L∞(B_{μ√N})} ≤ e^{4(N+|q|)} ‖|F|²−|G|²‖_{L∞(S_{N,μ})}` for `F, G ∈ V_q^N` | `block_norming : ∃ S : Finset (Pt d), ↑S ⊆ annulus ∧ (∀ x y ∈ S, x ≠ y → sep N ≤ dist x y) ∧ ∀ F ∈ VqN κ N, ∀ G ∈ VqN κ N, ∀ x, ‖x‖ < μ√N → ∃ y ∈ S, |diff F G x| ≤ e^{4(N+L)} |diff F G y|` where `sep N := deltaPaper d (annulus) · (finrank (VqN κ N))^{−1/(2d)}` (`discrete_norming_explicit` + A1–A3, P2, P3) | `BlockNorming.lean` |
| B2 | `δ ≥ (μ√N/16)(63/64/(3·10⁵(1+d)))^{1/(2d)} C(N+d,d)^{−1/(2d)} ≥ 4μ√d/10⁵` for large `N` (p. 5–6) | `sep_ge : N₀ ≤ N → 4 μ √d / 10⁵ ≤ sep N` (A3, P3, P4; candidate `N₀ := 3`, the binding case is `d = 1`; verify numerically, raise `N₀` if needed) | `BlockNorming.lean` |
| C | the combined block estimate (p. 6): `‖|F_N|²−|G_N|²‖_{L∞(B_{μ√N})} ≤ e^{4(N+|q|)} ‖|F|²−|G|²‖_{L∞(S_{N,μ})} + C N^{|q|} exp((μ²/2 + 9/2 + log μ) N) max(‖F‖,‖G‖)²` | `block_estimate : ∀ x, ‖x‖₂ < μ√N → ∃ y ∈ S_N, |‖F_N(x)‖² − ‖G_N(x)‖²| ≤ e^{4(N+L)} |‖F(y)‖² − ‖G(y)‖²| + C N^c exp((μ²/2 + 9/2 + log μ) N) max(‖F‖,‖G‖)²` (triangle inequality on `S_N ⊆ B_{μ√N}`, E2 at `y`, B1 for `F_N, G_N`) | `BlockEstimate.lean` |
| X | `μ = 1/100`: `μ²/2 + 9/2 + log μ ≤ −1/10` | `exponent_neg` (needs `log 100 ≥ 4.6`) | `BlockEstimate.lean` |
| L1 | `F_N → F` pointwise (uniformly on compacts is not needed) | `tendsto_truncate : Tendsto (fun N ↦ eval (truncate N F) z) atTop (𝓝 (eval F z))` (tail of an absolutely convergent series) | `Coefficients.lean` |
| L2 | from `‖|F_{N_j}|² − |G_{N_j}|²‖_{L∞(B_{μ√N_j})} ≤ ε_j → 0` conclude `|F| = |G|` on `ℂ^d` | `norm_eq_of_blocks : (N_j → ∞) → (∀ j z, ‖z‖₂ < μ√N_j → |‖F_{N_j} z‖² − ‖G_{N_j} z‖²| ≤ ε_j) → (ε → 0) → ∀ z, ‖F z‖ = ‖G z‖` | `Limit.lean` |
| S1 | blocks are far apart: `N' ≥ 100N ⇒ dist(A_{N,μ}, A_{N',μ}) ≥ μ√N/4` | `annuli_far` | `Limit.lean` |
| S2 | the union of separated blocks on a rapidly increasing sequence is separated | `union_separated : (∀ j, S j ⊆ annulus μ (N j)) → (∀ j, S j is δ-separated) → (∀ j, 100 N j ≤ N (j+1)) → μ√(N 0)/4 ≥ δ → ⋃ j, S j is δ-separated` | `Limit.lean` |
| CPR | equal moduli everywhere ⇒ equal up to a unimodular constant (cited in the paper; **imported**, Step 2) | `continuous_phase_retrieval : (∀ z, ‖eval κ F z‖ = ‖eval κ G z‖) → ∃ θ, ‖θ‖ = 1 ∧ eval κ F = θ • eval κ G` , proved by one call of the earlier development's `DiscretePolyFock.exactModulusRecovery` | `ContinuousPR.lean` |
| M | **Theorem 1.1** | `PolyDiscreteSPR_proved` (same statement as `Showcase.lean`; the only use of `continuous_phase_retrieval`) | `Main.lean` |

### The assembly (`Main.lean`) and what stays local to it

Given `d ≥ 1`, `κ`. Put `L := |κ|`, `N₁ := max (3L) (L+9)` (T, E2), `N₀` from B2, and choose
`N_* := max N₀ N₁ d`, `N_j := N_* · 100^j` (so `N_{j+1} = 100 N_j`, `N_j → ∞`, and
`μ√N_0/4 ≥ 4μ√d/10⁵` since `N_0 ≥ d`). For each `j` take `S_j` from B1 at `N_j` and put
`S := ⋃ j, toC '' S_j : Set (Fin d → ℂ)`.
* Separation: within a block by B1+B2 (`toC` preserves Euclidean distance, `Bridge.lean`);
  across blocks by S1, S2. The sequence, `N_*`, and the `min` of the two separations occur
  only here.
* Phase retrieval: for `f, g ∈ PolyFockSpace κ` get coefficient vectors `F, G` with
  `f = eval F`, `g = eval G`; `|f| = |g|` on `S` means `|F| = |G|` on every `S_j`; C at `N_j`
  with X gives `|‖F_{N_j}(x)‖² − ‖G_{N_j}(x)‖²| ≤ C N_j^c e^{−N_j/10} max(‖F‖,‖G‖)² =: ε_j → 0`
  on `B_{μ√N_j}`; L2 gives `|F| = |G|` on `ℂ^d`; CPR gives `θ`; hence `f = θ • g`.
* The "WLOG `‖F‖, ‖G‖ ≤ 1`" of the paper is replaced by carrying `max(‖F‖,‖G‖)²`.

### Checks

`Check.lean`: `example : <statement of Showcase.PolyDiscreteSPR> := PolyDiscreteSPR_proved`
(verifies the proved statement is syntactically the comparator's) and `#print axioms` of
`PolyDiscreteSPR_proved` (expected: `propext`, `Classical.choice`, `Quot.sound`). The proof library imports `DiscretePhaseRetrieval.Showcase` for the
definitions and never uses the `sorry`'d `PolyDiscreteSPR` itself.

## 5. Work split (Opus agents)

* Step 1 (one agent, first): generalize `DiscreteNorming`; rebuild; update its `CLAIMS.md`.
* Step 2 (one agent, in parallel with Step 1): copy the 11-file closure, compile under
  v4.31.0-rc2 with minimal recorded patches, write the bridge `ContinuousPR.lean`.
* Wave 1 (independent, after the sorry'd interface compiles): `Bridge`+`Defs` (P0), `Polynomials`
  (P1–P4), `Coefficients` (W, L1), `KernelBound` (K), `TailBound` (T, E1, E2; uses K's
  statements), `Annulus` (A1–A3), `Limit` (L2, S1, S2), `BlockEstimate`'s `exponent_neg` (X).
* Wave 2: `BlockNorming` (B1, B2; needs Step 1 and `Annulus`, `Polynomials` statements),
  `BlockEstimate` (C), `Main` (M).
* Before wave 1, I rename the comparator's namespace (2b), write `Defs.lean`, the interface
  statements of every file, `CLAIMS.md`, add `DiscretePhaseRetrieval` and `ContinuousPhaseRetrieval`
  to `lakefile.toml`, and check numerically `N₀` (B2), the exponent (X), and that
  `4μ√d/10⁵ = 4√d/10⁷` matches `Showcase.lean`.

Expected size ≈ 3000 new lines plus the 16 128 copied ones. Risks: Step 2a (API drift
v4.30.0 → v4.31.0-rc2 across 16 k lines, unknown until tried; a trial build is the first thing
the Step-2 agent does); P3's count `C(N+d,d)` (must be exact, or the `√d` in the
separation is lost); A1's convex-hull inclusion; K's one-variable estimate (the paper cites the
kernel bound without proof; the elementary route above gives the exponent `e^{|z|²}` exactly,
only the polynomial factor is cruder). None affects the final constants.
