# Plan: Proposition 2.1, the discrete norming inequality (`DiscreteNorming/`)

**Status (2026-09-02): done.** All claims C1–C15 proved, sorry-free, standard axioms; see
`DiscreteNorming/CLAIMS.md`. Two interface adjustments during execution: `exists_spanning` needs
`1 ≤ N` (the statement is false for `N = 0`), and `superlevel_measure_ge_T` does not actually
need the maximality hypothesis (kept for readability).

Target: Proposition 2.1 of `Discrete_PR/paper.pdf` (p. 2–4), including Lemma 2.2. The claim map
`DiscreteNorming/CLAIMS.md` lists every substantial claim of the proof with the Lean declaration
that proves it; it is updated as the work lands.

Inputs already formalised: `Remez.brudnyi_ganzburg` (multivariate Remez, Chebyshev form, on
`Fin m → ℝ`), `SignPatterns.sign_patterns_warren` (Warren's bound
`#patterns ≤ (4e·max 2 d·(m+1)/n)^n` for `m` polynomials of degree `≤ d` in `n` variables),
`VCInequality.relative_deviation_vc` (relative VC inequality, constant 8, Sauer–Shelah form).

## 1. The statement in Lean

Setting. `d ≥ 1`; points of `ℂ^d` are `x : EuclideanSpace ℝ (Fin (2*d))` with
`toC x : Fin d → ℂ := fun j ↦ ⟨x j, x (j + d)⟩`; Lebesgue measure `volume`; Euclidean `dist`.
`Ω` is measurable, bounded, of positive measure; `hull Ω := closure (convexHull ℝ Ω)` (compact,
convex, `Ω ⊆ hull Ω`; its boundary is null by `Convex.addHaar_frontier`, so this is the paper's
`Ω̂` up to a null set). `𝒱 : Submodule ℂ (MvPolynomial (Fin d) ℂ)` with every element of total
degree `≤ n` and `finrank 𝒱 = N ≥ 1`. For `F G : MvPolynomial (Fin d) ℂ` write
`P F G x := ‖eval (toC x) F‖² − ‖eval (toC x) G‖²` (a real number).
`|B^{2d}| := (volume (ball (0 : EuclideanSpace ℝ (Fin (2*d))) 1)).toReal`.

```lean
/-- Proposition 2.1, explicit constants (`C_norm = 4`, `δ` as in the paper). -/
theorem discrete_norming_explicit (hd : 1 ≤ d) (hΩ : MeasurableSet Ω) (hb : IsBounded Ω)
    (hpos : 0 < volume Ω)
    (hhull : volume (hull Ω \ Ω) ≤ 2⁻¹ ^ (4 * d + 2) * volume (hull Ω))
    (h𝒱deg : ∀ F ∈ 𝒱, F.totalDegree ≤ n) (h𝒱dim : finrank ℂ 𝒱 = N) (hN : 1 ≤ N) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin (2 * d))), ↑S ⊆ Ω ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        (1/16) * ((volume Ω).toReal / |B^{2d}| / (3 * 10^5 * (1 + d))) ^ (1/(2*d : ℝ))
          * (N : ℝ) ^ (-(1 / (2 * d : ℝ))) ≤ dist x y) ∧
      ∀ F ∈ 𝒱, ∀ G ∈ 𝒱, ∀ x ∈ hull Ω, ∃ y ∈ S, |P F G x| ≤ Real.exp (4 * n) * |P F G y|

/-- Proposition 2.1, general form: constants depending only on `Ω` (and `d`). -/
theorem discrete_norming (hd : 1 ≤ d) (hΩ : MeasurableSet Ω) (hb : IsBounded Ω)
    (hpos : 0 < volume Ω) :
    ∃ Cnorm δ : ℝ, 0 < δ ∧ ∀ n N 𝒱, (∀ F ∈ 𝒱, F.totalDegree ≤ n) → finrank ℂ 𝒱 = N → 1 ≤ N →
      ∃ S : Finset _, ↑S ⊆ Ω ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ * (N : ℝ) ^ (-(1/(2*d : ℝ))) ≤ dist x y) ∧
        ∀ F ∈ 𝒱, ∀ G ∈ 𝒱, ∀ x ∈ hull Ω, ∃ y ∈ S, |P F G x| ≤ Real.exp (Cnorm * n) * |P F G y|
```

`‖·‖_{L∞(S)}` is expressed as `∃ y ∈ S, … ≤ e^{Cn}|P y|`, which avoids a `sup` over a possibly
empty finset and reads the same way. Both theorems are corollaries of one parametric core
theorem (§3, claim C13) in which the Remez constant is kept in Chebyshev form
`T_{2n}((1+β)/(1−β))`, `β = θ^{1/(2d)}`, `θ = (t|Ω| + |Ω̂ \ Ω|)/|Ω̂|`; the general form takes
`Cnorm = 2·arcosh((1+β)/(1−β))` (any `θ < 1` works), the explicit form uses `θ ≤ 2^{−4d}`
⇒ `T_{2n} ≤ e^{8n√β} ≤ e^{4n}`. Note the paper's proof only covers the general claim when
`|Ω̂ \ Ω| < 2^{−4d}|Ω̂|`; the Chebyshev form of the Lean Remez theorem removes that restriction.

## 2. Constants (decided 2026-09-02)

* Lemma 2.2 is two-sided in the paper (`ℱ = {{z ∈ Ω : ||F|² − |G|²| ≥ τ}}`, `𝒢_N` likewise), the
  polynomials `p_ℓ = ||Σa y|² − |Σb y|²|² − 1` are quartic in `(Re a, Im a, Re b, Im b)`, and the
  bound `36N` is correct; it is formalised exactly so. (Lean's Warren bound has `(K+1)` in place of
  `K`; `2^x > 16e(x + 1/4)` for `x ≥ 9` still gives `K ≤ 36N`.)
* The sample size stays the paper's `M = ⌊(3000 + 1200|log t|)N/t⌋` with `V = 36N`, `ε = √t/2`,
  under the extra hypothesis `t ≤ 1/8` (numerically verified: the bound `≤ 1/100` holds for all
  `t ≤ 1/8` and `N ≥ 1`, and fails for `t ≥ 1/4`). The hypothesis `t ≤ 1/8` is inserted wherever
  needed; the paper will be amended.
* p. 4: `½M` and `⅓M` are `(t/2)M` and `(t/3)M`.

## 3. Claims and their Lean statements (files under `DiscreteNorming/`)

Notation: `m = 2d`, `k = 2n`, `V ⊇ Ω` compact convex (instantiated with `hull Ω`).

| # | claim (paper) | Lean statement (readable form) | file |
|---|---|---|---|
| C1 | Remez, exponential form: `‖p‖_V ≤ exp(4k(|V\ω|/|V|)^{1/(2m)}) ‖p‖_ω` when `|V\ω| ≤ 2^{−2m}|V|` | `T_eval_le_exp : 0 ≤ β ≤ 1/4 → (T ℝ k).eval ((1+β)/(1−β)) ≤ exp (4 k √β)` (via `T_k(cosh u) = cosh(ku)`, new), and `remez_exp : … |eval x p| ≤ exp (4 k λ^{1/(2m)}) K` for `λ = |V\E|/|V| ≤ 2^{−2m}`, `|p| ≤ K` on `E` | `Chebyshev.lean` |
| C2 | superlevel set: `|{z ∈ Ω : |P(z)| ≥ exp(−4kθ^{1/(2m)}) ‖P‖_V}| ≥ t|Ω|`, `θ = (t|Ω| + |V\Ω|)/|V| ≤ 2^{−2m}` | `superlevel_measure_ge` (proof by contradiction with C1 applied to `E = V \ (Ω \ S)`); Chebyshev-form variant `superlevel_measure_ge_T` for any `θ < 1` | `Superlevel.lean` |
| C3 | `|F|² − |G|²` is a real polynomial of degree `≤ 2n` in `2d` real variables | `exists_realPoly : ∃ Q : MvPolynomial (Fin (2d)) ℝ, Q.totalDegree ≤ 2n ∧ ∀ x, eval x Q = P F G x` (real/imaginary parts of `aeval (X_j ↦ Y_j + i Y_{d+j}) F`) | `ComplexPoly.lean` |
| C3' | uniform approximation on bounded `Ω` by rational coefficients | `exists_rat_approx : ∀ η > 0, ∃ a' b' : Fin N → ℚ × ℚ, ∀ x ∈ Ω, |P_{a,b} x − P_{a',b'} x| ≤ η` (basis `φ` of `𝒱`, `P_{a,b} = |Σ a_j φ_j|² − |Σ b_j φ_j|²`) | `ComplexPoly.lean` |
| C4a | VC dimension is non-increasing under pull-back | `VCDimLE_preimage : (∀ B ∈ ℱ, ∃ X ∈ 𝒢, B = Φ ⁻¹' X) → VCDimLE 𝒢 V → VCDimLE ℱ V` | `VCBound.lean` |
| C4b | shattering `K` points ⇒ all `2^K` strict sign patterns of the `2K` polynomials `q_ℓ ∓ 1` occur (scaling trick) | `shatter_signPatterns : … 2^K ≤ (strictSignPatterns p).ncard` (the `K` quartic polynomials `p_ℓ`) | `VCBound.lean` |
| C4c | Warren ⇒ `K ≤ 36N` | `card_le_of_signPatterns : 2^K ≤ (4e(K+1)/N)^{4N} → K ≤ 36 N` (real-analytic: `2^x > 16e(x + 1/4)` for `x ≥ 9`) | `VCBound.lean` |
| C4 | **Lemma 2.2**: the family `{{z ∈ Ω : |P F G z| ≥ τ} : F, G ∈ 𝒱, τ > 0}` has VC dimension `≤ 36N` | `vcDim_superlevel_family : VCDimLE (superlevelFamily Ω 𝒱) (36 * N)` | `VCBound.lean` |
| C5 | relative VC inequality + Sauer–Shelah | existing `VCInequality.relative_deviation_vc` | — |
| C6 | choice of `M`: `8 (2eM/V)^V exp(−Mε²/4) ≤ 1/100` with `ε = √t/2`, `V = 36N`, `M = ⌊(3000 + 1200|log t|)N/t⌋`, `0 < t ≤ 1/8` | `sample_size_bound` (pure real arithmetic) | `Sampling.lean` |
| C7 | off the bad event, every family set of measure `≥ t|Ω|` contains `≥ (t/2)M` sample points | `count_ge_of_not_bad : x ∉ badEvent μ A M (√t/2) → t ≤ μ (A i) → t/2 * M ≤ count x (A i)` | `Sampling.lean` |
| C7' | the countable subfamily: rational coefficients w.r.t. a basis of `𝒱`, rational threshold; it is countable, measurable, contained in the family of C4 | `ratFamily`, `ratFamily_subset`, `measurableSet_ratFamily` | `Sampling.lean` |
| C8 | two independent uniform points of `Ω` are `r`-close with probability `≤ r^{2d}|B^{2d}|/|Ω|`; expected number of `r`-close pairs `≤ (M(M−1)/2) r^{2d}|B^{2d}|/|Ω|` | `prob_close_le`, `expected_closePairs_le` (product measure, pair marginal, `EuclideanSpace.volume_ball`) | `Separation.lean` |
| C9 | with `δ = (tN|Ω|/(2M|B^{2d}|))^{1/(2d)}`, `r = δN^{−1/(2d)}`: expected number of close pairs `≤ (t/4)M`; Markov: `P[#pairs ≤ (t/3)M] ≥ 1/4` | `closePairs_markov` | `Separation.lean` |
| C10 | a sample in the good event (prob `≥ 99/100`) with `≤ (t/3)M` close pairs exists (`1/4 > 1/100`) | `exists_good_sample` | `Separation.lean` |
| C11 | deleting one point of each close pair leaves an `r`-separated set meeting every set that had `≥ (t/2)M > (t/3)M` sample points | `exists_separated_subsample` | `Separation.lean` |
| C12 | from "every rational-family set of measure `≥ t|Ω|` meets `S`" to the norming inequality for **all** `F, G ∈ 𝒱`: approximate `P` by rational `P'` within `ηK`, threshold `τ ∈ ℚ ∩ [(c'−η)K, c'K]` with `c' + η ≤ c_t`; then `S` meets `{|P'| ≥ τ} ⊇ {|P| ≥ (c'+η)K}` (measure `≥ t|Ω|` by C2), giving `sup_S |P| ≥ (c' − 2η)K`; let `c' ↑ c_t`, `η ↓ 0` | `norming_of_hits` (no loss of constants: `S` is fixed, the limit is over `c', η`) | `Density.lean` |
| C13 | **core theorem** (parametric in `t`): `0 < t ≤ 1/8`, `θ < 1` ⇒ `∃ S ⊆ Ω` finite, `δ(t)N^{−1/(2d)}`-separated, with `|P(x)| ≤ T_{2n}((1+β)/(1−β)) · |P(y)|` for some `y ∈ S`, all `F, G ∈ 𝒱`, `x ∈ V` | `discrete_norming_core` | `Main.lean` |
| C14 | explicit constants: `t = 2^{−4d−1}` ⇒ `θ ≤ 2^{−4d}`, `T_{2n} ≤ e^{4n}`, `δ(t) ≥ (1/16)(|Ω|/|B^{2d}|/(3·10^5(1+d)))^{1/(2d)}` | `discrete_norming_explicit` | `Main.lean` |
| C15 | general constants | `discrete_norming` | `Main.lean` |

## 4. Work split (Opus agents, one file each, fixed sorry'd interface first)

Wave 1 (independent): `Chebyshev` (C1), `Superlevel` (C2, uses C1's statement),
`ComplexPoly` (C3, C3'), `VCBound` (C4a–C4), `Sampling` (C6, C7, C7'), `Separation` (C8–C11).
Wave 2: `Density` (C12), `Main` (C13–C15). Before wave 1: I write `Defs.lean` (the objects
above: `toC`, `P`, `hull`, `superlevelFamily`, `ratFamily`, the uniform measure `volume[|Ω]`),
all interface statements, `CLAIMS.md`, and run the numeric check fixing the constants of C6/C9.
Expected size 3000–4000 lines. Uniform probability on `Ω` is `ProbabilityTheory.cond volume Ω`
(`cond_isProbabilityMeasure`); the transport `EuclideanSpace ℝ (Fin m) ↔ (Fin m → ℝ)` for Remez
is the continuous linear, measure-preserving `EuclideanSpace.equiv`.
