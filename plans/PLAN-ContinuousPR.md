# Plan: continuous phase retrieval by hand (`Complexification/`, `ContinuousPhaseRetrieval_PolyFock`)

Goal: replace the earlier development `ContinuousPhaseRetrieval` behind `DiscretePhaseRetrieval/ContinuousPR.lean`
by a direct proof of

> `|F(z)| = |G(z)|` for all `z ∈ ℂ^d`, `F, G ∈ 𝓕_κ` (coefficient model `lp 2`) ⟹ `F = θ G`, `|θ| = 1`,

along the outline: (1) identity theorems for entire functions vanishing on totally real subspaces,
(2) complexify `P(z, z̄) = |F|² − |G|²` to `P_ℂ(z, ζ)`, conclude `P_ℂ ≡ 0`, compare coefficients.
**Not yet executed.** Section 4 records where the outline stops being a proof and what the options
are; that decision comes before execution.

## 0. What Mathlib provides (checked against the project's Mathlib, v4.31.0-rc2)

| need | Mathlib | remark |
|---|---|---|
| (1.1) identity theorem, one variable | `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, `…eqOn_of_preconnected_of_frequently_eq` (`Analysis/Analytic/IsolatedZeros.lean`) | zeros accumulating at a point of a preconnected domain force `f = 0`; `ℝ ⊂ ℂ` accumulates at `0` |
| entire ⟹ analytic, one variable | `Complex.analyticOnNhd_iff_differentiableOn` (`Analysis/Complex/CauchyIntegral.lean`) | **only for `f : ℂ → E`**; Mathlib has no several-variable "holomorphic ⟹ analytic" (no Osgood/Hartogs) |
| identity theorem, several variables | `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` (`Analysis/Analytic/Uniqueness.lean`) | needs vanishing on an **open** set, so it does not give (1.2) directly |
| entire functions from series | `differentiableOn_tsum_of_summable_norm`, `hasSum_deriv_of_summable_norm` (`Analysis/Complex/LocallyUniformLimit.lean`) | one variable; enough for everything below |
| power series with given scalar coefficients | `FormalMultilinearSeries.ofScalars` and its radius lemmas (`Analysis/Analytic/OfScalars.lean`), `HasFPowerSeriesAt` uniqueness (`Analysis/Analytic/Basic.lean`) | coefficient extraction from a vanishing one-variable series |
| polynomials vanishing as functions | `MvPolynomial.funext` | finite-support case of step (2) |
| `m` independent vectors span `ℂ^m` | `LinearIndependent.span_eq_top_of_card_eq_finrank` | for (1.3) |
| Laguerre polynomials | **absent** (only `Polynomial.hermite`) | relevant to Section 4 |

Design consequence: work with a class of functions on `ℂ^m` for which only **one-variable**
analyticity is ever used.

## 1. Folder `Complexification/` (step 1)

`Complexification/Defs.lean`

```lean
/-- entire along every complex line: the class of functions on `ℂ^m` we use -/
def EntireAlongLines {m : ℕ} (f : (Fin m → ℂ) → ℂ) : Prop :=
  ∀ a v : Fin m → ℂ, Differentiable ℂ (fun t : ℂ ↦ f (a + t • v))
```

Closure lemmas: `EntireAlongLines.add / sub / mul / const / comp_linear`, and `of_tsum` for a
series of polynomials converging locally uniformly (via `differentiableOn_tsum_of_summable_norm`
on balls). Every function of step (2) is such a series, so the class contains them; it is closed
under linear changes of variables, which (1.3) needs. Joint analyticity (`AnalyticOnNhd` on
`Fin m → ℂ`) is never needed and would be expensive (Section 0).

`Complexification/OneVariable.lean`: (1.1)

```lean
theorem eq_zero_of_real_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ x : ℝ, f x = 0) : f = 0
```
Proof: `analyticOnNhd_iff_differentiableOn isOpen_univ`, then
`eqOn_zero_of_preconnected_of_frequently_eq_zero` at `0`, where the real zeros `1/(n+1)` accumulate.

`Complexification/Several.lean`: (1.2)

```lean
theorem eq_zero_of_real_zero_pi {n : ℕ} {f : (Fin n → ℂ) → ℂ} (hf : EntireAlongLines f)
    (h : ∀ x : Fin n → ℝ, f (fun i ↦ (x i : ℂ)) = 0) : f = 0
```
**Path: induction on the number of complexified coordinates, with change of base point.**
Claim `P k`: `f z = 0` whenever `z i ∈ ℝ` for all `i ≥ k`. `P 0` is the hypothesis. For `P (k+1)`:
given `z` real in the coordinates `≥ k+1`, the one-variable function `t ↦ f (update z k t)` is
entire (it is `f` along the line through `update z k 0` in direction `e_k`) and vanishes for real
`t` by `P k`, so by (1.1) it vanishes at `t = z k`. `P n` is the claim. Only (1.1) and
`Function.update` are used; no several-variable analyticity, no Hartogs.

`Complexification/TotallyReal.lean`: (1.3)

```lean
theorem eq_zero_of_totallyReal_zero {m : ℕ} {f : (Fin m → ℂ) → ℂ} (hf : EntireAlongLines f)
    (v : Fin m → (Fin m → ℂ)) (hv : LinearIndependent ℂ v)
    (h : ∀ x : Fin m → ℝ, f (∑ i, (x i : ℂ) • v i) = 0) : f = 0
```
Proof: `T x = ∑ x i • v i` is `ℂ`-linear; `f ∘ T` is entire along lines, vanishes on `ℝ^m`, so
`f ∘ T = 0` by (1.2); `T` is surjective (`span_eq_top_of_card_eq_finrank`), so `f = 0`.

`Complexification/Conjugate.lean`: (1.4), in the form step (2) uses

```lean
/-- `ℂ^d × ℂ^d ≅ ℂ^{2d}`; `{(z, z̄)}` is the real span of the `2d` `ℂ`-independent vectors
    `(e_j, e_j)`, `(i e_j, −i e_j)`. -/
theorem eq_zero_of_conj_diag_zero {d : ℕ} {f : (Fin d → ℂ) → (Fin d → ℂ) → ℂ}
    (hf : EntireAlongLines (fun p : Fin (2*d) → ℂ ↦
            f (fun j ↦ p (Fin.castAdd d j)) (fun j ↦ p (Fin.natAdd d j))))
    (h : ∀ z : Fin d → ℂ, f z (star ∘ z) = 0) : ∀ z ζ, f z ζ = 0
```
The "entire real-analytic function of `z`" is the restriction `z ↦ f z z̄` and `f` is its
complexification. In step (2) the complexified function is defined first and the original is its
restriction, so (1.4) is this corollary of (1.3), not a construction.

## 2. File `ContinuousPhaseRetrieval_PolyFock.lean` (step 2, setting)

Reuses the algebraic layer `PolyFock.Fock` (`P d = MvPolynomial (Fin d ⊕ Fin d) ℂ`, `Psihat`,
`ev z = aeval (Sum.elim z (conj ∘ z))`, `Hpoly` with real coefficients).

```lean
/-- evaluation with `z` and `ζ` independent -/
def evC (z ζ : Fin d → ℂ) : P d →ₐ[ℂ] ℂ := MvPolynomial.aeval (Sum.elim z ζ)
lemma evC_conj (z) : evC z (star ∘ z) = ev z
lemma conj_evC (z ζ) (p : P d) (hp : p has real coefficients) :
    star (evC z ζ p) = evC (star ∘ ζ) (star ∘ z) p

/-- the complexified `F ∈ 𝓕_κ`, and the complexified conjugate -/
def Fc  (κ) (F : PolyFock d) (z ζ) : ℂ := ∑' m, F m * evC z ζ (Psihat m κ)
def Fcb (κ) (F : PolyFock d) (z ζ) : ℂ := ∑' n, star (F n) * evC ζ z (Psihat n κ)
lemma Fc_diag  : Fc κ F z (star ∘ z) = polyanalyticEval κ F z
lemma Fcb_diag : Fcb κ F z (star ∘ z) = star (polyanalyticEval κ F z)

/-- `P_ℂ` -/
def Pc (κ) (F G) (z ζ) : ℂ := Fc κ F z ζ * Fcb κ F z ζ - Fc κ G z ζ * Fcb κ G z ζ
lemma Pc_diag : Pc κ F G z (star ∘ z) =
    ‖polyanalyticEval κ F z‖ ^ 2 - ‖polyanalyticEval κ G z‖ ^ 2
```

Claims:

| # | claim | Lean | remark |
|---|---|---|---|
| C1 | `|H_{m,q}(z,ζ)| ≤ C_q (1+|ζ|)^q (1+|z|)^m m^q/√m!`; hence `Fc`, `Fcb` converge locally uniformly | `norm_evC_Psihat_le`, `summable_Fc` | elementary; the two-variable analogue of `kernel_bound` |
| C2 | `Fc`, `Fcb`, `Pc` are entire along lines | `entireAlongLines_Fc`, `entireAlongLines_Pc` | C1 + `EntireAlongLines.of_tsum` |
| C3 | `|F| = |G|` on `ℂ^d` ⟹ `Pc κ F G ≡ 0` | `Pc_eq_zero` | (1.4) + `Pc_diag` |
| C4 | `Pc κ F G z ζ = ∑_{m,n} c_{mn} Ψ_{m,κ}(z,ζ) Ψ_{n,κ}(ζ,z)`, `c_{mn} = F_m F̄_n − G_m Ḡ_n`; the monomial coefficients of a vanishing (iterated one-variable) power series vanish | `coeff_Pc`, `coeff_eq_zero_of_Pc_zero` | Cauchy product of absolutely convergent series; fix `ζ`, `HasFPowerSeriesAt` uniqueness in `z`, then in `ζ` |
| C5 | in one variable the coefficient of `z^a ζ^b` is `∑_{r,s ≤ q} K_{rs}(m,n) c_{mn}` with `m = a+r+s−q`, `n = b+r+s−q` (products over coordinates in general): the equations decouple along the diagonals `m − n = s`, each involves `c` at `2q+1` consecutive points of one diagonal, and the extreme coefficients `K_{00}`, `K_{qq}` are nonzero | `coeff_monomial_Pc` | the "collapse to monomials at `ζ = 0`" of the outline is the `r = q` part of this |
| C6 | rank-one identity `∀ m n, F_m F̄_n = G_m Ḡ_n` ⟹ `∃ θ, |θ| = 1 ∧ F = θ G` | `eq_smul_of_rank_one` | `n₀` with `G_{n₀} ≠ 0`, `θ = Ḡ_{n₀}/F̄_{n₀}` |
| C7 | **`c = 0` from C5**: Section 3 for the cases where it holds by algebra, Section 4 otherwise | | |
| CPR | the statement of `DiscretePR.continuous_phase_retrieval` | `continuous_phase_retrieval_byhand` | C3–C7 |

## 3. Where the outline is a complete proof

* **`q = 0`**, all `d`, the full space: `Pc = g(z)ḡ(ζ) − h(z)h̄(ζ)` with `g = ∑ F_m z^m/√m!`;
  C4 gives `c_{mn} = 0` directly; C6 finishes.
* **Finitely supported `F, G`** (the polynomial subspaces `𝒱_κ^N`), any `q`: `c` has finite
  support; on each diagonal take the largest `(m,n)` with `c_{mn} ≠ 0` and the monomial
  `z^{m+q} ζ^{n+q}`. Only the term `r = s = 0` survives: `K_{00}(m,n) c_{mn} = 0` with
  `K_{00} ≠ 0`, contradiction. So `c = 0`; C6 finishes. (Checked symbolically for `q = 1` and a
  cubic `g`: the only solutions of `P_ℂ = 0` are `h = λ g`, `|λ| = 1`.)

## 4. Where it is not: the full space at `q ≥ 1`

The equations of C5 alone do **not** force `c = 0`. On the diagonal `m − n = s` they form a
`(2q+1)`-term linear recurrence with polynomial coefficients whose solution space is
`q`-dimensional. Computed (`kernel_test.py`, window of 40 coefficients, diagonal `m = n`):

| `q` | kernel dimension | basis | `L_39(λ)` | `∑_{n<40} L_n(λ)²` |
|---|---|---|---|---|
| 1 | 1 | `n ↦ L_n(1)` (note `L_1(1) = 0`) | `0.257` | `5.2`, still growing |
| 2 | 2 | `n ↦ L_n(2 − √2)`, `n ↦ L_n(2 + √2)` | `−0.283`, `−0.859` | `4.5`, `33.4`, still growing |

In general the kernel on the diagonal `s` is spanned by `n ↦ √(n!/(n+s)!) L_n^{(s)}(λ_i)`, with
`λ_1, …, λ_q` the zeros of the Laguerre polynomial `L_q` (numerical residual `10⁻¹⁵`). These
sequences are bounded, tend to zero like `n^{-1/4}`, and are excluded only by `∑ |c_{mn}|² < ∞`,
which holds for `c_{mn} = F_m F̄_n − G_m Ḡ_n` because `F, G ∈ ℓ²`, but only just. This is the
same fact as "the ambiguity function of the Hermite function `h_q` vanishes only on the `q`
circles `|ξ|² = λ_i`, a null set", which is what the cited continuous-phase-retrieval proof (and
the earlier development) uses. It cannot be avoided by algebra: in operator language the equations
say `tr(C ρ_z) = 0` for the coherent-state projections `ρ_z` and `C = F F* − G G*`, and the bounded
operators `C_{λ,s} = ∫_{|ξ|²=λ} e^{isθ} π(ξ) dθ` lie in the kernel of `C ↦ tr(C ρ_z)`; only their
failure to be Hilbert–Schmidt distinguishes them from `F F* − G G*`.

So the by-hand proof of the full-space statement needs one analytic lemma:

> **Lemma L.** A square-summable sequence satisfying the diagonal recurrence `R_{q,s}` is zero.

Routes, with rough costs (the present development is 5.6k code lines):

* **L-a (Hardy-space estimate).** Identify the solution space of `R_{q,s}` with the Laguerre
  sequences (this needs the operator identity `P_ℂ = ℓ_q(XY)(gḡ − hh̄)` with `X = ζ − ∂_z`,
  `Y = z − ∂_ζ`, `ℓ_q(x) ∝ L_q(−x)`, and `XY ≅ ∂_z∂_ζ` after conjugation by `e^{zζ}`), the
  generating function `∑ L_n^{(s)}(λ) x^n = e^{−λx/(1−x)}/(1−x)^{s+1}`, and compare the `H²` norm
  on `|x| = r` of the generating function of a kernel element (`≍ (1−r)^{−s−1/2}`) with the bound
  `≲ (1−r)^{−s}` from square-summability. Needs Laguerre polynomials (not in Mathlib), an
  exponential-sum mean-value lemma, contour estimates. Estimate 3–5k lines of new analysis. For
  `s = 0` alone a cheaper boundedness argument works, but `s ≠ 0` cannot be reduced to `s = 0`
  without the Heisenberg translations on `𝓕_κ` (roughly another 1k lines).
* **L-b (Fourier).** Prove that `C ↦ tr(C ρ_z)` is injective on Hilbert–Schmidt operators through
  the Fourier–Wigner transform. This is the earlier proof; no saving.
* **L-c (stability).** Use the block estimates already proved for the truncations `F_N, G_N` with
  a quantitative form of the finite-support argument. The recurrence amplifies errors by about
  `e^{c√N}` (the second Laguerre solution), which `e^{−N/10}` would absorb, but proving that
  amplification bound is Lemma L in disguise. Not viable.

## 5. Recommendation and what to decide

Execute Sections 1–3 as stated: the folder `Complexification/` (1.1–1.4), the file
`ContinuousPhaseRetrieval_PolyFock.lean` with C1–C6, C7 for `q = 0` (full space) and for `𝒱_κ^N`
(all `q`), about 1.5–2k lines, pure algebra plus one-variable Mathlib analysis; claim map in
`ContinuousPhaseRetrieval_PolyFock/CLAIMS.md`. This does **not** let the bridge
`ContinuousPR.lean` drop the earlier development; that requires Lemma L, a choice between L-a (new,
large) and keeping the earlier proof.

Agents: Opus, one per file, statements fixed in advance, `#print axioms` audit, as before.
