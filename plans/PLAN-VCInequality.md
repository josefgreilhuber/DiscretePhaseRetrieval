# Attack plan: the relative Vapnik–Chervonenkis inequality (`VCInequality/`)

**Status (2026-09-02): done.** `VCInequality.relative_deviation` and `relative_deviation_vc` are
proved with the faithful constant 8 of Vapnik–Chervonenkis 1974 (Appendix, Theorem 1),
sorry-free, standard axioms only, 2018 lines. Route F2 below was carried out for the binomial
lemma (constant `1/8`), simplified: domination reduces to `p = k/m`, where the De Moivre
identity and Cauchy–Schwarz give `P[Y ≥ k+1] ≥ (k(m−k)/m) P[Y=k]²` with no modal-mass shift,
and Robbins' bound follows from Mathlib's `Stirling.log_stirlingSeq_diff_le`. See the README
section for the file layout.

Target: the inequality invoked as "[VapnikChervonenkis1974]" in the proof of Proposition 2.1 of
`Discrete_PR/paper.pdf` (p. 3), together with the Sauer–Shelah step displayed right after it.

## Reference (what to cite, and what is actually proved there)

**Primary reference.** C. Cortes, S. Greenberg, M. Mohri, *Relative deviation learning bounds
and generalization with unbounded loss functions*, Ann. Math. Artif. Intell. 85 (2019) 45–70,
arXiv:1310.5796. Theorem 5 with `α = 2` and `τ → 0`:

    P_{S ~ D^m} [ sup_h (R(h) − R̂_S(h)) / √R(h) > ε ]  ≤  4 · E[S_H(x₁^{2m})] · exp(−m ε² / 4)
                                                       ≤  4 · Π_H(2m) · exp(−m ε² / 4),

`R(h) = P(A_h)`, `R̂_S` the empirical frequency, `Π_H(2m)` the growth function. This is the
one-sided *lower-tail* statement; a second inequality of the same theorem bounds the upper tail
`(R̂_S − R)/√R̂_S` — note the **empirical** denominator there.

Its proof has three ingredients, all of which we follow:

1. **Symmetrization (their Lemma 2)**: the ghost-sample lemma of Vapnik 1998, valid for
   `m ε² > 1`. It needs, for a fixed set of probability `p > 1/m`, that a binomial
   `Bin(m, p)` is at least its mean with probability `> 1/4`.
2. **Binomial lemma (their Lemma 1)**: S. Greenberg, M. Mohri, *Tight lower bound on the
   probability of a binomial exceeding its expectation*, Statist. Probab. Lett. 86 (2014)
   91–98, arXiv:1306.1433. `P[Bin(m,p) ≥ mp] > 1/4` for `p > 1/m`. Cortes–Greenberg–Mohri
   point out that every earlier proof of the relative deviation bound (Vapnik 1974/1998,
   Anthony–Shawe-Taylor 1993) used this without proof. Elementary proof: B. Doerr, *An
   elementary analysis of the probability that a binomial random variable exceeds its
   expectation*, Statist. Probab. Lett. 139 (2018) 67–74, arXiv:1712.00519 (Theorem 10 there
   gives even `P[X > E X] ≥ 1/4` for `ln(4/3)/m ≤ p < 1`).
3. **Random signs + Hoeffding + union bound over dichotomies**, then Sauer–Shelah.

Secondary: M. Anthony, J. Shawe-Taylor, *A result of Vapnik with applications*, Discrete Appl.
Math. 47 (1993) 207–217 (the `ν`-relative form); Anthony–Bartlett, *Neural Network Learning*
(1999) Ch. 5; Boucheron–Bousquet–Lugosi, ESAIM P&S 9 (2005) §5.1 (statement only, no proof).

**Mismatch with the paper's display.** The paper states a two-sided bound
`P[sup |P̂ − P| / √P > ε] ≤ 8 m(2M) exp(−Mε²/4)` with the *true* probability in the
denominator on both sides. The literature gives the lower tail with denominator `√P` and the
upper tail with denominator `√P̂`, each with constant 4. The paper's argument only uses the
lower tail (it needs every set of `F` to receive at least its share of sample points), so the
clean fix is to cite CGM Theorem 5 (`α = 2`) and state the one-sided inequality with 4. We
formalise exactly that one-sided inequality; the constant 8 in the paper is then slack, which
matters for the binomial lemma (see step F).

## Target statements (`VCInequality/RelativeVCInequality.lean`, namespace `VCInequality`)

```lean
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Empirical frequency of `A` in the sample `x` (`#{i | x i ∈ A} / m`). -/
noncomputable def empFreq (m : ℕ) (x : Fin m → X) (A : Set X) : ℝ :=
  (Finset.univ.filter (fun i ↦ x i ∈ A)).card / m

/-- `G` bounds the number of traces of `𝒢` on every `n`-point sample (growth function). -/
def IsGrowthBound (𝒢 : Set (Set X)) (n G : ℕ) : Prop :=
  ∀ x : Fin n → X, ((fun A ↦ {i | x i ∈ A}) '' 𝒢).ncard ≤ G

/-- **Relative VC inequality** (Vapnik–Chervonenkis; Cortes–Greenberg–Mohri Thm 5, α = 2). -/
theorem relative_deviation {ι : Type*} [Countable ι] (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (m : ℕ) {G : ℕ}
    (hG : IsGrowthBound (Set.range A) (2 * m) G) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : Fin m ↦ μ).real
        {x | ∃ i, ε < (μ.real (A i) - empFreq m x (A i)) / √(μ.real (A i))}
      ≤ 4 * G * Real.exp (-(m * ε ^ 2) / 4)

/-- VC dimension `≤ V`: no `V+1`-point finset is shattered. -/
def VCDimLE (𝒢 : Set (Set X)) (V : ℕ) : Prop :=
  ∀ s : Finset X, (∀ t ⊆ s, ∃ A ∈ 𝒢, ∀ y ∈ s, y ∈ A ↔ y ∈ t) → s.card ≤ V

/-- Sauer–Shelah form: the growth function is at most `(e n / V)^V` for `n ≥ V ≥ 1`. -/
theorem relative_deviation_vc {ι : Type*} [Countable ι] (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (m V : ℕ) (hV : 1 ≤ V) (hmV : V ≤ 2 * m)
    (hvc : VCDimLE (Set.range A) V) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : Fin m ↦ μ).real
        {x | ∃ i, ε < (μ.real (A i) - empFreq m x (A i)) / √(μ.real (A i))}
      ≤ 4 * (Real.exp 1 * (2 * m) / V) ^ V * Real.exp (-(m * ε ^ 2) / 4)
```

Design remarks:

* **No `sup`, no `τ`.** The event is `∃ i, …`, a countable union of measurable sets, so the
  measurability problem of `sup_h` (which CGM simply *assume*) disappears; countability of the
  index is the only price. Lean's `x / 0 = 0` and `√0 = 0` make the ratio `0` when
  `μ (A i) = 0`, which is exactly the right convention (such a set can never violate the
  bound), so CGM's `+τ` regulariser and the `τ → 0` limit are not needed. Likewise the
  `+ 1/m` in the symmetrized denominator is dropped: with `c = 0` the monotonicity argument in
  step A is *easier* (no `mε² > 1` needed there).
* **Countable index.** For the application (Prop. 2.1) the family `F` is uncountable; the
  reduction to a countable subfamily (sets `{|P| ≥ r}` with `P` having Gaussian-rational
  coefficients and `r ∈ ℚ`, chosen so that each set of `F` of measure `≥ t|Ω|` contains a
  countable-family set of measure `≥ t'|Ω|`) belongs to the Prop. 2.1 formalisation, not here.
  The VC pull-back lemma of Lemma 2.2 is also out of scope.
* `hmV : V ≤ 2m` is the `k ≥ V` hypothesis of the paper's Sauer–Shelah display; `1 ≤ V` avoids
  `V = 0` degeneracy (`(x/0)^0 = 1` would still be fine, but the sum bound is stated for `V ≥ 1`).

## Proof

Write `ν := Measure.pi (fun _ : Fin m ↦ μ)` for the sample, `P A := μ.real A`,
`P̂ x A := empFreq m x A`. Two representations of the double sample are used:
`(Fin m → X) × (Fin m → X)` with `ν.prod ν` (for Fubini) and `Fin m → X × X` with
`Measure.pi (fun _ ↦ μ.prod μ)` (for coordinate swaps); they are identified by
`MeasureTheory.measurePreserving_arrowProdEquivProdArrow` (Mathlib, `Constructions/Pi.lean`).

**Trivial regime.** If `m ε² < 1` then `4 exp(−mε²/4) ≥ 4 e^{−1/4} > 1 ≥ LHS` (and `G ≥ 1`
as soon as `ι` is nonempty; for empty `ι` the event is empty). So assume `m ε² ≥ 1`.

**A (symmetrization, `Symmetrization.lean`).** Hypothesis, kept *parametric* in a constant
`c > 0`:

    hbin : ∀ B, MeasurableSet B → 1/m < P B → c ≤ ν.real {y | m * P B ≤ #{i | y i ∈ B}}.

Claim: `ν.real E ≤ c⁻¹ · (ν.prod ν).real E'`, where

    E  := {x | ∃ i, ε < (P (A i) − P̂ x (A i)) / √(P (A i))},
    E' := {(x,y) | ∃ i, ε < (P̂ y (A i) − P̂ x (A i)) / √(½ (P̂ x (A i) + P̂ y (A i)))}.

Proof. Let `Ẽ := {(x,y) | ∃ i, ε < ratio_x(i) ∧ P (A i) ≤ P̂ y (A i)}` (measurable, countable
union). (i) `Ẽ ⊆ E'`: for the witness `i`, put `R = P(A i)`, `a = P̂ x`, `b = P̂ y`, so
`a < R − ε√R` and `b ≥ R`. The function `F(u,v) = (u − v)/√(½(u+v))` is increasing in `u` and
decreasing in `v` on `u,v ≥ 0`, `u+v > 0` (derivative check, or the algebraic identity
`F(u,v)² · ½(u+v) = (u−v)²`), hence
`F(b,a) ≥ F(R, R − ε√R) = ε√R / √(R − ½ε√R) > ε`. (ii) `(ν.prod ν) Ẽ ≥ c · ν E` by
`Measure.prod_apply` + `lintegral_mono`: for `x ∈ E` with witness `i`, the section
`Ẽ_x ⊇ {y | m P(A i) ≤ #{j | y j ∈ A i}}` has measure `≥ c` by `hbin`, since
`R > ε² ≥ 1/m` (from `R − a > ε√R`, `a ≥ 0`). The witness `i = i(x)` need not be chosen
measurably: it is only used pointwise inside the integrand, which is measurable by
`measurable_measure_prodMk_left`.

**B (swap invariance, `Swap.lean`).** For `σ : Fin m → Bool` let
`swap σ : (Fin m → X × X) → (Fin m → X × X)` flip the coordinates `i` with `σ i = true`.
`MeasurePreserving (swap σ) (pi (μ.prod μ)) (pi (μ.prod μ))` by `measurePreserving_pi` and
`Measure.prod_swap`. Hence for any measurable `E'`,
`π E' = 2^{−m} ∑_σ π (swap σ ⁻¹' E') = ∫ (2^{−m} ∑_σ 1_{E'}(swap σ z)) dπ(z)`
(`lintegral_indicator`, `lintegral_finset_sum`). Transport `E'` from A to this representation
via `measurePreserving_arrowProdEquivProdArrow`.

**C (Rademacher–Hoeffding for one dichotomy, `Rademacher.lean`).** Fix `z : Fin m → X × X`
and a trace `v : Fin m → Bool × Bool` (membership of the two halves). With
`d i := (v i).2 − (v i).1 ∈ {−1,0,1}` and `T := ∑ i, ((v i).1 + (v i).2) ≥ ∑ i, (d i)²`,
the inner event for the pair `(z, v)` is

    ∑ i, s_i · d i > ε · √(m T / 2),   s_i = ±1 according to σ i.

Under the uniform measure on `Fin m → Bool` (`uniformOn Set.univ`, which is `Measure.pi` of
uniform-on-`Bool` by `uniformOn_pi`, coordinates independent by `iIndepFun_pi`), each summand
is mean zero, supported in `[−|d i|, |d i|]`, hence sub-Gaussian with parameter `(d i)²`
(`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`; `HasSubgaussianMGF.zero` when `d i = 0`).
Hoeffding `measure_sum_ge_le_of_iIndepFun` gives
`≤ exp(−ε² m T / 2 / (2 ∑ (d i)²)) ≤ exp(−m ε² / 4)` (using `∑ (d i)² ≤ T`; if `T = 0` the
event is empty since the ratio is `0`). This is the only place Mathlib's probability library
does real work.

**D (union over dichotomies, `Dichotomy.lean`).** For fixed `z` the event
`{σ | ∃ i, ε < sym-ratio(swap σ z, A i)}` depends on `A i` only through its trace on the `2m`
points of `z`; it is the union over the traces `v ∈ image (Set.range A)` (at most `G` of them by
`hG`, viewed on `Fin (2m) ≃ Fin m ⊕ Fin m`) of the events of C. `measure_biUnion_finset_le`
gives `≤ G · exp(−mε²/4)`. Combine with B and A: `ν E ≤ c⁻¹ · G · exp(−mε²/4)`.

**E (Sauer–Shelah, `Sauer.lean`).** For a sample `x : Fin n → X`, the trace family
`𝒯 := image … ⊆ Finset (Fin n)` (as a `Finset (Finset (Fin n))`) satisfies
`#𝒯 ≤ #𝒯.shatterer ≤ ∑_{k ≤ 𝒯.vcDim} n.choose k` (Mathlib `Finset.card_le_card_shatterer`,
`Finset.card_shatterer_le_sum_vcDim`). `𝒯.vcDim ≤ V` because a shattered index set `s` gives a
shattered point set `x '' s` of the same cardinality (`x` is injective on `s`: if `x i = x j`
then `{i}` cannot be cut out of `{i,j}`), then `hvc`. New lemma needed:
`∑_{k ≤ V} n.choose k ≤ (e n / V)^V` for `1 ≤ V ≤ n` (proof: multiply by `(V/n)^V ≤ (V/n)^k`,
bound by `(1 + V/n)^n ≤ e^V` via `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`-free route:
`(1 + V/n)^n ≤ exp(V)` from `one_add_le_exp`/`Real.add_one_le_exp`). This is the
`IsGrowthBound … ((e·2m/V)^V)` fed to `relative_deviation`; the real-valued bound is
kept as a real number (no floor), so state `IsGrowthBound` with `(G : ℝ)` or add a `≤` wrapper.

**F (the binomial lemma, `Binomial.lean`) — the expensive part.** Needed:
`c ≤ P[Bin(m,p) ≥ mp]` for all `m ≥ 1`, `1/m < p ≤ 1`, in the form `hbin` of step A. First
identify the count: `y ↦ #{i | y i ∈ B}` pushes `ν` to `Bin(m, P B)` (Mathlib
`ProbabilityTheory.binomial`, `setBernoulli`; or directly: the event `{count = k}` is the
disjoint union over `k`-subsets `J` of boxes of measure `p^k (1−p)^{m−k}` by `Measure.pi_pi`).
Then the purely arithmetic statement about `∑_{k ≥ mp} C(m,k) p^k (1−p)^{m−k}`. Options:

| route | constant `c` | cost | what it needs |
|---|---|---|---|
| F1 Doerr Thm 10 / Greenberg–Mohri | `1/4` (paper's 4) | high (~2000 lines) | stochastic domination in `p` (derivative `d/dp P[X ≥ k] = m C(m−1,k−1) p^{k−1} q^{m−k} ≥ 0`, `Polynomial`-friendly); **median fact** `P[Bin(m,k/m) ≥ k] ≥ 1/2` (Neumann 1966 / Kaas–Buhrman 1980 — not in Mathlib, its own project); Robbins-precision Stirling bound for `P[Bin(m,k/m) = k] < √(m / (2π k (m−k)))` (Mathlib has only `le_factorial_stirling` and `stirlingSeq'_antitone`; the threshold `g(20,3) = 0.2502` is razor-thin, so the `e^{1/(12n)}` form must be derived from `log_stirlingSeq_diff_hasSum`); ~91 exact small cases (`n ≤ 19`) by `norm_num`/`decide` on ℚ. |
| F2 Cauchy–Schwarz + De Moivre | `1/8` (paper's 8) | medium-high | Identity `E(X − mp)₊ = m p q · P[Bin(m−1,p) = ⌊mp⌋]` (telescoping with `k C(m,k) = m C(m−1,k−1)`, ~150 lines), then `P[X > mp] ≥ E(X−mp)₊² / E(X−mp)² = m p q · P[Bin(m−1,p) = ⌊mp⌋]²` — no median fact, no domination. Numerically (grid `m ≤ 1000`) `max(this, p^m) ≥ 0.1326 > 1/8`, worst case `m = 3, p ≈ 0.335`. Still needs a Robbins-quality *lower* bound for the modal mass `P[Bin(m−1,p) = ⌊mp⌋] ≥ 0.354/√(mpq)` (the mode of `Bin(m−1,p)` is exactly `⌊mp⌋`) plus `p ≥ 1 − 1/m ⇒ P[X = m] = p^m ≥ 1/4`. Margin only ~3%, so small cases again by exact arithmetic. |
| F3 Chebyshev symmetrization (fallback, no binomial lemma) | — | low (~100 lines) | Replace `P̂ y ≥ P` in `Ẽ` by `P̂ y ≥ P − ½ε√P`; Chebyshev (`meas_ge_le_variance_div_sq`, variance of the count `= m p q`) gives probability `≥ 1 − 4/(mε²) ≥ 1/2` for `mε² ≥ 8`; the monotonicity argument then yields sym-ratio `> ε/2`. Result: `2 · G · exp(−mε²/16)` for `mε² ≥ 8`. **Changes the paper's constants** (`M` grows by a factor 4: `3000 + 1200|log t|` becomes roughly `12000 + 4800|log t|`). |

Recommendation: do A–E now with `hbin` as an explicit hypothesis (theorem
`relative_deviation_of_binomial_bound`), so the whole Vapnik argument is verified
independently of F. Then decide F: F3 if the paper's constants may change; F1 for a faithful
constant 4; F2 is the elementary path to the paper's 8 but is not cheaper than F1 in Lean
because both bottleneck on Robbins-quality Stirling. Before starting F1/F2, derive Robbins'
bounds `√(2πn)(n/e)^n e^{1/(12n+1)} ≤ n! ≤ √(2πn)(n/e)^n e^{1/(12n)}` from
`Stirling.log_stirlingSeq_diff_hasSum` — a self-contained ~200-line lemma of independent use.

## Files

| file | content |
|---|---|
| `VCInequality/Defs.lean` | `empFreq`, `IsGrowthBound`, `VCDimLE`, `symRatio`; basic measurability lemmas |
| `VCInequality/Monotone.lean` | the two-variable monotonicity of `F(u,v)` and the inequality `F(R, R − ε√R) > ε` |
| `VCInequality/Symmetrization.lean` | step A, parametric in `c` (`hbin`) |
| `VCInequality/Swap.lean` | step B: `swap σ` measure preserving, averaging identity, transport between the two representations |
| `VCInequality/Rademacher.lean` | step C: Hoeffding for `∑ s_i d_i` under `uniformOn univ` on `Fin m → Bool` |
| `VCInequality/Dichotomy.lean` | step D: reduction to traces, union bound |
| `VCInequality/Sauer.lean` | step E: trace family, `vcDim` comparison, `∑ choose ≤ (en/V)^V` (the binomial estimate itself is the shared `DiscretePR.sum_choose_le_exp_pow`, `DiscretePhaseRetrieval/Auxiliary.lean`) |
| `VCInequality/Binomial.lean` | step F (initially `sorry`-free only for the Chebyshev fallback, or left as a hypothesis) |
| `VCInequality/RelativeVCInequality.lean` | assembly: `relative_deviation_of_binomial_bound`, `relative_deviation`, `relative_deviation_vc` |
| `VCInequality.lean` | import root; add `[[lean_lib]] name = "VCInequality"` to `lakefile.toml` and to `defaultTargets` |

Suggested order: Defs → Monotone → Sauer (pure combinatorics, independent) → Rademacher →
Swap → Dichotomy → Symmetrization → RelativeVCInequality (with `hbin` hypothesis) → Binomial.

## Mathlib API checklist (all present in the pinned Mathlib, `v4.31.0-rc2`)

* `MeasureTheory.Measure.pi`, `Measure.pi_pi`, `Measure.pi_eq`, `measurePreserving_pi`,
  `measurePreserving_arrowProdEquivProdArrow`, `Measure.prod_swap`, `Measure.prod_apply`,
  `measurable_measure_prodMk_left`, `lintegral_mono`, `lintegral_finset_sum`, `lintegral_indicator`
* `ProbabilityTheory.uniformOn`, `uniformOn_pi`, `uniformOn_apply_finset`, `iIndepFun_pi`
* `ProbabilityTheory.HasSubgaussianMGF`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`,
  `HasSubgaussianMGF.zero`, `measure_sum_ge_le_of_iIndepFun`
* `Finset.Shatters`, `Finset.shatterer`, `Finset.vcDim`, `Finset.card_le_card_shatterer`,
  `Finset.card_shatterer_le_sum_vcDim`
* `ProbabilityTheory.binomial`, `setBernoulli`, `map_ncard_setBernoulli_real_singleton` (step F);
  `ProbabilityTheory.meas_ge_le_variance_div_sq` (F3); `Stirling.le_factorial_stirling`,
  `Stirling.log_stirlingSeq_diff_hasSum` (F1/F2)
* Missing and to be proved here: `∑_{k≤V} n.choose k ≤ (e n/V)^V`; Robbins' bounds; the
  binomial-count law under `Measure.pi`.

## Side observations on `paper.pdf` (p. 3–4), to fix in the text

* Cite the one-sided lower-tail inequality with constant 4 (CGM Thm 5, α = 2), see above.
* With `ε = ½√t` the guaranteed point count per set is `(t/2)·M`, not `½M`, and the deleted
  set has size `(t/3)·M`, not `⅓M` (the Markov step is stated with `t/3·M` pairs).
