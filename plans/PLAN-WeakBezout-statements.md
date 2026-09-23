# Blueprint: Lean statements for sharp weak Bézout (draft, pre-survey)

Namespace `WeakBezout`. `k` field (algebraically closed only where marked).
`R := MvPolynomial (Fin n) k`, `m := Ideal.span (Set.range X)` (irrelevant ideal),
`I := Ideal.span (Set.range p)`, `J := Ideal.span (Set.range L)` where
`L i := homogeneousComponent (d i) (p i)`.

## Cluster A — interpolation (any field)

A1. `exists_eval_ne_zero_of_ne` : for `a ≠ b : Fin n → k`, there is a degree-1
    polynomial vanishing at `b`, not at `a`.
A2. `linearIndependent_evals` : for distinct points `x : Fin N ↪ (Fin n → k)`
    all lying in the zero set of `I`, the images in `R ⧸ I` of suitable
    interpolation polynomials are linearly independent; consequently
    `N ≤ Module.finrank k (R ⧸ I)` whenever the quotient is finite-dimensional.
    (Phrase via: the evaluation `R ⧸ I →ₗ (Fin N → k)` is surjective.)

## Cluster B — leading-form degeneration (any field)

B1. Define the filtration `V t := (image of degree-≤-t polynomials in R ⧸ I)`.
B2. `finrank_quotient_le` : `finrank (R ⧸ I) ≤ finrank (R ⧸ J)` given both
    finite-dimensional — via: the top-degree form of an element of `I` with
    degree exactly `t` need not lie in `J`, so state it carefully:
    `dim (V t ⧸ V (t−1)) ≤ dim (R_t ⧸ (J ∩ R_t))` — the correct elementary
    statement: if `f₁,…,f_r ∈ R ⧸ I` images of degree-≤-t polys are linearly
    independent mod `V (t−1)`, their top forms are linearly independent mod
    `J_t`. Key sub-lemma: top form of `∑ gᵢ pᵢ` (degree t) lies in
    `∑ (top form gᵢ)·Lᵢ ⊆ J_t` when no cancellation of top degrees; handle
    cancellation by choosing representatives of minimal degree.
    NOTE (risk): this is the standard `in(I) ⊇ (in(p₁),…,in(pₙ))` argument;
    the implementation agent should phrase it as: for `f ∈ I` with
    `deg f = t`, `homogeneousComponent t f ∈ J`? — FALSE in general
    (e.g. cancellation): correct is `homogeneousComponent t f ∈ J_t + in-parts
    of lower-degree members`… Simplest correct route: prove
    `dim V t − dim V (t−1) ≤ h_{R/J}(t)` directly by a rank argument on the
    map `(top form)` from a complement of `V(t−1)` in `V t`. Implementation
    freedom given to the agent; the *statement* B2 is what matters.
    Fallback formulation: `finrank (R ⧸ I) ≤ ∑_{t ≤ T} h_{R/J}(t)` for the `T`
    with `m^T ⊆ J` — any correct constant works since the RHS total is `∏dᵢ`.

## Cluster C — Nullstellensatz consequences (k alg. closed)

C1. `radical_eq_irrelevant` : if the only common zero of the `L i` is `0`,
    then `(Ideal.span (range L)).radical = m`. [Nullstellensatz]
C2. `pow_irrelevant_le` : `m` f.g. ⟹ `∃ s, m ^ s ≤ J`.
C3. `finiteDimensional_quotient` : `m ^ s ≤ J` ⟹ `FiniteDimensional k (R ⧸ J)`
    (monomials of degree ≥ s die; quotient spanned by monomials of degree < s).
    Same conclusion for `R ⧸ I` (since `p i ≡ L i` + lower, some power of each
    variable reduces — needs its own argument: `x^α` for large `|α|` reducible
    mod `I`… simplest: `dim (R⧸I) ≤ dim (R⧸J) < ∞` comes from B2's fallback
    formulation; so C3 only needed for `J`).

## Cluster D — regularity of the leading forms (the CM core; k alg. closed)

D1. `isRegular_of_radical_irrelevant` : if `L : Fin n → R` homogeneous of
    degrees `d i ≥ 1` and `√J = m`, then `L` is a regular sequence on `R`.
    Route per survey: localize at `m`, regular local + sop ⟹ regular sequence,
    transfer back (graded faithfulness at `m`). Exact decomposition fixed
    after survey.

## Cluster E — Hilbert-series count (any field)

E1. For a regular sequence of homogeneous `L i` of degrees `d i`:
    `finrank (R ⧸ J) = ∏ i, d i` (given `FiniteDimensional`).
    Implementation: induction on the sequence with the SES
    `0 → (R⧸J_k)(−d) →·L→ R⧸J_k → R⧸J_{k+1} → 0` at the level of graded
    dimension counts, or the generating-function identity; only `≤` needed.

## Cluster F — assembly (k alg. closed)

F1. `weak_bezout` :
    `∀ (p : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ), (∀ i, 1 ≤ d i) →`
    `(∀ i, (p i).totalDegree ≤ d i) →`
    `(∀ x : Fin n → k, (∀ i, eval x (homogeneousComponent (d i) (p i)) = 0) → x = 0) →`
    `{x | ∀ i, eval x (p i) = 0}.Finite ∧ {x | ∀ i, eval x (p i) = 0}.ncard ≤ ∏ i, d i`.
    (Finiteness free: every finite subset has ≤ ∏dᵢ elements by A+B+E.)

Edge cases to keep honest: `n = 0` (empty products; zero set is `{0}`-ish
singleton `≤ 1 = ∏` ✓); some `p i = 0` with `L i = 0` — then hypothesis F1
fails unless n=0, fine; `d i` larger than `totalDegree` allowed — then
`L i = homogeneousComponent (d i) (p i)` may be `0`, hypothesis forces
nondegeneracy, correct as stated.
