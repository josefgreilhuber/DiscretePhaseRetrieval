# Orchestration plan: sharp weak Bézout (Looijenga Ch. 2 §10 route)

Target (headline, affine form — equivalent to the notes' Thm 10.13 weak form, but
avoids formalizing ℙⁿ):

> **Theorem (sharp weak Bézout).** Let `k` be an algebraically closed field,
> `p₁, …, pₙ ∈ k[x₁, …, xₙ]`, `dᵢ ≥ 1`, with `deg pᵢ ≤ dᵢ`. Let `Lᵢ` be the
> degree-`dᵢ` homogeneous component of `pᵢ` (the leading form). If the only common
> zero of `L₁, …, Lₙ` in `kⁿ` is `0`, then the common zero set of `p₁, …, pₙ` in
> `kⁿ` is finite and has at most `d₁ ⋯ dₙ` points.

This is sharp (bound `∏ dᵢ` attained by `pᵢ = ∏_{j<dᵢ}(xᵢ − j)`), and the
"no zeros at infinity" hypothesis is the finiteness hypothesis of the notes'
Theorem 10.13 in affine clothing.

## Proof chain (each step = one lemma cluster, one agent)

Let `R = k[x₁..xₙ]`, `I = (p₁..pₙ)`, `J = (L₁..Lₙ)`, `m = (x₁..xₙ)`.

- **(A) Interpolation.** For `N` distinct points of `Z(p₁..pₙ)`, the evaluation
  map `R/I → k^N` is surjective (Lagrange interpolation; any field), so
  `dim_k R/I ≥ N` (in the sense: `N` linearly independent elements).
- **(B) Leading-form degeneration.** `dim_k R/I ≤ dim_k R/J`, via the degree
  filtration: `dim (R_{≤t} + I)/(R_{≤t−1} + I) ≤ dim (R_t / J_t)` because the
  top form of any element of `I` of degree `t` lies in `J_t + (top forms from
  lower...)` — precisely: if `f ∈ R_{≤t}` and `f ∈ R_{≤t−1} + I` fails, its
  degree-`t` component is constrained mod `J_t`. Pure linear algebra.
- **(C) Nullstellensatz step.** `Z(L₁..Lₙ) = {0}` ⟹ `√J = m` ⟹ `m^s ⊆ J`
  for some `s` ⟹ `R/J` is a finite-dimensional `k`-vector space, and `J` is
  `m`-primary.
- **(D) Regularity (the CM core).** `L₁..Lₙ` is a regular sequence in `R`.
  Route: localize at `m`; `R_m` is an `n`-dimensional regular (hence
  Cohen–Macaulay) local ring; `J` is `m_m`-primary so `L₁..Lₙ` is a system of
  parameters; sop in CM local ⟹ regular sequence; transfer regularity back to
  `R` (a nonzero graded module over `R` localizes nonzero at `m`, since proper
  homogeneous ideals lie in `m`).
- **(E) Hilbert-series count.** For a regular sequence of forms of degrees
  `dᵢ`, iterating `0 → (R/(L₁..L_k))(−d_{k+1}) → R/(L₁..L_k) → R/(L₁..L_{k+1}) → 0`
  gives `∑_t dim (R/J)_t = ∏ dᵢ` (finite by (C)); we only need `≤`.
- **(F) Assembly.** `N ≤ dim R/I ≤ dim R/J = ∏dᵢ` for every `N` distinct common
  zeros ⟹ zero set finite with `ncard ≤ ∏dᵢ`.

Fallbacks if (D)'s ingredients are missing from Mathlib: formalize the sop⟹regular
implication for the graded polynomial ring directly (depth induction), scoped by the
survey results.

## Phases

0. **Survey** (2 parallel agents): map exactly what the local Mathlib
   (`Warren/.lake/packages/mathlib`, v4.31.0-rc2 era) provides for each step.
1. **Blueprint**: I fix Lean statements of A–F against the surveyed API.
2. **Implement**: parallel Opus agents, one per cluster, in this project
   (`Warren/WeakBezout/*.lean`; junction gives ~15 s builds).
3. **Assemble + audit**: final theorem, `#print axioms`, README, memory.

Rules: agents write all Lean; I write none. Everything importable from Mathlib
must be imported, not re-proved.
