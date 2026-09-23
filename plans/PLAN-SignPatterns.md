# Attack plan: Warren's sign-pattern bound (`Warren/SignPatterns/`)

**Route (revised 2026-09-02, "augmentation" version):** no degree enlargement. Instead of
adding `ε|x|^D` to every `pⱼ`, add ONE polynomial `q₀ := |x|² − M²` (degree 2) to the list,
with `M` so large that `q₀(x_σ) < 0` at every chosen witness `x_σ`. Every strict sign pattern
`σ` of `p` becomes the pattern `(−1, σ)` of the augmented list `(q₀, p₁, …, pₘ)`, and each such
pattern's component lies in `{q₀ < 0}`, a ball — bounded for free. Degrees stay `≤ D := max 2 d`,
the list grows by one (`m ↦ m + 1`).

Target (namespace `SignPatterns`):

```lean
theorem sign_patterns {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hdeg : ∀ j, (p j).totalDegree ≤ d) :
    (strictSignPatterns p).ncard
      ≤ ∑ l ∈ Finset.range (n + 1), Nat.choose (m + 1) l * 2 ^ l * (2 * max 2 d) ^ n
```
Warren form (`1 ≤ n ≤ m + 1`): `≤ (4 e · max 2 d · (m+1) / n)ⁿ`. Warren's Theorem 2 has
`2(2d)ⁿ` and `m` where we have `(2·max 2 d)ⁿ` and `m + 1`.

## Proof

**B (augmentation, `Perturb.lean`).** Fix witnesses `x_σ`; `M² > max_σ Σᵢ (x_σ)ᵢ²`;
`q₀ := Σᵢ Xᵢ² − M²`. Apply `AlgebraicTransversality.exists_not_bad` to the augmented family
`Fin.cons q₀ p` (perturbs only degree-≤1 coefficients): `q := pert (Fin.cons q₀ p) z`. Then
`deg qⱼ ≤ max 2 d`, general position, `{q₀' ≤ 0}` bounded (positive-definite quadratic beats
linear terms), signs at all `x_σ` unchanged, and `sign q₀'(x_σ) = −1`.

**A (counting for a generic family, `Charge.lean` + `Counting.lean`).** For a strict pattern `σ`
with some `σⱼ = −1` where `{qⱼ ≤ 0}` is bounded: `U_σ := connectedComponentIn G x_σ` is open and
bounded (`⊆ {qⱼ < 0}`). `F_σ := closure U_σ \ U_σ` is nonempty (`n ≥ 1`), closed, `⊆ ⋃ Z_{{j}}`.
Pick `x₀ ∈ F_σ` maximizing `|J(x)|`, `J := J(x₀)`, `C := connectedComponentIn Z_J x₀`.
*Clopen claim:* `C ⊆ F_σ` and `J(z) = J` on `C` (closed by maximality; open by the orthant lemma
`Orthant.lean`, via `implicitToOpenPartialHomeomorph`). *Fiber bound:* patterns charged to
`(J, C)` agree off `J` (read at any point of `C`), so `≤ 2^{|J|}` of them. *Count:* `≤ (2D)ⁿ`
bounded components per `J` (`bounded_components`), summed over `|J| ≤ n`.

**Main.** `S := strictSignPatterns p` injects into
`S' := {τ ∈ strictSignPatterns q | τ 0 = −1}` via `σ ↦ Fin.cons (−1) σ`; apply
`card_le_of_charge` to `S'` (family of `m + 1` polynomials of degree `≤ max 2 d`) with charges
from `exists_charge` using the index `0`.

## Files

| file | content |
|---|---|
| `Orthant.lean` | orthant lemma at a transversal point (IFT) — unchanged |
| `Perturb.lean` | Theorem B: augmentation + transversality glue (`exists_generic_augmentation`) |
| `Counting.lean` | abstract counting `card_le_of_charge` — unchanged |
| `Charge.lean` | `exists_charge`, hypothesis now `∃ j, σ j = −1 ∧ IsBounded {qⱼ ≤ 0}` |
| `SignPatternBound.lean` | assembly + Warren form (binomial estimate: shared `DiscretePR.sum_choose_le_exp_pow_range`, `DiscretePhaseRetrieval/Auxiliary.lean`) |
