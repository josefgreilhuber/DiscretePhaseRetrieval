# Attack plan: bounded components of a real polynomial zero set

Target (`Warren/BoundedComponents/`, namespace `BoundedComponents`):

```lean
/-- **Bounded components bound.** The joint zero set of polynomials `p₁, …, pₘ` in `n`
real variables of degree `≤ d` has at most `(2d)ⁿ` bounded connected components. -/
theorem bounded_components {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hdeg : ∀ i, (p i).totalDegree ≤ d) :
    {C : Set (Fin n → ℝ) |
        ∃ x, (∀ i, MvPolynomial.eval x (p i) = 0) ∧
          C = connectedComponentIn {x | ∀ i, MvPolynomial.eval x (p i) = 0} x ∧
          Bornology.IsBounded C}.Finite ∧
    {C : Set (Fin n → ℝ) | … same … }.ncard ≤ (2 * d) ^ n
```

Proof shape (all steps elementary; no genericity, no Morse theory):

Let `Z = {x | ∀ i, eval x (p i) = 0}`, `Q = Σ (p i)²` (so `Z = {Q = 0}`, `Q ≥ 0`,
`deg Q ≤ 2d`). Given `N` distinct bounded components `C₁..C_N ⊆ B(0,M)`:

1. **Separation (topology).** Pairwise disjoint open `V₁..V_N`, and an open `V'`, with
   `Cᵢ ⊆ Vᵢ ⊆ B(0,M+1)`, `Vᵢ ∩ V' = ∅`, and `Z ∩ B̄(0,M+1) ⊆ ⋃Vᵢ ∪ V'`.
   [`K := Z ∩ B̄(0,M+1)` compact; `Cᵢ` is a component of `K`; in compact T2 spaces
   components are intersections of clopens (`connectedComponent_eq_iInter_isClopen`);
   separate `Cᵢ` from the compact `(⋃_{j≠i} Cⱼ) ∪ (K ∩ sphere)` by a clopen `Wᵢ`; make the
   `Wᵢ` pairwise disjoint by boolean operations; thicken by `δ/3` where `δ` is a positive
   lower bound on all mutual distances (`Disjoint.exists_thickenings`).]
2. **Sublevel capture.** `∃ ε₀ > 0, ∀ ε < ε₀, {Q ≤ ε} ∩ B̄(0,M+1) ⊆ ⋃Vᵢ ∪ V'`.
   [`Q` attains a positive minimum on the compact `B̄(0,M+1) \ (⋃Vᵢ ∪ V')`
   (`IsCompact.exists_isMinOn`), disjoint from `Z`.]
3. **Perturbation (explicit, not generic).** `P̃ := Q − ε + δ · Σⱼ Xⱼ^(2d+1)` with
   `δ · n · (M+1)^(2d+1) < ε/2` and `ε < ε₀/2`. Then on `B̄(0,M+1)`: `|P̃ − (Q − ε)| < ε/2`, so
   `{P̃ ≤ 0} ∩ B̄ ⊆ {Q ≤ 2ε} ∩ B̄ ⊆ ⋃Vᵢ ∪ V'`, and `P̃ < −ε/2 < 0` on each `Cᵢ`.
4. **Trapping.** `Dᵢ := connectedComponentIn {P̃ ≤ 0} xᵢ` (`xᵢ ∈ Cᵢ`) satisfies `Dᵢ ⊆ Vᵢ`.
   [`Dᵢ ⊆ Vᵢ ⊔ (⋃_{j≠i}Vⱼ ∪ V' ∪ B̄ᶜ)`, two disjoint opens, `Dᵢ` connected and meets `Vᵢ`.]
   Hence `Dᵢ` bounded, closed (component of a closed set), compact, pairwise distinct.
5. **Critical point in each `Dᵢ`.** `P̃` attains its min on `Dᵢ` at `xᵢ*`, with value
   `< 0`; a ball around `xᵢ*` lies in `{P̃ < 0}`, is preconnected, hence
   `⊆ Dᵢ` (`IsPreconnected.subset_connectedComponentIn`); so `xᵢ*` is a local min of `P̃`
   on `ℝⁿ`; `IsLocalMin.hasFDerivAt_eq_zero` + `hasFDerivAt_eval` + `dualCLM_single` give
   `∇P̃(xᵢ*) = 0`. Distinct `Dᵢ` ⟹ distinct `xᵢ*`.
6. **Count.** `∂ⱼP̃ = ∂ⱼQ + (2d+1)δ Xⱼ^(2d)`, `deg ≤ 2d`, leading form `(2d+1)δ Xⱼ^(2d)`
   (the degree-`2d` component of `∂ⱼQ` is `0` since `deg ∂ⱼQ ≤ 2d−1`). Properness at infinity
   is immediate (common complex zero of `{zⱼ^(2d)}` is `0`), so
   `PolynomialSard.polynomial_sard` gives `#Crit(P̃) ≤ (2d)ⁿ`. Therefore `N ≤ (2d)ⁿ`.
7. **Bootstrap.** Any finite family of bounded components has size `≤ (2d)ⁿ`
   (they lie in a common ball), so the set of bounded components is finite with
   `ncard ≤ (2d)ⁿ` — same argument as in `WeakBezout/Main.lean`.

## Clusters (one agent each; disjoint files)

| file | content | est. |
|---|---|---|
| `Separation.lean` | steps 1–2 and 4 for an arbitrary closed `Z ⊆ ℝⁿ` and continuous `Q`, `P̃` — pure topology, no polynomials | 400–600 |
| `CriticalPoint.lean` | step 5 for a differentiable `F : (Fin n → ℝ) → ℝ`: bounded `connectedComponentIn {F ≤ 0} x₀` with `F x₀ < 0` contains a point where `fderiv ℝ F = 0` | 100–150 |
| `Perturbation.lean` | step 3 + 6: `Q`, `P̃` as `MvPolynomial`s; `eval Q ≥ 0`, `eval Q = 0 ↔ ∈ Z`; size bound on the ball; `pderiv` of `P̃`; leading forms; `ProperAtInfinity`; apply `finite_criticalSet` | 250–350 |
| `Main.lean` | assemble + bootstrap + `#print axioms` | 150–200 |

Dependencies: `Separation`, `CriticalPoint`, `Perturbation` independent (Wave 1);
`Main` after all three (Wave 2). `Perturbation` imports `Warren.PolynomialSard`;
`CriticalPoint` imports `Warren.Transversality`.

## Design notes

* State steps 1–5 for **general closed sets and continuous/differentiable functions**, so the
  topology never sees `MvPolynomial`; polynomials enter only in `Perturbation`.
* Components are `connectedComponentIn Z x` (subsets), matching the style of
  `weak_bezout`; "bounded" is `Bornology.IsBounded`.
* Avoid `LocallyConnectedSpace`: use a small ball (convex ⟹ preconnected) in step 5.
* `hd : 1 ≤ d` is needed for `finite_criticalSet` (`1 ≤ 2d`); the `d = 0` case is degenerate.
* Bound sharpness: `(2d)ⁿ` is what this route gives; Milnor's `d(2d−1)^(n−1)` counts all
  components and uses a different (Morse-theoretic) argument.
