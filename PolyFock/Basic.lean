/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Definitions
import DiscretePhaseRetrieval.Auxiliary

/-!
# True polyanalytic Fock spaces: basis, reproducing kernel, and its tail

This file sets up, in the most elementary way possible, the objects appearing in the
"tail bounds" lemma for the reproducing kernel of the true polyanalytic Fock space
`𝓕^d_L ⊆ L²(ℂ^d ; e^{-|·|²})`.

## Main definitions

The basis itself is not defined here: this development uses the comparator's basis from
`Definitions.lean`, namely `DiscretePR.HermitePoly m n z` — the normalised complex Hermite
function of the paper,
`φ_{m,n}(z, z̄) = (m! n!)^{-1/2} ∑_{r=0}^{min m n} (-1)^r r! C(m,r) C(n,r) z^{m-r} z̄^{n-r}`,
an orthonormal basis of `L²(ℂ ; e^{-|·|²})` — and its tensorisation
`DiscretePR.Φ n q z = ∏ᵢ φ_{nᵢ,qᵢ}(zᵢ, z̄ᵢ)` on `ℂ^d` (the paper's `Φ_{𝐧,𝐪}`, with the
coefficient multi-index first and the Landau level second).

* `PolyFock.tailKernelDiag L N z` — the real number `∑ ‖Φ_{𝐧,𝐪}(z)‖²` over the index set
  `{(𝐧, 𝐪) : ‖𝐪‖₁ = L, ‖𝐧‖₁ > N}`, i.e. the diagonal of the reproducing kernel `K_{L,N}` of the
  orthogonal complement of `span {Φ_{𝐧,𝐪} : ‖𝐪‖₁ = L, ‖𝐧‖₁ ≤ N}` inside `𝓕^d_L`.
  By Parseval / the reproducing property this is exactly
  `‖K_{L,N}(z, ·)‖²_{L²(ℂ^d ; e^{-|·|²})}`, the quantity bounded in the tail-bound lemma.

Nothing here uses any Hilbert-space theory: every object is an explicit (finite or
infinite) sum of explicit polynomials in `z` and `z̄`.
-/

namespace PolyFock

open Finset Complex
open DiscretePR (Φ)
open scoped DiscretePR

noncomputable section

variable {d : ℕ}

/-- The diagonal of the tail kernel

`K_{L,N}(z, w) = ∑_{‖𝐪‖₁ = L} ∑_{‖𝐧‖₁ > N} Φ_{𝐧,𝐪}(z, z̄) conj (Φ_{𝐧,𝐪}(w, w̄))`,

as a real number:
`∑_{‖𝐪‖₁ = L} ∑_{‖𝐧‖₁ > N} ‖Φ_{𝐧,𝐪}(z, z̄)‖²`.

By the reproducing property this equals `‖K_{L,N}(z, ·)‖²_{L²(ℂ^d ; e^{-|·|²})}`, the
quantity estimated by the tail-bound lemma. -/
def tailKernelDiag (L N : ℕ) (z : Fin d → ℂ) : ℝ :=
  ∑' p : (Fin d → ℕ) × (Fin d → ℕ),
    if ‖p.2‖₁ = L ∧ N < ‖p.1‖₁ then ‖Φ p.1 p.2 z‖ ^ 2 else 0

/-- The summand of `tailKernelDiag` is nonnegative. -/
lemma diagTerm_nonneg (L N : ℕ) (z : Fin d → ℂ)
    (p : (Fin d → ℕ) × (Fin d → ℕ)) :
    0 ≤ (if ‖p.2‖₁ = L ∧ N < ‖p.1‖₁ then ‖Φ p.1 p.2 z‖ ^ 2 else 0) := by
  split <;> positivity

end

end PolyFock
