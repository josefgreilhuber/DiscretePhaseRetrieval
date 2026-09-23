/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-!
# Definitions for the multivariate Remez inequality

Shared definitions for `Remez/Multivariate/`: ray fibers of a set in `ℝᵐ = Fin m → ℝ`
(with the sup norm), their `r^{m-1}`-weighted length, and the function
`βₘ(t) = (1 - t)^{1/m}` of Brudnyi–Ganzburg.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Remez

variable {m : ℕ}

/-- The fiber `{r > 0 | x + r • θ ∈ S}` of `S` along the open ray from `x` in direction `θ`. -/
def rayFiber (S : Set (Fin m → ℝ)) (x θ : Fin m → ℝ) : Set ℝ :=
  {r : ℝ | 0 < r ∧ x + r • θ ∈ S}

/-- The `r^{m-1}`-weighted length `∫_{rayFiber S x θ} r^{m-1} dr` of a ray fiber. -/
noncomputable def rayWeight (m : ℕ) (S : Set (Fin m → ℝ)) (x θ : Fin m → ℝ) : ℝ≥0∞ :=
  ∫⁻ r in rayFiber S x θ, ENNReal.ofReal (r ^ (m - 1))

/-- `βₘ(t) = (1 - t)^{1/m}` (Ganzburg, (4.2)). -/
noncomputable def beta (m : ℕ) (t : ℝ) : ℝ := (1 - t) ^ (1 / (m : ℝ))

lemma rayFiber_mono {S T : Set (Fin m → ℝ)} (h : S ⊆ T) (x θ : Fin m → ℝ) :
    rayFiber S x θ ⊆ rayFiber T x θ := fun _ hr => ⟨hr.1, h hr.2⟩

lemma rayWeight_mono {S T : Set (Fin m → ℝ)} (h : S ⊆ T) (x θ : Fin m → ℝ) :
    rayWeight m S x θ ≤ rayWeight m T x θ :=
  lintegral_mono_set (rayFiber_mono h x θ)

lemma measurableSet_rayFiber {S : Set (Fin m → ℝ)} (hS : MeasurableSet S) (x θ : Fin m → ℝ) :
    MeasurableSet (rayFiber S x θ) :=
  measurableSet_Ioi.inter (hS.preimage (by fun_prop))

end Remez
