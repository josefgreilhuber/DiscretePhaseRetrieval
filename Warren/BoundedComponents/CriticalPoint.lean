/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-! # Bounded components: critical points

Two pure-topology / pure-analysis facts about connected components of sublevel sets.

* `IsClosed.connectedComponentIn'`: connected components (in the sense of
  `connectedComponentIn`) of a closed subset of any topological space are closed.
* `BoundedComponents.exists_fderiv_eq_zero_of_isBounded`: if `F : (Fin n → ℝ) → ℝ` is
  differentiable, `F x₀ < 0`, and the connected component of `x₀` in the sublevel set
  `{x | F x ≤ 0}` is bounded, then that component contains a critical point of `F`.
  The point is a global minimiser of `F` on the (compact) component; since `F < 0` on a
  ball around it, that ball lies in the component, so the minimiser is a local minimum.
-/

open Set Filter Topology

/-- Connected components (`connectedComponentIn`) of a closed set are closed. -/
theorem IsClosed.connectedComponentIn' {X : Type*} [TopologicalSpace X] {F : Set X}
    (hF : IsClosed F) (x : X) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

namespace BoundedComponents

variable {n : ℕ}

/-- A bounded connected component of the sublevel set `{F ≤ 0}` on which `F` takes a negative
value contains a critical point of `F`. -/
theorem exists_fderiv_eq_zero_of_isBounded (F : (Fin n → ℝ) → ℝ) (hF : Differentiable ℝ F)
    (x₀ : Fin n → ℝ) (hx₀ : F x₀ < 0)
    (hbdd : Bornology.IsBounded (connectedComponentIn {x | F x ≤ 0} x₀)) :
    ∃ x ∈ connectedComponentIn {x | F x ≤ 0} x₀, fderiv ℝ F x = 0 := by
  set S : Set (Fin n → ℝ) := {x | F x ≤ 0} with hS
  set D : Set (Fin n → ℝ) := connectedComponentIn S x₀ with hD
  have hScl : IsClosed S := isClosed_le hF.continuous continuous_const
  have hDcl : IsClosed D := hScl.connectedComponentIn' x₀
  have hDcpt : IsCompact D := Metric.isCompact_of_isClosed_isBounded hDcl hbdd
  have hx₀S : x₀ ∈ S := by simpa [hS] using hx₀.le
  have hx₀D : x₀ ∈ D := mem_connectedComponentIn hx₀S
  obtain ⟨xs, hxsD, hmin⟩ := hDcpt.exists_isMinOn ⟨x₀, hx₀D⟩ hF.continuous.continuousOn
  have hxs_neg : F xs < 0 := lt_of_le_of_lt (hmin hx₀D) hx₀
  -- a ball around `xs` on which `F < 0`
  have hopen : IsOpen {x | F x < 0} := isOpen_lt hF.continuous continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen xs hxs_neg
  have hballS : Metric.ball xs r ⊆ S := fun y hy => by
    have : F y < 0 := hball hy
    exact this.le
  -- the ball lies in `D`
  have hDeq : D = connectedComponentIn S xs := connectedComponentIn_eq hxsD
  have hballD : Metric.ball xs r ⊆ D := by
    rw [hDeq]
    exact Metric.isPreconnected_ball.subset_connectedComponentIn (Metric.mem_ball_self hr) hballS
  -- hence `xs` is a local minimum
  have hloc : IsLocalMin F xs :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds xs hr) fun y hy => hmin (hballD hy)
  exact ⟨xs, hxsD, hloc.fderiv_eq_zero⟩

end BoundedComponents
