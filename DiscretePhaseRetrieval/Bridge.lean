import DiscretePhaseRetrieval.Defs

/-!
# Claim P0: identifications

* The comparator's basis `Φ n q` of `Definitions.lean` — the index convention of the paper, the
  coefficient multi-index first and the Landau level second — is the evaluation of the polynomial
  `Psihat n q ∈ ℂ[z, z̄]` (`PolyFock.Fock.ev_Psihat`).  The polyanalytic Fock development in
  `PolyFock/` is stated in terms of that same `Φ`, so no identification of two bases is needed.
  Taking the same combination of levels on both sides, the mixed-level basis `Ψ n h` is the
  evaluation of `PsihatH n h`.
* `toC`/`ofC` identify `Fin d → ℂ` with `ℝ^{2d}`, and the comparator's `euclideanDist` is the
  Euclidean distance of `Pt d` (`euclideanDist_eq_dist`); `euclideanDist z 0` is the Euclidean
  norm (`norm_ofC`).

These are the only places where the metric of `Pt d` is compared with the comparator's
`euclideanDist`: every statement of the proof of Theorem 1.1 is phrased with `euclideanDist`,
and `mem_annulus_ofC` describes the sampling block `annulus d μ N ⊆ Pt d` in those terms.
-/

open MeasureTheory Metric PolyFock PolyFock.Fock

namespace DiscretePR

variable {d : ℕ}

/-- The basis element is the evaluation of the polynomial `Psihat α κ`. -/
theorem Phi_eq_ev (α κ : Fin d → ℕ) (z : Fin d → ℂ) :
    Φ α κ z = ev z (Psihat α κ) :=
  (ev_Psihat _ _ _).symm

/-- The mixed-level basis element is the evaluation of the polynomial `PsihatH α h`. -/
theorem Psi_eq_ev (α : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) (z : Fin d → ℂ) :
    Ψ α h z = ev z (PsihatH α h) := by
  rw [PsihatH, map_mul, ev_C, map_sum, Ψ, hnorm]
  congr 1
  exact Finset.sum_congr rfl fun q _ ↦ by rw [map_mul, ev_C, Phi_eq_ev]

/-! ### Coordinates of `ofC`, and splitting a sum over `Fin (2d)` into its two halves -/

/-- Coordinatewise description of `ofC`. -/
theorem ofC_apply (z : Fin d → ℂ) (i : Fin (2 * d)) :
    (ofC z) i = if h : (i : ℕ) < d then (z ⟨i, h⟩).re else (z ⟨i - d, by omega⟩).im := rfl

/-- A sum over `Fin (2d)` splits into the first `d` and the last `d` coordinates. -/
lemma sum_split (f : Fin (2 * d) → ℝ) :
    ∑ i, f i = ∑ j : Fin d, f ⟨(j : ℕ), by omega⟩ + ∑ j : Fin d, f ⟨(j : ℕ) + d, by omega⟩ := by
  have h : d + d = 2 * d := (two_mul d).symm
  rw [← Fin.sum_congr' f h, Fin.sum_univ_add]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact Fin.ext (by simp [Nat.add_comm])

set_option linter.unusedSimpArgs false in
/-- The first `d` coordinates of `ofC z` are the real parts. -/
lemma ofC_apply_lt (z : Fin d → ℂ) (j : Fin d) (h : (j : ℕ) < 2 * d) :
    (ofC z) ⟨(j : ℕ), h⟩ = (z j).re := by
  rw [ofC_apply]
  simp only [Fin.val_mk]
  rw [dif_pos j.isLt]

set_option linter.unusedSimpArgs false in
/-- The last `d` coordinates of `ofC z` are the imaginary parts. -/
lemma ofC_apply_ge (z : Fin d → ℂ) (j : Fin d) (h : (j : ℕ) + d < 2 * d) :
    (ofC z) ⟨(j : ℕ) + d, h⟩ = (z j).im := by
  rw [ofC_apply]
  simp only [Fin.val_mk]
  rw [dif_neg (by omega)]
  have e : (⟨(j : ℕ) + d - d, by omega⟩ : Fin d) = j := Fin.ext (by simp)
  rw [e]

theorem toC_ofC (z : Fin d → ℂ) : DiscreteNorming.toC (ofC z) = z := by
  funext j
  apply Complex.ext
  · simp [DiscreteNorming.toC, ofC_apply]
  · simp [DiscreteNorming.toC, ofC_apply]

theorem ofC_toC (x : DiscreteNorming.Pt d) : ofC (DiscreteNorming.toC x) = x := by
  ext i
  rw [ofC_apply]
  by_cases h : (i : ℕ) < d
  · rw [dif_pos h]
    simp only [DiscreteNorming.toC]
  · rw [dif_neg h]
    simp only [DiscreteNorming.toC]
    have e : (⟨(i : ℕ) - d + d, by omega⟩ : Fin (2 * d)) = i := Fin.ext (by simp; omega)
    rw [e]

/-- The comparator's Euclidean distance is the distance of `Pt d`. -/
theorem euclideanDist_eq_dist (z w : Fin d → ℂ) : euclideanDist z w = dist (ofC z) (ofC w) := by
  rw [euclideanDist, EuclideanSpace.dist_eq]
  congr 1
  rw [sum_split (fun i => dist ((ofC z) i) ((ofC w) i) ^ 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ofC_apply_lt, ofC_apply_lt, ofC_apply_ge, ofC_apply_ge, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im]
  ring

/-- `euclideanDist` is symmetric. -/
theorem euclideanDist_comm (z w : Fin d → ℂ) : euclideanDist z w = euclideanDist w z := by
  rw [euclideanDist_eq_dist, euclideanDist_eq_dist, dist_comm]

theorem ofC_zero : ofC (0 : Fin d → ℂ) = 0 := by
  ext i
  rw [ofC_apply]
  by_cases h : (i : ℕ) < d <;> simp [h]

/-- The comparator's distance to the origin is the norm of the real coordinate vector. -/
theorem norm_ofC (z : Fin d → ℂ) : ‖ofC z‖ = euclideanDist z 0 := by
  rw [euclideanDist_eq_dist, ofC_zero, dist_zero_right]

/-- The sampling block, described by the comparator's Euclidean distance:
`ofC z ∈ A_{N,μ}` exactly when `μ√N/8 ≤ |z| < μ√N`. -/
theorem mem_annulus_ofC {μ : ℝ} {N : ℕ} (z : Fin d → ℂ) :
    ofC z ∈ annulus d μ N ↔
      μ * Real.sqrt N / 8 ≤ euclideanDist z 0 ∧ euclideanDist z 0 < μ * Real.sqrt N := by
  rw [annulus, Set.mem_diff, mem_ball_zero_iff, mem_ball_zero_iff, not_lt, norm_ofC]
  exact and_comm

/-! ### An arithmetic helper

Taking square roots in a squared estimate; used wherever a bound on `‖x‖ ^ 2` is turned into a
bound on `‖x‖`. -/

/-- From `‖x‖ ^ 2 ≤ c ^ 2 * B` and `0 ≤ c` conclude `‖x‖ ≤ c * √B`. -/
theorem norm_le_of_sq_le {E : Type*} [SeminormedAddGroup E] {x : E} {c B : ℝ}
    (h : ‖x‖ ^ 2 ≤ c ^ 2 * B) (hc : 0 ≤ c) : ‖x‖ ≤ c * Real.sqrt B := by
  have h' := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc] at h'

end DiscretePR
