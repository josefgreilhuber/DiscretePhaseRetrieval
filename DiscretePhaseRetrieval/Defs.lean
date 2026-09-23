import DiscreteNorming.Defs
import Definitions
import DiscretePhaseRetrieval.Auxiliary
import PolyFock.TailBound

/-!
# The main theorem — definitions

Objects of the proof of Theorem 1.1 (paper §4) on top of the comparator `Showcase.lean`
(namespace `DiscretePR`), the Remez/VC block theory `DiscreteNorming` (points
`Pt d = EuclideanSpace ℝ (Fin (2d))`, complex coordinates `toC`), and the polynomial model of the
basis `PolyFock.Fock` (`P d = ℂ[z, z̄]`, `Psihat α q`, evaluation `ev`).

Throughout, `h : (Fin d → ℕ) →₀ ℂ` is the family of level weights of `Definitions.lean` and
`Ψ α h` the associated mixed-level basis; the paper's `L` is `levelBound h`, the largest size of
a level in the support of `h`.

* the size `‖α‖₁ = ∑ αᵢ` of a multi-index is `DiscretePR.size` (`Auxiliary.lean`);
  `mu = 1/100`, the annulus parameter of the paper;
* `levelBound h = max {‖q‖₁ : q ∈ supp h}` and `hnorm h = (∑_q |h_q|²)^{1/2}`, the normalisation
  of `Ψ`;
* `ofC` — real coordinates of a complex point (inverse of `DiscreteNorming.toC`);
* `box d N` — the multi-indices with `‖α‖₁ ≤ N`; `truncate N F` — the coefficients `F_N = P_N F`;
* `PsihatH α h` — the polynomial `Ψ_{α,h} ∈ ℂ[z, z̄]`;
* `truncPoly h N F ∈ VhN h N` — the polynomial `∑_{‖α‖₁≤N} F_α Ψ_{α,h}` in `ℂ[z, z̄]`;
* `annulus d μ N = B_{μ√N}(0) \ B_{μ√N/8}(0)` — the sampling block `A_{N,μ}`;
* `blockSep d h N` — the separation Proposition 2.1 gives on the block.

See `PLAN-MixedLevel-Main.md` and `CLAIMS.md`.
-/

open MeasureTheory Metric PolyFock PolyFock.Fock

noncomputable section

namespace DiscretePR

variable {d : ℕ}

/-- The annulus parameter `μ = 1/100` fixed in the paper. -/
def mu : ℝ := 1 / 100

/-! ### The level weights `h` -/

/-- `L = max {‖q‖₁ : q ∈ supp h}`, the paper's `L` with `h_q = 0` for `‖q‖₁ > L`. -/
def levelBound (h : (Fin d → ℕ) →₀ ℂ) : ℕ := h.support.sup size

/-- Every level occurring in `h` has size at most `levelBound h`. -/
theorem size_le_levelBound {h : (Fin d → ℕ) →₀ ℂ} {q : Fin d → ℕ} (hq : q ∈ h.support) :
    ‖q‖₁ ≤ levelBound h :=
  Finset.le_sup hq

/-- `‖h‖ = (∑_q |h_q|²)^{1/2}`, the normalisation of `Ψ`. -/
def hnorm (h : (Fin d → ℕ) →₀ ℂ) : ℝ := Real.sqrt (∑ q ∈ h.support, ‖h q‖ ^ 2)

theorem hnorm_nonneg (h : (Fin d → ℕ) →₀ ℂ) : 0 ≤ hnorm h := Real.sqrt_nonneg _

theorem hnorm_pos {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0) : 0 < hnorm h := by
  obtain ⟨q₀, hq₀⟩ := Finsupp.support_nonempty_iff.mpr hnonzero
  refine Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ⟨q₀, hq₀, ?_⟩)
  have : h q₀ ≠ 0 := Finsupp.mem_support_iff.mp hq₀
  positivity

theorem hnorm_sq (h : (Fin d → ℕ) →₀ ℂ) : hnorm h ^ 2 = ∑ q ∈ h.support, ‖h q‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-! ### Real coordinates, boxes, truncation -/

/-- Real coordinates of a complex point: `x_j = Re z_j`, `x_{j+d} = Im z_j`
(inverse of `DiscreteNorming.toC`). -/
def ofC (z : Fin d → ℂ) : DiscreteNorming.Pt d :=
  WithLp.toLp 2 fun i : Fin (2 * d) ↦
    if h : (i : ℕ) < d then (z ⟨i, h⟩).re else (z ⟨i - d, by omega⟩).im

/-- The multi-indices `α` with `‖α‖₁ ≤ N`. -/
def box (d N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ : Fin d ↦ Finset.range (N + 1)).filter fun α ↦ ‖α‖₁ ≤ N

/-- Truncation `F_N = P_N F` of a coefficient vector to the indices with `‖α‖₁ ≤ N`. -/
def truncate (N : ℕ) (F : PolyFock d) : PolyFock d :=
  ∑ α ∈ box d N, lp.single 2 α (F α)

/-! ### The mixed-level basis as a polynomial, and the spaces it spans -/

/-- `Ψ_{α,h}` as a polynomial in `ℂ[z, z̄]`. -/
def PsihatH (α : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) : P d :=
  MvPolynomial.C ((hnorm h : ℂ)⁻¹) * ∑ q ∈ h.support, MvPolynomial.C (h q) * Psihat α q

/-- The polynomial `∑_{‖α‖₁ ≤ N} F_α Ψ_{α,h}` in `ℂ[z, z̄]` (evaluating to `F_N`). -/
def truncPoly (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) (F : PolyFock d) : P d :=
  ∑ α ∈ box d N, MvPolynomial.C (F α) * PsihatH α h

/-- The space `V_h^N = span {Ψ_{α,h} : ‖α‖₁ ≤ N}` as a subspace of `ℂ[z, z̄]`. -/
def VhN (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) : Submodule ℂ (P d) :=
  Submodule.span ℂ (Set.range fun α : box d N ↦ PsihatH (α : Fin d → ℕ) h)

/-- The sampling block `A_{N,μ} = B_{μ√N}(0) \ B_{μ√N/8}(0)` in `ℝ^{2d} = ℂ^d`. -/
def annulus (d : ℕ) (μ : ℝ) (N : ℕ) : Set (DiscreteNorming.Pt d) :=
  ball 0 (μ * Real.sqrt N) \ ball 0 (μ * Real.sqrt N / 8)

/-- The separation `δ · (dim V_h^N)^{−1/(2d)}` that Proposition 2.1 provides on the block. -/
def blockSep (d : ℕ) (h : (Fin d → ℕ) →₀ ℂ) (N : ℕ) : ℝ :=
  DiscreteNorming.deltaPaper d (annulus d mu N)
    * (Module.finrank ℂ (VhN h N) : ℝ) ^ (-(1 / (2 * d : ℝ)))

end DiscretePR
