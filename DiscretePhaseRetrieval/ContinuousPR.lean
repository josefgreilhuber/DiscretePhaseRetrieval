import Definitions
import ContinuousPhaseRetrieval.ContinuousPR

/-! # Continuous phase retrieval (imported)
The only use of the earlier development `ContinuousPhaseRetrieval/` (by the author and
collaborators; see its `PROVENANCE.md`): equal pointwise moduli on all of `ℂ^d` force equality
up to one unimodular constant. Its theorem `DiscretePolyFock.exactModulusRecovery` is stated
directly for `DiscretePR.polyanalyticEval`, so no identification of definitions is needed. -/

namespace DiscretePR

/-- **Continuous phase retrieval** for the mixed-level polyanalytic Fock space of the
level weights `h ≠ 0` (cited in the paper; imported from the older development). -/
theorem continuous_phase_retrieval {d : ℕ} (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0)
    (F G : PolyFock d)
    (hmod : ∀ z, ‖polyanalyticEval h F z‖ = ‖polyanalyticEval h G z‖) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧ polyanalyticEval h F = θ • polyanalyticEval h G := by
  obtain ⟨θ, hθ, hFG⟩ :=
    DiscretePolyFock.exactModulusRecovery (d := d) hd h hnonzero (a := G) (b := F)
      (fun z => (hmod z).symm)
  refine ⟨θ, hθ, ?_⟩
  -- the coefficient identity `F = θ • G` transported to the coefficient functions
  have hcoeff : ∀ α : Fin d → ℕ, coeff F α = θ * coeff G α := by
    intro α
    have hfun : (F : (Fin d → ℕ) → ℂ) = ((θ • G : PolyFock d) : (Fin d → ℕ) → ℂ) := by
      rw [hFG]
    change (F : (Fin d → ℕ) → ℂ) α = θ * (G : (Fin d → ℕ) → ℂ) α
    rw [hfun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  funext z
  change polyanalyticEval h F z = θ * polyanalyticEval h G z
  simp only [polyanalyticEval]
  rw [← tsum_mul_left]
  exact tsum_congr fun α => by rw [hcoeff α, mul_assoc]

end DiscretePR
