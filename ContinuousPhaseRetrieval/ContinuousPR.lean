import Definitions
import ContinuousPhaseRetrieval.ModulusRecovery.MixedLevel

/-!
# Interface: continuous phase retrieval in a mixed-level component

If two members of the mixed-level coefficient model of the level weights `h ≠ 0`
have the same pointwise modulus everywhere on `ℂ^d`, they agree up to one global
unimodular phase.  The statement below is obtained by gluing to
`ModulusRecovery.exact_modulus_recovery_mixed`
(`ModulusRecovery/MixedLevel.lean`): `Coeffs d` coefficient families are exactly
`DiscretePR.PolyFock d` elements, and `toFunH h` is exactly
`DiscretePR.polyanalyticEval h` (identical series, definitionally equal term by term).
-/

noncomputable section

namespace DiscretePolyFock

/-- Package a `DiscretePR.PolyFock d` coefficient family as a `ModulusRecovery.Coeffs d`
coefficient family.  The coefficient function is literally the same; the
square-summability certificate comes from `lp` membership at `p = 2`. -/
private def toCoeffs {d : ℕ} (F : DiscretePR.PolyFock d) :
    ModulusRecovery.Coeffs d where
  coeff := fun α => F α
  summable_norm_sq := by
    have h := (lp.memℓp F).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
    have hfun :
        (fun α : Fin d → ℕ => ‖F α‖ ^ (2 : ENNReal).toReal) =
          fun α : Fin d → ℕ => ‖F α‖ ^ (2 : ℕ) := by
      funext α
      have h2 : ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) := by norm_num
      rw [h2, Real.rpow_natCast]
    exact hfun ▸ h

/-- The two evaluation series are definitionally identical:
`DiscretePR.HermitePoly n k = phi1D k n`, hence `DiscretePR.Φ α q = Phi q α`,
hence `DiscretePR.Ψ α h` is the mixed basis element used by `toFunH h`, and the
tsums agree term by term. -/
private theorem toFunH_toCoeffs {d : ℕ} (h : (Fin d → ℕ) →₀ ℂ)
    (F : DiscretePR.PolyFock d) (z : Fin d → ℂ) :
    ModulusRecovery.toFunH h (toCoeffs F) z = DiscretePR.polyanalyticEval h F z := rfl

/-- Continuous phase retrieval in a mixed-level component (`imp:emr`): if two
coefficient families have pointwise equal evaluation moduli everywhere, they agree
up to a global unimodular phase.

Proved by gluing to `ModulusRecovery.exact_modulus_recovery_mixed`. -/
theorem exactModulusRecovery {d : ℕ} (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (hnonzero : h ≠ 0)
    {a b : DiscretePR.PolyFock d}
    (hmod : ∀ z : Fin d → ℂ,
      ‖DiscretePR.polyanalyticEval h a z‖ = ‖DiscretePR.polyanalyticEval h b z‖) :
    ∃ τ : ℂ, ‖τ‖ = 1 ∧ b = τ • a := by
  obtain ⟨w, hw, hVU⟩ :=
    ModulusRecovery.exact_modulus_recovery_mixed (d := d) hd h hnonzero
      (U := toCoeffs a) (V := toCoeffs b)
      (by
        intro z
        rw [toFunH_toCoeffs, toFunH_toCoeffs]
        exact hmod z)
  refine ⟨w, hw, ?_⟩
  have hcoeff : ∀ α : Fin d → ℕ, b α = w * a α := fun α =>
    congrFun (congrArg ModulusRecovery.Coeffs.coeff hVU) α
  apply Subtype.ext
  funext α
  have hsmul : (w • a : DiscretePR.PolyFock d) α = w * a α := by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  exact (hcoeff α).trans hsmul.symm

end DiscretePolyFock
