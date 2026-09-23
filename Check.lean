import Main
import STFT
import STFTComparatorBridge
import Showcase

/-!
# Checks

The comparator uses polynomial weights and the Euclidean-space model `ℂ^[d]`, while the proof
uses finitely supported level weights and the coordinate model `Fin d → ℂ`.  The lemmas below
transport the coefficient theorem across the canonical equivalences between these
representations.  The zero-dimensional case is elementary; positive dimensions use
`DiscretePR.DiscretePhaseRetrieval_coefficients`.

The file then checks the comparators' exact types, records the single-level specialization, and
audits the axioms of the main theorem, both comparator bridges, and the STFT corollaries.
-/

open scoped BigOperators ENNReal lp

noncomputable section

namespace ComparatorBridge

/-- Reindex the monomials of a multivariate polynomial by ordinary multi-index functions. -/
def levelWeights {d : ℕ} (h : MvPolynomial (Fin d) ℂ) : (Fin d → ℕ) →₀ ℂ :=
  Finsupp.domCongr Finsupp.equivFunOnFinite h

lemma levelWeights_apply {d : ℕ} (h : MvPolynomial (Fin d) ℂ) (q : Fin d → ℕ) :
    levelWeights h q = h.coeff (Finsupp.equivFunOnFinite.symm q) := by
  simp [levelWeights, MvPolynomial.coeff]

lemma levelWeights_ne_zero {d : ℕ} {h : MvPolynomial (Fin d) ℂ} (hh : h ≠ 0) :
    levelWeights h ≠ 0 := by
  exact (Finsupp.domCongr Finsupp.equivFunOnFinite).injective.ne hh

private lemma tsum_norm_eq_sum {d : ℕ} (h : MvPolynomial (Fin d) ℂ) :
    ∑' q, ‖h.coeff q‖ ^ 2 =
      ∑ q ∈ (levelWeights h).support, ‖levelWeights h q‖ ^ 2 := by
  have hfin : (∑' q, ‖levelWeights h q‖ ^ 2) =
      ∑ q ∈ (levelWeights h).support, ‖levelWeights h q‖ ^ 2 := by
    apply tsum_eq_sum
    intro q hq
    rw [Finsupp.notMem_support_iff.mp hq]
    norm_num
  rw [← hfin, ← Finsupp.equivFunOnFinite.tsum_eq]
  apply tsum_congr
  intro q
  simp [levelWeights, MvPolynomial.coeff]

private lemma phi_eq {d : ℕ} (n : Fin d → ℕ) (q : Fin d →₀ ℕ) (z : Fin d → ℂ) :
    DiscretePR_Showcase.Φ n q (WithLp.toLp 2 z) =
      DiscretePR.Φ n (Finsupp.equivFunOnFinite q) z := by
  rfl

private lemma tsum_phi_eq_sum {d : ℕ} (h : MvPolynomial (Fin d) ℂ)
    (n : Fin d → ℕ) (z : Fin d → ℂ) :
    ∑' q, h.coeff q * DiscretePR_Showcase.Φ n q (WithLp.toLp 2 z) =
      ∑ q ∈ (levelWeights h).support, levelWeights h q * DiscretePR.Φ n q z := by
  have hfin : (∑' q, levelWeights h q * DiscretePR.Φ n q z) =
      ∑ q ∈ (levelWeights h).support, levelWeights h q * DiscretePR.Φ n q z := by
    apply tsum_eq_sum
    intro q hq
    simp only [Finsupp.notMem_support_iff.mp hq, zero_mul]
  rw [← hfin, ← Finsupp.equivFunOnFinite.tsum_eq]
  apply tsum_congr
  intro q
  rw [phi_eq]
  simp [levelWeights, MvPolynomial.coeff]

lemma psi_eq {d : ℕ} (h : MvPolynomial (Fin d) ℂ)
    (n : Fin d → ℕ) (z : Fin d → ℂ) :
    DiscretePR_Showcase.Ψ h n (WithLp.toLp 2 z) =
      DiscretePR.Ψ n (levelWeights h) z := by
  rw [DiscretePR_Showcase.Ψ, DiscretePR.Ψ, tsum_norm_eq_sum, tsum_phi_eq_sum]

lemma expansion_eq {d : ℕ} (h : MvPolynomial (Fin d) ℂ)
    (F : ℓ^2((Fin d → ℕ), ℂ)) (z : Fin d → ℂ) :
    (∑' n, F n * DiscretePR_Showcase.Ψ h n (WithLp.toLp 2 z)) =
      DiscretePR.polyanalyticEval (levelWeights h) F z := by
  apply tsum_congr
  intro n
  rw [psi_eq]
  rfl

private lemma euclideanDist_eq_dist {d : ℕ} (x y : Fin d → ℂ) :
    DiscretePR.euclideanDist x y = dist (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
  rw [DiscretePR.euclideanDist, EuclideanSpace.dist_eq]
  congr 2
  funext i
  rw [dist_eq_norm]

/-- The proved coefficient theorem has exactly the comparator's public conclusion. -/
theorem comparator_proved : type_of% @DiscretePR_Showcase.DiscretePhaseRetrieval := by
  intro d h hnonzero
  cases d with
  | zero =>
      refine ⟨Set.univ, ?_, ?_⟩
      · intro x _ y _ hxy
        exact (hxy (Subsingleton.elim x y)).elim
      · intro f _ g _ hsample
        have habs : ‖f 0‖ = ‖g 0‖ := hsample 0 (by simp)
        by_cases hg : g 0 = 0
        · have hf : f 0 = 0 := norm_eq_zero.mp (by simpa [hg] using habs)
          refine ⟨0, ?_⟩
          funext z
          have hz : z = 0 := Subsingleton.elim z 0
          subst z
          simp [hf, hg]
        · refine ⟨f 0 / g 0, ?_⟩
          funext z
          have hz : z = 0 := Subsingleton.elim z 0
          subst z
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
  | succ d =>
      obtain ⟨S₀, hsep, hphase⟩ := DiscretePR.DiscretePhaseRetrieval_coefficients
        (d + 1) (by omega) (levelWeights h) (levelWeights_ne_zero hnonzero)
      let S : Set (EuclideanSpace ℂ (Fin (d + 1))) := {z | WithLp.ofLp z ∈ S₀}
      refine ⟨S, ?_, ?_⟩
      · intro x hx y hy hxy
        have hxy' : WithLp.ofLp x ≠ WithLp.ofLp y := by
          intro heq
          exact hxy (WithLp.ofLp_injective 2 heq)
        have hs := hsep (WithLp.ofLp x) hx (WithLp.ofLp y) hy hxy'
        rw [euclideanDist_eq_dist] at hs
        simpa using hs
      · intro f hf g hg hsample
        obtain ⟨F, rfl⟩ := hf
        obtain ⟨G, rfl⟩ := hg
        obtain ⟨θ, -, hθ⟩ := hphase F G (by
          intro z hz
          have hs := hsample (WithLp.toLp 2 z) (by simpa [S] using hz)
          simp only at hs
          rw [expansion_eq, expansion_eq] at hs
          exact hs)
        refine ⟨θ, ?_⟩
        funext z
        calc
          (∑' n, F n * DiscretePR_Showcase.Ψ h n z) =
              DiscretePR.polyanalyticEval (levelWeights h) F (WithLp.ofLp z) := by
                simpa using expansion_eq h F (WithLp.ofLp z)
          _ = θ * DiscretePR.polyanalyticEval (levelWeights h) G (WithLp.ofLp z) := by
                simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hθ (WithLp.ofLp z)
          _ = θ * ∑' n, G n * DiscretePR_Showcase.Ψ h n z := by
                rw [expansion_eq]

end ComparatorBridge

/-- The single-level weight recovers the basis `Φ · q` of the true polyanalytic Fock space. -/
example {d : ℕ} (n q : Fin d → ℕ) (z : Fin d → ℂ) :
    DiscretePR.Ψ n (Finsupp.single q 1) z = DiscretePR.Φ n q z := by
  simp [DiscretePR.Ψ]

#print axioms DiscretePR.DiscretePhaseRetrieval_proved
#print axioms DiscretePR.DiscretePhaseRetrieval_coefficients
#print axioms ComparatorBridge.comparator_proved
#print axioms ComparatorBridge.window_MemLp_proved
#print axioms ComparatorBridge.stft_comparator_proved
#print axioms DiscretePR.continuous_phase_retrieval
#print axioms DiscretePR.STFTDiscretePhaseRetrieval_unit_of_finite_window
#print axioms DiscretePR.STFTDiscretePhaseRetrieval
