import Main
import ContinuousPhaseRetrieval.ModulusRecovery.HermiteBasis
import ContinuousPhaseRetrieval.ModulusRecovery.WindowExpansion
import DiscretePhaseRetrieval.Dilation

/-!
# Corollary: discrete phase retrieval for the short-time Fourier transform

Corollary of the main theorem `DiscretePR.DiscretePhaseRetrieval_proved` (`Main.lean`) on the
level of the STFT, stated in the vocabulary of `Definitions.lean` only and as in the paper
(Theorem `thm:STFT`).  Phase space is `ℝ^d × ℝ^d`, with points `(x, ξ)` (`x` the position,
`ξ` the frequency) and the Euclidean distance; the STFT of `f ∈ L²(ℝ^d)` with window
`w ∈ L²(ℝ^d)` is
`stft w f x ξ = ∫ f(t) conj(w(t − x)) e^{−2πi ξ·t} dt`; the window is
`gaussWindow h = h(x) e^{−π|x|²}` for a real polynomial `h ≠ 0` in `d` variables.  The
separation is `√d/10⁷`.

The proof has two steps.

1. `STFTDiscretePhaseRetrieval_unit`: the corollary in the unit scale of the formal development,
   window `gaussWindowUnit h = h(x) e^{−|x|²/2}` (a finite combination of the Hermite functions
   of `ContinuousPhaseRetrieval/`, whose Hermite coefficients are the level weights of the space
   `𝓕_h` of the main theorem).  The link is `T(x, ξ) = (x − 2πi ξ)/√2 ∈ ℂ^d`:
   `|V_w f (x, ξ)| = e^{−(|x|² + 4π²|ξ|²)/4} |F(T(x, ξ))|` for the function
   `F ∈ 𝓕_h` with the
   Hermite coefficients of `f`; `phaseDistUnit` is the Euclidean distance of `ℂ^d` pulled back
   along `T`, so the sampling set of the main theorem transfers with its separation `4√d/10⁷`.
   Hermite completeness comes from `ContinuousPhaseRetrieval/ModulusRecovery/HermiteBasis.lean`,
   the window expansion, the phase-space geometry and the membership of the model functions in
   `𝓕_h` from `ContinuousPhaseRetrieval/ModulusRecovery/WindowExpansion.lean`.
2. `STFTDiscretePhaseRetrieval`: the unitary dilation `t = s/√(2π)` of `L²(ℝ^d)`
   (`DiscretePhaseRetrieval/Dilation.lean`) turns the window `h(x) e^{−π|x|²}` into a unit-scale
   window and `T` into `z = √π (x − i ξ)`, the map of the paper.  The unit phase-space
   distance
   becomes `√π` times the Euclidean one, and `4/√π ≥ 1` gives the constant `√d/10⁷`.
-/

open MeasureTheory

noncomputable section

namespace DiscretePR

/-- Unit-scale STFT phase retrieval for any nonzero finite Hermite window.  This is the reusable
coefficient-level core behind both the real-polynomial corollary and the standalone comparator's
complex-polynomial window. -/
theorem STFTDiscretePhaseRetrieval_unit_of_finite_window
    (d : ℕ) (hd : 0 < d) (w : L2Real d) (c : (Fin d → ℕ) →₀ ℂ) (hc : c ≠ 0)
    (hw : w = ∑ α ∈ c.support, c α • ModulusRecovery.realHermiteTensorL2 α) :
    ∃ S : Set (RealVec d × RealVec d),
      UniformlyDiscretePhaseUnit (4 * Real.sqrt d / 10 ^ 7) S ∧
        ∀ f g : L2Real d,
          (∀ x ξ, (x, ξ) ∈ S → ‖stft w f x ξ‖ = ‖stft w g x ξ‖) →
            ∃ θ : ℂ, ‖θ‖ = 1 ∧ f = θ • g := by
  classical
  have hh'0 : ModulusRecovery.signedConj c ≠ 0 := ModulusRecovery.signedConj_ne_zero hc
  have hwin : ModulusRecovery.windowH (ModulusRecovery.signedConj c)
      = ((ModulusRecovery.hnorm c : ℝ)⁻¹ : ℂ) • w := by
    rw [ModulusRecovery.windowH_signedConj, hw]
  obtain ⟨SC, hsep, hpr⟩ := DiscretePhaseRetrieval_proved d hd _ hh'0
  refine ⟨{p : RealVec d × RealVec d | ModulusRecovery.phaseToC p ∈ SC}, ?_, ?_⟩
  · intro x ξ hxξ x' ξ' hxξ' hne
    rw [ModulusRecovery.phaseDist_eq]
    exact hsep _ hxξ _ hxξ' fun heq => hne (ModulusRecovery.phaseToC_injective heq)
  · intro f g hmod
    have hfU : ModulusRecovery.hermiteExpansion (ModulusRecovery.hermiteCoeffs f) = f :=
      ModulusRecovery.hermiteExpansion_hermiteCoeffs f
    have hgV : ModulusRecovery.hermiteExpansion (ModulusRecovery.hermiteCoeffs g) = g :=
      ModulusRecovery.hermiteExpansion_hermiteCoeffs g
    have hsmul : ∀ (F : ModulusRecovery.L2Real d) (p : ModulusRecovery.PhaseSpace d),
        ModulusRecovery.stftRep (ModulusRecovery.windowH (ModulusRecovery.signedConj c)) F p
          = ((ModulusRecovery.hnorm c : ℝ)⁻¹ : ℂ) * ModulusRecovery.stftRep w F p := by
      intro F p
      rw [hwin, ModulusRecovery.stftRep_window_smul]
      congr 1
      simp
    have hkey : ∀ z ∈ SC,
        ‖ModulusRecovery.toFunH (ModulusRecovery.signedConj c)
            (ModulusRecovery.hermiteCoeffs f) z‖
          = ‖ModulusRecovery.toFunH (ModulusRecovery.signedConj c)
            (ModulusRecovery.hermiteCoeffs g) z‖ := by
      intro z hz
      have hpz : ModulusRecovery.phaseToC (ModulusRecovery.phaseToCInv z) = z :=
        ModulusRecovery.phaseToC_phaseToCInv z
      have hpS : ModulusRecovery.phaseToCInv z
          ∈ {p : RealVec d × RealVec d | ModulusRecovery.phaseToC p ∈ SC} := by
        change ModulusRecovery.phaseToC (ModulusRecovery.phaseToCInv z) ∈ SC
        rw [hpz]
        exact hz
      have hmodp :
          ‖ModulusRecovery.stftRep w
              (ModulusRecovery.hermiteExpansion (ModulusRecovery.hermiteCoeffs f))
              (ModulusRecovery.phaseToCInv z)‖
            = ‖ModulusRecovery.stftRep w
              (ModulusRecovery.hermiteExpansion (ModulusRecovery.hermiteCoeffs g))
              (ModulusRecovery.phaseToCInv z)‖ := by
        rw [hfU, hgV]
        exact hmod (ModulusRecovery.phaseToCInv z).1 (ModulusRecovery.phaseToCInv z).2 hpS
      have hnorm_eq :
          ‖ModulusRecovery.stftRep (ModulusRecovery.windowH (ModulusRecovery.signedConj c))
              (ModulusRecovery.hermiteExpansion (ModulusRecovery.hermiteCoeffs f))
              (ModulusRecovery.phaseToCInv z)‖
            = ‖ModulusRecovery.stftRep (ModulusRecovery.windowH (ModulusRecovery.signedConj c))
              (ModulusRecovery.hermiteExpansion (ModulusRecovery.hermiteCoeffs g))
              (ModulusRecovery.phaseToCInv z)‖ := by
        rw [hsmul, hsmul, norm_mul, norm_mul, hmodp]
      rw [ModulusRecovery.stft_model_modulus_mixed hd _ _ (ModulusRecovery.phaseToCInv z),
        ModulusRecovery.stft_model_modulus_mixed hd _ _ (ModulusRecovery.phaseToCInv z),
        hpz] at hnorm_eq
      exact mul_left_cancel₀
        (ne_of_gt (ModulusRecovery.gaussWeight_pos (ModulusRecovery.phaseToCInv z))) hnorm_eq
    obtain ⟨θ, hθ, hθeq⟩ :=
      hpr _ (ModulusRecovery.toFunH_mem_polyFockSpace hd _ (ModulusRecovery.hermiteCoeffs f))
        _ (ModulusRecovery.toFunH_mem_polyFockSpace hd _ (ModulusRecovery.hermiteCoeffs g)) hkey
    have hall : ∀ z,
        ‖ModulusRecovery.toFunH (ModulusRecovery.signedConj c)
            (ModulusRecovery.hermiteCoeffs g) z‖
          = ‖ModulusRecovery.toFunH (ModulusRecovery.signedConj c)
            (ModulusRecovery.hermiteCoeffs f) z‖ := by
      intro z
      rw [hθeq]
      simp [hθ]
    obtain ⟨a, ha, hae⟩ :=
      ModulusRecovery.exact_modulus_recovery_mixed hd _ hh'0
        (U := ModulusRecovery.hermiteCoeffs g) (V := ModulusRecovery.hermiteCoeffs f) hall
    refine ⟨a, ha, ?_⟩
    calc f = ModulusRecovery.hermiteExpansion (ModulusRecovery.hermiteCoeffs f) := hfU.symm
      _ = ModulusRecovery.hermiteExpansion (a • ModulusRecovery.hermiteCoeffs g) := by rw [hae]
      _ = a • ModulusRecovery.hermiteExpansion (ModulusRecovery.hermiteCoeffs g) :=
          ModulusRecovery.hermiteExpansion_smul a _
      _ = a • g := by rw [hgV]

/-- **Discrete phase retrieval for the STFT, unit scale** (corollary of Theorem 1.1).

For every `d ≥ 1` and every nonzero real polynomial `h` in `d` variables there is a subset
`S` of phase space `ℝ^d × ℝ^d` whose distinct points are at `phaseDistUnit` at least
`4√d/10⁷` from each other.  For `f, g ∈ L²(ℝ^d)`, equality of the STFT moduli
`|V_w f(x, ξ)| = |V_w g(x, ξ)|` for all `(x, ξ) ∈ S`, with the window
`w = h(x) e^{−|x|²/2}`, forces `f = θ g` almost everywhere for one unimodular constant `θ`. -/
theorem STFTDiscretePhaseRetrieval_unit (d : ℕ) (hd : 0 < d) (h : MvPolynomial (Fin d) ℝ)
    (hnonzero : h ≠ 0) :
    ∃ S : Set (RealVec d × RealVec d),
      UniformlyDiscretePhaseUnit (4 * Real.sqrt d / 10 ^ 7) S ∧
        ∀ f g : L2Real d,
          (∀ x ξ, (x, ξ) ∈ S →
            ‖stft (gaussWindowUnit h) f x ξ‖ = ‖stft (gaussWindowUnit h) g x ξ‖) →
            ∃ θ : ℂ, ‖θ‖ = 1 ∧ f = θ • g := by
  classical
  obtain ⟨c, -, hc_win⟩ := ModulusRecovery.gaussWindow_eq_sum h
  have hc : c ≠ 0 := by
    intro hc0
    refine ModulusRecovery.gaussWindow_ne_zero hnonzero ?_
    rw [hc_win, hc0]
    simp
  exact STFTDiscretePhaseRetrieval_unit_of_finite_window d hd _ c hc hc_win


/-- **Discrete phase retrieval for the STFT** (the paper's Theorem `thm:STFT`).

For every `d ≥ 1` and every nonzero real polynomial `h` in `d` variables there is a subset `S` of
phase space `ℝ^d × ℝ^d` whose distinct points are at Euclidean distance at least
`√d/10⁷` from
each other, such that for `f, g ∈ L²(ℝ^d)`, equality of the STFT moduli
`|V_w f(x, ξ)| = |V_w g(x, ξ)|` for all `(x, ξ) ∈ S`, with the window
`w = h(x) e^{−π|x|²}`, forces
`f = θ g` almost everywhere for one unimodular constant `θ`. -/
theorem STFTDiscretePhaseRetrieval (d : ℕ) (hd : 0 < d) (h : MvPolynomial (Fin d) ℝ)
    (hnonzero : h ≠ 0) :
    ∃ S : Set (RealVec d × RealVec d),
      UniformlyDiscretePhase (Real.sqrt d / 10 ^ 7) S ∧
        ∀ f g : L2Real d,
          (∀ x ξ, (x, ξ) ∈ S →
            ‖stft (gaussWindow h) f x ξ‖ = ‖stft (gaussWindow h) g x ξ‖) →
            ∃ θ : ℂ, ‖θ‖ = 1 ∧ f = θ • g := by
  classical
  have hcpos : (0 : ℝ) < sqrtTwoPi := sqrtTwoPi_pos
  have hc0 : sqrtTwoPi ≠ 0 := sqrtTwoPi_ne_zero
  -- the unit-scale corollary for the rescaled polynomial `h̃ = h(·/√(2π))`
  obtain ⟨S₀, hsep, hpr⟩ :=
    STFTDiscretePhaseRetrieval_unit d hd (rescalePoly sqrtTwoPi⁻¹ h)
      (rescalePoly_ne_zero (inv_ne_zero hc0) hnonzero)
  refine
    ⟨{p : RealVec d × RealVec d |
      (sqrtTwoPi • p.1, sqrtTwoPi⁻¹ • p.2) ∈ S₀}, ?_, ?_⟩
  · -- separation: the dilation multiplies the unit-scale distance by `√π ≤ 4`
    intro x ξ hxξ x' ξ' hxξ' hne
    have hne' :
        (sqrtTwoPi • x, sqrtTwoPi⁻¹ • ξ) ≠
          (sqrtTwoPi • x', sqrtTwoPi⁻¹ • ξ') := by
      intro heq
      refine hne ?_
      rw [Prod.mk.injEq] at heq ⊢
      exact ⟨smul_right_injective _ hc0 heq.1,
        smul_right_injective _ (inv_ne_zero hc0) heq.2⟩
    have hbound := hsep _ _ hxξ _ _ hxξ' hne'
    rw [phaseDistUnit_scaled] at hbound
    have hD : 0 ≤ Real.sqrt (‖x - x'‖ ^ 2 + ‖ξ - ξ'‖ ^ 2) := Real.sqrt_nonneg _
    have h4 : Real.sqrt Real.pi * Real.sqrt (‖x - x'‖ ^ 2 + ‖ξ - ξ'‖ ^ 2)
        ≤ 4 * Real.sqrt (‖x - x'‖ ^ 2 + ‖ξ - ξ'‖ ^ 2) :=
      mul_le_mul_of_nonneg_right sqrt_pi_le_four hD
    linarith
  · -- phase retrieval: transfer the hypothesis to the dilated signals
    intro f g hmod
    have hkey : ∀ u v : RealVec d, (u, v) ∈ S₀ →
        ‖stft (gaussWindowUnit (rescalePoly sqrtTwoPi⁻¹ h)) (dilate sqrtTwoPi⁻¹ f) u v‖
          = ‖stft (gaussWindowUnit (rescalePoly sqrtTwoPi⁻¹ h))
              (dilate sqrtTwoPi⁻¹ g) u v‖ := by
      intro u v huv
      have hmem : (sqrtTwoPi⁻¹ • u, sqrtTwoPi • v)
          ∈ {p : RealVec d × RealVec d |
            (sqrtTwoPi • p.1, sqrtTwoPi⁻¹ • p.2) ∈ S₀} := by
        simp only [Set.mem_setOf_eq, smul_inv_smul₀ hc0, inv_smul_smul₀ hc0]
        exact huv
      have hmoduv := hmod (sqrtTwoPi⁻¹ • u) (sqrtTwoPi • v) hmem
      rw [norm_stft_gaussWindow, norm_stft_gaussWindow, smul_inv_smul₀ hc0,
        inv_smul_smul₀ hc0] at hmoduv
      exact mul_left_cancel₀
        (ne_of_gt (inv_pos.mpr (dilateFactor_pos hcpos))) hmoduv
    obtain ⟨θ, hθ, hθeq⟩ := hpr _ _ hkey
    refine ⟨θ, hθ, ?_⟩
    calc f = dilate sqrtTwoPi (dilate sqrtTwoPi⁻¹ f) := (dilate_dilate_inv hcpos f).symm
      _ = dilate sqrtTwoPi (θ • dilate sqrtTwoPi⁻¹ g) := by rw [hθeq]
      _ = θ • dilate sqrtTwoPi (dilate sqrtTwoPi⁻¹ g) := dilate_smul hc0 θ _
      _ = θ • g := by rw [dilate_dilate_inv hcpos g]

end DiscretePR
