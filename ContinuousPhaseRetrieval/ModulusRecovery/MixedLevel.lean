import ContinuousPhaseRetrieval.ModulusRecovery.ExactModulusRecovery
import Definitions

/-!
# Mixed-level exact modulus recovery

The level-`κ` STFT/ambiguity argument of `ExactModulusRecovery.lean` is run once more
for the mixed-level basis `Ψ_{·, h}` of `Definitions.lean`.  The window is the finite
mixture `windowH h = ∑_q weight h q • φ_q` of the Hermite windows `φ_q = varphiKappa q`,
whose coefficients absorb both the conjugation in the STFT and the sign `(-1)^{|q|}` of
`stftModelPhase q`.  The STFT of a Hermite expansion against this window is then one
global phase times the Gaussian weight times the mixed evaluation `toFunH h`, so equal
moduli of `toFunH h U` and `toFunH h V` give equal spectrograms, hence equal ambiguity
functions (the mixed window's own ambiguity function is a phase-space polynomial times a
Gaussian and is nonzero at the origin, hence nonzero on a dense set), hence one global
unimodular phase between the coefficient families.
-/

noncomputable section

namespace ModulusRecovery

open MeasureTheory
open scoped RealInnerProductSpace

/-! ## The mixed window -/

/-- `hnorm h = (∑_q |h_q|²)^{1/2}`, the normalisation constant of `Ψ · h`. -/
def hnorm {d : Nat} (h : (Fin d → ℕ) →₀ ℂ) : ℝ :=
  Real.sqrt (∑ q ∈ h.support, ‖h q‖ ^ 2)

theorem hnorm_pos {d : Nat} {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0) : 0 < hnorm h := by
  have hne : h.support.Nonempty := Finsupp.support_nonempty_iff.mpr hnonzero
  obtain ⟨q, hq⟩ := hne
  have hqpos : 0 < ‖h q‖ ^ 2 := by
    have : h q ≠ 0 := Finsupp.mem_support_iff.mp hq
    positivity
  have hsum : 0 < ∑ q ∈ h.support, ‖h q‖ ^ 2 :=
    Finset.sum_pos' (fun i _ => by positivity) ⟨q, hq, hqpos⟩
  exact Real.sqrt_pos.mpr hsum

theorem hnorm_ne_zero {d : Nat} {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0) :
    ((hnorm h : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (hnorm_pos hnonzero))

/-- The window coefficient of level `q`: the sign `(-1)^{|q|}` of `stftModelPhase q`
is absorbed here, and the STFT conjugates the window. -/
def weight {d : Nat} (h : (Fin d → ℕ) →₀ ℂ) (q : Fin d → ℕ) : ℂ :=
  (-1 : ℂ) ^ (∑ i, q i) * star (h q) / ((hnorm h : ℝ) : ℂ)

theorem star_weight_mul_sign {d : Nat} (h : (Fin d → ℕ) →₀ ℂ) (q : Fin d → ℕ) :
    star (weight h q) * (-1 : ℂ) ^ (∑ i, q i) = h q / ((hnorm h : ℝ) : ℂ) := by
  have hs : star (((hnorm h : ℝ) : ℂ)) = ((hnorm h : ℝ) : ℂ) := Complex.conj_ofReal _
  have hsign : star ((-1 : ℂ) ^ (∑ i, q i)) = (-1 : ℂ) ^ (∑ i, q i) := by
    simp
  have hsq : ((-1 : ℂ) ^ (∑ i, q i)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [weight, star_div₀, star_mul', hs, hsign, star_star]
  field_simp
  rw [hsq, one_mul]

theorem weight_ne_zero {d : Nat} {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0)
    {q : Fin d → ℕ} (hq : q ∈ h.support) : weight h q ≠ 0 := by
  rw [weight]
  apply div_ne_zero _ (hnorm_ne_zero hnonzero)
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · simpa using (Finsupp.mem_support_iff.mp hq)

/-- The mixed window `w_h = ∑_q weight h q • φ_q ∈ L²(ℝ^d)`. -/
def windowH {d : Nat} (h : (Fin d → ℕ) →₀ ℂ) : L2Real d :=
  ∑ q ∈ h.support, weight h q • varphiKappa q

/-- The mixed-level evaluation of a coefficient family. -/
def toFunH {d : Nat} (h : (Fin d → ℕ) →₀ ℂ) (U : Coeffs d) : Cd d → ℂ :=
  fun z => ∑' α : Idx d, coeffAt U α * DiscretePR.Ψ α h z

/-! ## Linearity in the window -/

private theorem ae_comp_add_right {d : Nat} {f₁ f₂ : RealVec d → ℂ} (a : RealVec d)
    (h : f₁ =ᵐ[(volume : Measure (RealVec d))] f₂) :
    (fun t : RealVec d => f₁ (t + a)) =ᵐ[(volume : Measure (RealVec d))]
      fun t : RealVec d => f₂ (t + a) := by
  simpa [Function.comp_def] using
    ((MeasureTheory.measurePreserving_add_right
      (volume : Measure (RealVec d)) a).quasiMeasurePreserving).ae_eq_comp h

private theorem translateL2_add {d : Nat} (a : RealVec d) (f g : L2Real d) :
    translateL2 a (f + g) = translateL2 a f + translateL2 a g := by
  simp [translateL2]

private theorem translateL2_smul {d : Nat} (a : RealVec d) (c : ℂ) (f : L2Real d) :
    translateL2 a (c • f) = c • translateL2 a f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [translateL2_coeFn a (c • f),
    MeasureTheory.Lp.coeFn_smul c (translateL2 a f),
    ae_comp_add_right a (MeasureTheory.Lp.coeFn_smul c f),
    translateL2_coeFn a f] with t h1 h2 h3 h4
  rw [h1, h2, h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h4]

private theorem star_L2_add {d : Nat} (f g : L2Real d) :
    star (f + g) = star f + star g := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_star (f + g), MeasureTheory.Lp.coeFn_star f,
    MeasureTheory.Lp.coeFn_star g, MeasureTheory.Lp.coeFn_add f g,
    MeasureTheory.Lp.coeFn_add (star f) (star g)] with t hfg hf hg hadd hstaradd
  rw [hfg, hstaradd]
  simp only [Pi.star_apply, Pi.add_apply] at *
  rw [hadd, hf, hg]
  simp

private theorem star_L2_smul {d : Nat} (c : ℂ) (f : L2Real d) :
    star (c • f) = star c • star f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_star (c • f), MeasureTheory.Lp.coeFn_star f,
    MeasureTheory.Lp.coeFn_smul c f,
    MeasureTheory.Lp.coeFn_smul (star c) (star f)] with t hcf hf hsmul hsmul'
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul] at hcf hf hsmul hsmul' ⊢
  rw [hcf, hsmul', hsmul, hf, star_mul']

private theorem modulateL2_add {d : Nat} (ω : RealVec d) (f g : L2Real d) :
    modulateL2 ω (f + g) = modulateL2 ω f + modulateL2 ω g := by
  apply MeasureTheory.Lp.ext
  filter_upwards [modulateL2_coeFn ω (f + g), modulateL2_coeFn ω f,
    modulateL2_coeFn ω g, MeasureTheory.Lp.coeFn_add f g,
    MeasureTheory.Lp.coeFn_add (modulateL2 ω f) (modulateL2 ω g)] with t hfg hf hg hadd hmodadd
  rw [hfg, hmodadd]
  simp only [Pi.add_apply] at *
  rw [hf, hg, hadd]
  ring

private theorem modulateL2_smul {d : Nat} (ω : RealVec d) (c : ℂ) (f : L2Real d) :
    modulateL2 ω (c • f) = c • modulateL2 ω f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [modulateL2_coeFn ω (c • f), modulateL2_coeFn ω f,
    MeasureTheory.Lp.coeFn_smul c f,
    MeasureTheory.Lp.coeFn_smul c (modulateL2 ω f)] with t hcf hf hsmul hsmul'
  rw [hcf, hsmul']
  simp only [Pi.smul_apply, smul_eq_mul] at *
  rw [hsmul, hf]
  ring

theorem stftRep_window_add {d : Nat} (h₁ h₂ f : L2Real d) (ξ : PhaseSpace d) :
    stftRep (h₁ + h₂) f ξ = stftRep h₁ f ξ + stftRep h₂ f ξ := by
  rw [stftRep_eq_lpPairing, stftRep_eq_lpPairing, stftRep_eq_lpPairing,
    translateL2_add, star_L2_add, modulateL2_add, map_add]

theorem stftRep_window_smul {d : Nat} (c : ℂ) (h f : L2Real d) (ξ : PhaseSpace d) :
    stftRep (c • h) f ξ = star c * stftRep h f ξ := by
  rw [stftRep_eq_lpPairing, stftRep_eq_lpPairing, translateL2_smul, star_L2_smul,
    modulateL2_smul, map_smul, smul_eq_mul]

theorem stftRep_window_zero {d : Nat} (f : L2Real d) (ξ : PhaseSpace d) :
    stftRep (0 : L2Real d) f ξ = 0 := by
  simpa using stftRep_window_smul (0 : ℂ) (0 : L2Real d) f ξ

theorem stftRep_window_sum {d : Nat} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (h : ι → L2Real d) (f : L2Real d) (ξ : PhaseSpace d) :
    stftRep (∑ i ∈ s, c i • h i) f ξ = ∑ i ∈ s, star (c i) * stftRep (h i) f ξ := by
  classical
  induction s using Finset.induction with
  | empty => simp [stftRep_window_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, stftRep_window_add,
        stftRep_window_smul, ih]

theorem stftRep_signal_add {d : Nat} (h f₁ f₂ : L2Real d) (ξ : PhaseSpace d) :
    stftRep h (f₁ + f₂) ξ = stftRep h f₁ ξ + stftRep h f₂ ξ := by
  rw [stftRep_eq_lpPairing, stftRep_eq_lpPairing, stftRep_eq_lpPairing, map_add]
  rfl

theorem stftRep_signal_smul {d : Nat} (c : ℂ) (h f : L2Real d) (ξ : PhaseSpace d) :
    stftRep h (c • f) ξ = c * stftRep h f ξ := by
  rw [stftRep_eq_lpPairing, stftRep_eq_lpPairing, map_smul]
  rfl

theorem stftRep_signal_zero {d : Nat} (h : L2Real d) (ξ : PhaseSpace d) :
    stftRep h (0 : L2Real d) ξ = 0 := by
  rw [stftRep_eq_lpPairing, map_zero]
  rfl

theorem stftRep_signal_sum {d : Nat} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → L2Real d) (h : L2Real d) (ξ : PhaseSpace d) :
    stftRep h (∑ i ∈ s, c i • f i) ξ = ∑ i ∈ s, c i * stftRep h (f i) ξ := by
  classical
  induction s using Finset.induction with
  | empty => simp [stftRep_signal_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, stftRep_signal_add,
        stftRep_signal_smul, ih]

/-! ## The STFT model with an explicit phase -/

/-! ## The mixed STFT model -/

private theorem Psi_eq {d : Nat} (α : Fin d → ℕ) (h : (Fin d → ℕ) →₀ ℂ) (z : Cd d) :
    DiscretePR.Ψ α h z =
      (((hnorm h : ℝ) : ℂ))⁻¹ * ∑ q ∈ h.support, h q * Phi q α z := rfl

theorem toFunH_eq_finsetSum {d : Nat} (h : (Fin d → ℕ) →₀ ℂ) (U : Coeffs d) (z : Cd d) :
    toFunH h U z = ∑ q ∈ h.support, (h q / ((hnorm h : ℝ) : ℂ)) * toFun q U z := by
  have hsum : ∀ q ∈ h.support,
      Summable (fun α : Idx d =>
        (h q / ((hnorm h : ℝ) : ℂ)) * (coeffAt U α * Phi q α z)) :=
    fun q _ => (summable_coeffs_eval_mul q U z).mul_left _
  have hstep : ∀ q ∈ h.support,
      (h q / ((hnorm h : ℝ) : ℂ)) * toFun q U z
        = ∑' α : Idx d, (h q / ((hnorm h : ℝ) : ℂ)) * (coeffAt U α * Phi q α z) := by
    intro q _
    rw [toFun, tsum_mul_left]
  rw [Finset.sum_congr rfl hstep, ← Summable.tsum_finsetSum hsum, toFunH]
  apply tsum_congr
  intro α
  rw [Psi_eq, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [div_eq_mul_inv]
  ring

theorem stft_model_eq_mixed {d : Nat} (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ)
    (U : Coeffs d) (ξ : PhaseSpace d) :
    stftRep (windowH h) (hermiteExpansion U) ξ =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
        (((gaussWeight ξ : ℝ) : ℂ) * toFunH h U (phaseToC ξ)) := by
  have hterm : ∀ q ∈ h.support,
      star (weight h q) * stftRep (varphiKappa q) (hermiteExpansion U) ξ
        = Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
            ((gaussWeight ξ : ℝ) : ℂ) *
            ((h q / ((hnorm h : ℝ) : ℂ)) * toFun q U (phaseToC ξ)) := by
    intro q _
    have hw := star_weight_mul_sign h q
    rw [stft_model_eq hd q U ξ]
    simp only [stftModelPhase]
    calc
      star (weight h q) *
          ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun i => q i) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
            (((gaussWeight ξ : ℝ) : ℂ) * toFun q U (phaseToC ξ)))
          = (star (weight h q) *
              (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun i => q i)) *
            (Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
              (((gaussWeight ξ : ℝ) : ℂ) * toFun q U (phaseToC ξ))) := by ring
      _ = Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
            ((gaussWeight ξ : ℝ) : ℂ) *
            ((h q / ((hnorm h : ℝ) : ℂ)) * toFun q U (phaseToC ξ)) := by
            rw [hw]; ring
  rw [windowH, stftRep_window_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    toFunH_eq_finsetSum]
  ring

theorem stft_model_modulus_mixed {d : Nat} (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ)
    (U : Coeffs d) (ξ : PhaseSpace d) :
    ‖stftRep (windowH h) (hermiteExpansion U) ξ‖ =
      gaussWeight ξ * ‖toFunH h U (phaseToC ξ)‖ := by
  rw [stft_model_eq_mixed hd h U ξ, norm_mul, norm_mul]
  have hexp :
      ‖Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre :
        (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [hexp, one_mul]
  congr 1
  simp [abs_of_pos (gaussWeight_pos ξ)]

/-! ## The ambiguity function from the STFT -/

theorem ambiguityRep_eq_exp_mul_stftRep {d : Nat} (f h : L2Real d) (ξ : PhaseSpace d) :
    ambiguityRep f h ξ =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
        stftRep h f ξ := by
  set c : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) with hc
  set a : RealVec d := (1 / 2 : ℝ) • ξ.1 with ha
  set G : RealVec d → ℂ := fun s =>
    c * ((f : RealVec d → ℂ) s * star ((h : RealVec d → ℂ) (s - ξ.1)) *
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 s : ℝ) : ℂ))) with hG
  have key : ∀ t : RealVec d,
      G (t + a) =
        (f : RealVec d → ℂ) (t + a) * star ((h : RealVec d → ℂ) (t - a)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ)) := by
    intro t
    have ha2 : t + a - ξ.1 = t - a := by
      rw [ha]; module
    have hinner :
        (inner ℝ ξ.2 (t + a) : ℝ)
          = (inner ℝ ξ.2 t : ℝ) + (1 / 2 : ℝ) * (inner ℝ ξ.1 ξ.2 : ℝ) := by
      rw [inner_add_right, ha, real_inner_smul_right, real_inner_comm ξ.2 ξ.1]
    have hsplit :
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 (t + a) : ℝ) : ℂ))
          = Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ)) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, hinner]
      push_cast
      ring_nf
    have hcc :
        c * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) = 1 := by
      rw [hc, ← Complex.exp_add,
        show (Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ) +
            -(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ) = 0 from by ring,
        Complex.exp_zero]
    rw [hG]
    simp only
    rw [ha2, hsplit]
    calc
      c * ((f : RealVec d → ℂ) (t + a) * star ((h : RealVec d → ℂ) (t - a)) *
          (Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ)) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ))))
          = (c * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ))) *
            ((f : RealVec d → ℂ) (t + a) * star ((h : RealVec d → ℂ) (t - a)) *
              Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
                ((inner ℝ ξ.2 t : ℝ) : ℂ))) := by ring
      _ = _ := by rw [hcc, one_mul]
  have hamb : ambiguityRep f h ξ = ∫ t : RealVec d, G (t + a) := by
    unfold ambiguityRep
    exact (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall key)).symm
  rw [hamb, MeasureTheory.integral_add_right_eq_self G a, hG]
  rw [MeasureTheory.integral_const_mul]
  rfl

theorem ambiguityRep_sum_sum {d : Nat} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (h : ι → L2Real d) (ξ : PhaseSpace d) :
    ambiguityRep (∑ i ∈ s, c i • h i) (∑ j ∈ s, c j • h j) ξ
      = ∑ i ∈ s, ∑ j ∈ s, c i * star (c j) * ambiguityRep (h i) (h j) ξ := by
  rw [ambiguityRep_eq_exp_mul_stftRep, stftRep_window_sum, Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [stftRep_signal_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ambiguityRep_eq_exp_mul_stftRep]
  ring

theorem ambiguityRep_hermite {d : Nat} (hd : 0 < d) (alpha kappa : MultiIndex d)
    (ξ : PhaseSpace d) :
    ambiguityRep (varphiKappa alpha) (varphiKappa kappa) ξ =
      (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun i => kappa i) *
        (((gaussWeight ξ : ℝ) : ℂ) * Phi kappa alpha (phaseToC ξ)) := by
  have hb : stftRep (varphiKappa kappa) (varphiKappa alpha) ξ =
      stftModelPhase kappa ξ *
        (((gaussWeight ξ : ℝ) : ℂ) * Phi kappa alpha (phaseToC ξ)) :=
    stft_model_basis_formula hd kappa alpha ξ
  have hcc :
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add,
      show (Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ) +
          -(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ) = 0 from by ring,
      Complex.exp_zero]
  rw [ambiguityRep_eq_exp_mul_stftRep, hb]
  simp only [stftModelPhase]
  calc
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
        ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun i => kappa i) *
          Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
          (((gaussWeight ξ : ℝ) : ℂ) * Phi kappa alpha (phaseToC ξ)))
        = (Complex.exp ((Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ)) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ))) *
          ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun i => kappa i) *
            (((gaussWeight ξ : ℝ) : ℂ) * Phi kappa alpha (phaseToC ξ))) := by ring
    _ = _ := by rw [hcc, one_mul]

/-! ## The mixed window's ambiguity function -/

/-- The polynomial part of the mixed window's ambiguity function. -/
def PH {d : Nat} (h : (Fin d → ℕ) →₀ ℂ) : PhaseSpace d → ℂ := fun ξ =>
  ∑ q ∈ h.support, ∑ q' ∈ h.support,
    weight h q * star (weight h q') *
      (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun i => q' i) *
      Phi q' q (phaseToC ξ)

theorem windowAmbiguity_factorization_mixed {d : Nat} (hd : 0 < d)
    (h : (Fin d → ℕ) →₀ ℂ) (ξ : PhaseSpace d) :
    ambiguityRep (windowH h) (windowH h) ξ =
      PH h ξ * Complex.ofReal (Real.exp (-(gaussQuad ξ))) := by
  rw [windowH, ambiguityRep_sum_sum, PH, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q' _
  rw [ambiguityRep_hermite hd q q' ξ]
  simp only [gaussWeight]
  ring

theorem PH_isPolynomial {d : Nat} (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) :
    IsPhaseSpacePolynomial (PH h) := by
  let _ := hd
  refine ⟨∑ q ∈ h.support, ∑ q' ∈ h.support,
    MvPolynomial.C (weight h q * star (weight h q') *
        (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun i => q' i)) *
      PhiPhaseToCPoly q' q, ?_⟩
  intro ξ
  rw [PH]
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, PhiPhaseToCPoly_eval]

theorem ambiguityRep_self_zero {d : Nat} (w : L2Real d) :
    ambiguityRep w w ((0 : RealVec d), (0 : RealVec d)) = inner ℂ w w := by
  have h1 : ambiguityRep w w ((0 : RealVec d), (0 : RealVec d))
      = ∫ t : RealVec d,
          (w : RealVec d → ℂ) t * star ((w : RealVec d → ℂ) t) := by
    unfold ambiguityRep
    simp
  rw [h1, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  change (w : RealVec d → ℂ) t * star ((w : RealVec d → ℂ) t)
      = inner ℂ ((w : RealVec d → ℂ) t) ((w : RealVec d → ℂ) t)
  rw [RCLike.inner_apply, Complex.star_def, mul_comm]

theorem windowH_ne_zero {d : Nat} {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0) :
    windowH h ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ := Finsupp.support_nonempty_iff.mpr hnonzero
  have hli : LinearIndependent ℂ (fun alpha : Idx d => realHermiteTensorL2 alpha) :=
    (realHermiteTensorL2_orthonormal (d := d)).linearIndependent
  have hsum : ∑ i ∈ h.support, weight h i • realHermiteTensorL2 i = 0 := hzero
  exact weight_ne_zero hnonzero hq
    (linearIndependent_iff'.mp hli h.support (weight h) hsum q hq)

theorem PH_zero_ne {d : Nat} (hd : 0 < d) {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0) :
    PH h ((0 : RealVec d), (0 : RealVec d)) ≠ 0 := by
  have hfac := windowAmbiguity_factorization_mixed hd h ((0 : RealVec d), (0 : RealVec d))
  have hq0 : gaussQuad ((0 : RealVec d), (0 : RealVec d)) = (0 : ℝ) := by
    simp [gaussQuad]
  rw [hq0, ambiguityRep_self_zero] at hfac
  simp only [neg_zero, Real.exp_zero, Complex.ofReal_one, mul_one] at hfac
  intro hPH
  rw [hPH] at hfac
  exact windowH_ne_zero hnonzero (inner_self_eq_zero.mp hfac)

theorem windowAmbiguity_dense_nonvanishing_mixed {d : Nat} (hd : 0 < d)
    {h : (Fin d → ℕ) →₀ ℂ} (hnonzero : h ≠ 0) :
    Dense {ξ : PhaseSpace d | ambiguityRep (windowH h) (windowH h) ξ ≠ 0} := by
  refine (dense_ne_zero_of_phaseSpace_polynomial (PH_isPolynomial hd h) ?_).mono ?_
  · exact ⟨(0, 0), PH_zero_ne hd hnonzero⟩
  · intro ξ hP
    change ambiguityRep (windowH h) (windowH h) ξ ≠ 0
    change PH h ξ ≠ 0 at hP
    rw [windowAmbiguity_factorization_mixed hd h ξ]
    exact mul_ne_zero hP (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

/-! ## The chain -/

theorem exact_modulus_recovery_mixed {d : Nat} (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ)
    (hnonzero : h ≠ 0) {U V : Coeffs d}
    (hmod : ∀ z, ‖toFunH h U z‖ = ‖toFunH h V z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ V = w • U := by
  have hstft : ∀ ξ : PhaseSpace d,
      ‖stftRep (windowH h) (hermiteExpansion U) ξ‖ =
        ‖stftRep (windowH h) (hermiteExpansion V) ξ‖ := by
    intro ξ
    rw [stft_model_modulus_mixed hd h U ξ, stft_model_modulus_mixed hd h V ξ,
      hmod (phaseToC ξ)]
  exact ambiguity_eq_to_coeffs_phase hd
    (spectrogram_eq_of_equal_modulus_to_ambiguity_eq_of_window (windowH h)
      (windowAmbiguity_dense_nonvanishing_mixed hd hnonzero) hstft)

end ModulusRecovery
