import DiscretePhaseRetrieval.UnitScale
import ContinuousPhaseRetrieval.ModulusRecovery.WindowExpansion

/-!
# The real-side dilation bridge `t = s/√(2π)`

The Hermite functions of `ContinuousPhaseRetrieval/` carry the Gaussian `e^{-|t|²/2}`, so the
STFT corollary is first proved in that *unit scale* (`DiscretePhaseRetrieval/UnitScale.lean`):
window `gaussWindowUnit h = h(t) e^{-|t|²/2}`, phase-space distance `phaseDistUnit`.  The public
corollary is stated, as in the paper, for the window `gaussWindow h = h(t) e^{-π|t|²}` and the
plain Euclidean distance on phase space; the Fock side of the development is untouched.  The two
are related by the unitary dilation `t = s/√(2π)` of `L²(ℝ^d)`,

`(D_c f)(t) = c^{d/2} f(c t)`,  `c = √(2π)`,

which is implemented here as `dilate`.  The three facts that the bridge needs are

* the covariance `stft_dilate`: `V_{D_c w}(D_c f)(x, ξ) = V_w f(c x, ξ/c)`;
* the window identity `dilate_gaussWindowUnit`: `D_c (gaussWindowUnit h̃) = c^{d/2} • gaussWindow h`
  for the rescaled polynomial `h̃ = rescalePoly c⁻¹ h`, `h̃(t) = h(t/c)`, because
  `π |t|² = |c t|²/2`;
* the metric identity `phaseDistUnit_scaled`: under `(x, ξ) ↦ (c x, ξ/c)` the unit-scale
  phase-space distance becomes `√π` times the Euclidean one.

Consequently a unit-scale separation `ε` becomes a public separation `ε/√π ≥ ε/4`
(`sqrt_pi_le_four`), which is where the constant `√d/10⁷` of the public STFT corollary
comes from (`STFT.lean`, `STFTDiscretePhaseRetrieval`).
-/

open MeasureTheory

noncomputable section

namespace DiscretePR

theorem sqrt_pi_pos : 0 < Real.sqrt Real.pi :=
  Real.sqrt_pos.mpr Real.pi_pos

theorem sqrt_pi_le_four : Real.sqrt Real.pi ≤ 4 := by
  have h : Real.sqrt Real.pi ≤ Real.sqrt 16 :=
    Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
  rwa [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)] at h

variable {d : ℕ}

/-! ## `L²` transfer along a dilation of `ℝ^d` -/

/-- Square-integrability is preserved by precomposition with a nonzero dilation `t ↦ c t`:
the map `t ↦ c t` pushes the Lebesgue measure of `ℝ^d` to a constant multiple of itself. -/
theorem memLp_comp_smul {c : ℝ} (hc : c ≠ 0) {f : RealVec d → ℂ}
    (hf : MemLp f 2 (volume : Measure (RealVec d))) :
    MemLp (fun t : RealVec d => f (c • t)) 2 (volume : Measure (RealVec d)) := by
  have hf' : MemLp f 2 (Measure.map (fun t : RealVec d => c • t) volume) := by
    rw [Measure.map_addHaar_smul volume hc]
    exact hf.smul_measure (by simp)
  exact hf'.comp_of_map ((continuous_const_smul c).measurable.aemeasurable)

/-- Almost-everywhere equality is preserved by precomposition with a nonzero dilation. -/
theorem ae_comp_smul {c : ℝ} (hc : c ≠ 0) {g₁ g₂ : RealVec d → ℂ}
    (hg : g₁ =ᵐ[(volume : Measure (RealVec d))] g₂) :
    (fun t : RealVec d => g₁ (c • t)) =ᵐ[(volume : Measure (RealVec d))]
      fun t : RealVec d => g₂ (c • t) :=
  (Measure.quasiMeasurePreserving_smul volume hc).ae_eq_comp hg

/-- Almost-everywhere equality is preserved by precomposition with a translation. -/
theorem ae_comp_sub {g₁ g₂ : RealVec d → ℂ}
    (hg : g₁ =ᵐ[(volume : Measure (RealVec d))] g₂) (x : RealVec d) :
    (fun t : RealVec d => g₁ (t - x)) =ᵐ[(volume : Measure (RealVec d))]
      fun t : RealVec d => g₂ (t - x) :=
  (measurePreserving_sub_right (volume : Measure (RealVec d)) x).quasiMeasurePreserving.ae_eq_comp
    hg

/-! ## The unitary dilation `D_c` of `L²(ℝ^d)` -/

/-- The `L²`-normalising factor `c^{d/2}` of the dilation `D_c` of `L²(ℝ^d)`. -/
def dilateFactor (c : ℝ) (d : ℕ) : ℝ := Real.sqrt (c ^ d)

/-- `c^{d/2} > 0` for `c > 0`. -/
theorem dilateFactor_pos {c : ℝ} (hc : 0 < c) : 0 < dilateFactor c d :=
  Real.sqrt_pos.mpr (pow_pos hc d)

/-- `c^{d/2} · c^{d/2} = c^d`. -/
theorem dilateFactor_mul_self {c : ℝ} (hc : 0 ≤ c) :
    dilateFactor c d * dilateFactor c d = c ^ d :=
  Real.mul_self_sqrt (pow_nonneg hc d)

/-- `c^{d/2} · (c⁻¹)^{d/2} = 1`. -/
theorem dilateFactor_mul_inv {c : ℝ} (hc : 0 < c) :
    dilateFactor c d * dilateFactor c⁻¹ d = 1 := by
  rw [dilateFactor, dilateFactor, ← Real.sqrt_mul (pow_nonneg hc.le d), ← mul_pow,
    mul_inv_cancel₀ (ne_of_gt hc), one_pow, Real.sqrt_one]

/-- The dilation `(D_c f)(t) = c^{d/2} f(c t)` of `L²(ℝ^d)`; for `c > 0` it is a unitary
operator.  (For `c ≠ 0` the `MemLp` branch is the one taken, by `dilate_coe`; the `if` only
keeps the definition proof-free.) -/
def dilate (c : ℝ) (f : L2Real d) : L2Real d := by
  classical
  exact if hL2 : MemLp (fun t : RealVec d =>
      ((dilateFactor c d : ℝ) : ℂ) * (f : RealVec d → ℂ) (c • t)) 2 volume
    then hL2.toLp _ else 0

/-- The function `t ↦ c^{d/2} f(c t)` is square-integrable. -/
theorem dilate_memLp {c : ℝ} (hc : c ≠ 0) (f : L2Real d) :
    MemLp (fun t : RealVec d => ((dilateFactor c d : ℝ) : ℂ) * (f : RealVec d → ℂ) (c • t)) 2
      (volume : Measure (RealVec d)) :=
  (memLp_comp_smul hc (Lp.memLp f)).const_mul _

/-- `D_c f` is represented by `t ↦ c^{d/2} f(c t)`. -/
theorem dilate_coe {c : ℝ} (hc : c ≠ 0) (f : L2Real d) :
    (dilate c f : RealVec d → ℂ) =ᵐ[(volume : Measure (RealVec d))]
      fun t : RealVec d => ((dilateFactor c d : ℝ) : ℂ) * (f : RealVec d → ℂ) (c • t) := by
  have hmem := dilate_memLp hc f
  have hdef : dilate c f = hmem.toLp
      (fun t : RealVec d => ((dilateFactor c d : ℝ) : ℂ) * (f : RealVec d → ℂ) (c • t)) := by
    rw [dilate]
    exact dif_pos hmem
  rw [hdef]
  exact hmem.coeFn_toLp

/-- `D_c` is homogeneous: `D_c (θ f) = θ D_c f`. -/
theorem dilate_smul {c : ℝ} (hc : c ≠ 0) (θ : ℂ) (f : L2Real d) :
    dilate c (θ • f) = θ • dilate c f := by
  refine Lp.ext ?_
  filter_upwards [dilate_coe hc (θ • f), dilate_coe hc f,
    ae_comp_smul hc (Lp.coeFn_smul θ f), Lp.coeFn_smul θ (dilate c f)] with t ht1 ht2 ht3 ht4
  simp only [ht1, ht3, ht4, Pi.smul_apply, ht2, smul_eq_mul]
  ring

/-- `D_c` inverts `D_{c⁻¹}`: the dilation is invertible with inverse `D_{c⁻¹}`. -/
theorem dilate_dilate_inv {c : ℝ} (hc : 0 < c) (f : L2Real d) :
    dilate c (dilate c⁻¹ f) = f := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  refine Lp.ext ?_
  filter_upwards [dilate_coe hc0 (dilate c⁻¹ f),
    ae_comp_smul hc0 (dilate_coe (inv_ne_zero hc0) f)] with t ht1 ht2
  rw [ht1, ht2, inv_smul_smul₀ hc0, ← mul_assoc, ← Complex.ofReal_mul,
    dilateFactor_mul_inv hc, Complex.ofReal_one, one_mul]

/-! ## The covariance of the STFT under dilations -/

/-- The STFT is covariant under the dilation: `V_{D_c w}(D_c f)(x, ξ) = V_w f(c x, ξ/c)`.
The two normalising factors `c^{d/2}` and the Jacobian `c^{-d}` of the substitution cancel, and
`⟪ξ/c, c t⟫ = ⟪ξ, t⟫` keeps the kernel unchanged. -/
theorem stft_dilate {c : ℝ} (hc : 0 < c) (w f : L2Real d) (x ξ : RealVec d) :
    stft (dilate c w) (dilate c f) x ξ = stft w f (c • x) (c⁻¹ • ξ) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinner : ∀ t : RealVec d, (inner ℝ (c⁻¹ • ξ) (c • t) : ℝ) = (inner ℝ ξ t : ℝ) := by
    intro t
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hae : (fun t : RealVec d => (dilate c f : RealVec d → ℂ) t *
        star ((dilate c w : RealVec d → ℂ) (t - x)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ t : ℝ) : ℂ)))
      =ᵐ[(volume : Measure (RealVec d))]
      fun t : RealVec d => ((dilateFactor c d * dilateFactor c d : ℝ) : ℂ) *
        ((f : RealVec d → ℂ) (c • t) *
          star ((w : RealVec d → ℂ) (c • t - c • x)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ (c⁻¹ • ξ) (c • t) : ℝ) : ℂ))) := by
    filter_upwards [dilate_coe hc0 f, ae_comp_sub (dilate_coe hc0 w) x] with t ht1 ht2
    rw [ht1, ht2, smul_sub, hinner t]
    simp only [Complex.ofReal_mul, star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  have hL : stft (dilate c w) (dilate c f) x ξ
      = ∫ t : RealVec d, ((dilateFactor c d * dilateFactor c d : ℝ) : ℂ) *
          ((f : RealVec d → ℂ) (c • t) *
            star ((w : RealVec d → ℂ) (c • t - c • x)) *
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
              ((inner ℝ (c⁻¹ • ξ) (c • t) : ℝ) : ℂ))) := integral_congr_ae hae
  have hR : stft w f (c • x) (c⁻¹ • ξ)
      = ∫ s : RealVec d, (f : RealVec d → ℂ) s *
          star ((w : RealVec d → ℂ) (s - c • x)) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
            ((inner ℝ (c⁻¹ • ξ) s : ℝ) : ℂ)) := rfl
  rw [hL, hR, integral_const_mul,
    Measure.integral_comp_smul (volume : Measure (RealVec d))
      (fun s : RealVec d => (f : RealVec d → ℂ) s *
        star ((w : RealVec d → ℂ) (s - c • x)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ (c⁻¹ • ξ) s : ℝ) : ℂ))) c,
    finrank_euclideanSpace_fin, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c ^ d)⁻¹),
    Complex.real_smul, dilateFactor_mul_self hc.le, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (by positivity : (c : ℝ) ^ d ≠ 0), Complex.ofReal_one, one_mul]

/-- The STFT is conjugate-linear in the window. -/
theorem stft_window_smul (a : ℂ) (w f : L2Real d) (x ξ : RealVec d) :
    stft (a • w) f x ξ = star a * stft w f x ξ :=
  ModulusRecovery.stftRep_window_smul a w f (x, ξ)

/-! ## The rescaled polynomial -/

/-- The rescaled polynomial `(rescalePoly c h)(t) = h(c t)`. -/
def rescalePoly (c : ℝ) (h : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C c * MvPolynomial.X i) h

/-- Evaluation of the rescaled polynomial: `(rescalePoly c h)(t) = h(c t)`. -/
theorem eval_rescalePoly (c : ℝ) (h : MvPolynomial (Fin d) ℝ) (t : Fin d → ℝ) :
    MvPolynomial.eval t (rescalePoly c h) = MvPolynomial.eval (c • t) h := by
  have key := MvPolynomial.comp_aeval_apply
    (f := fun i : Fin d => MvPolynomial.C c * (MvPolynomial.X i : MvPolynomial (Fin d) ℝ))
    (MvPolynomial.aeval t) h
  have hfun : (fun i : Fin d =>
      (MvPolynomial.aeval t) (MvPolynomial.C c * (MvPolynomial.X i : MvPolynomial (Fin d) ℝ)))
      = c • t := by
    funext i
    simp
  rw [hfun] at key
  simpa [rescalePoly] using key

/-- Rescaling by a nonzero factor preserves nonvanishing of a polynomial. -/
theorem rescalePoly_ne_zero {c : ℝ} (hc : c ≠ 0) {h : MvPolynomial (Fin d) ℝ} (hh : h ≠ 0) :
    rescalePoly c h ≠ 0 := by
  intro hzero
  refine hh (MvPolynomial.funext fun v => ?_)
  have key := eval_rescalePoly c h (c⁻¹ • v)
  rw [hzero, smul_smul, mul_inv_cancel₀ hc, one_smul, map_zero] at key
  rw [map_zero]
  exact key.symm

/-! ## The dilation parameter `√(2π)` and the window identity -/

/-- The dilation parameter `c = √(2π)` relating the unit scale to the Gröchenig–Folland
convention: `π |t|² = |c t|² / 2`. -/
def sqrtTwoPi : ℝ := Real.sqrt (2 * Real.pi)

/-- `√(2π) > 0`. -/
theorem sqrtTwoPi_pos : 0 < sqrtTwoPi := Real.sqrt_pos.mpr (by positivity)

/-- `√(2π) ≠ 0`. -/
theorem sqrtTwoPi_ne_zero : sqrtTwoPi ≠ 0 := ne_of_gt sqrtTwoPi_pos

/-- `(√(2π))² = 2π`. -/
theorem sq_sqrtTwoPi : sqrtTwoPi ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)

/-- The representative `h(t) e^{-π|t|²}` of the public Gaussian window `gaussWindow h`. -/
def gaussWindowRep (h : MvPolynomial (Fin d) ℝ) : RealVec d → ℂ :=
  fun x : RealVec d =>
    ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * Real.exp (-Real.pi * ‖x‖ ^ 2)

/-- Pointwise window identity: the unit-scale window `h̃(t) e^{-|t|²/2}` of the rescaled
polynomial `h̃ = rescalePoly (√(2π))⁻¹ h`, evaluated at `√(2π) t`, is `h(t) e^{-π|t|²}`. -/
theorem gaussWindowRep_smul (h : MvPolynomial (Fin d) ℝ) (t : RealVec d) :
    ModulusRecovery.gaussWindowRep (rescalePoly sqrtTwoPi⁻¹ h) (sqrtTwoPi • t)
      = gaussWindowRep h t := by
  have harg : (sqrtTwoPi⁻¹ • fun i : Fin d => (sqrtTwoPi • t) i) = fun i : Fin d => t i := by
    funext i
    have hne : sqrtTwoPi ≠ 0 := sqrtTwoPi_ne_zero
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
  have hnorm : Real.exp (-‖sqrtTwoPi • t‖ ^ 2 / 2) = Real.exp (-Real.pi * ‖t‖ ^ 2) := by
    congr 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos sqrtTwoPi_pos, mul_pow, sq_sqrtTwoPi]
    ring
  rw [ModulusRecovery.gaussWindowRep_apply, eval_rescalePoly, harg, hnorm]
  rfl

/-- The representative of the public window is square-integrable: it is the unit-scale window
of the rescaled polynomial, dilated by `√(2π)`. -/
theorem gaussWindowRep_memLp (h : MvPolynomial (Fin d) ℝ) :
    MemLp (gaussWindowRep h) 2 (volume : Measure (RealVec d)) := by
  have hbase : MemLp (fun t : RealVec d =>
      ModulusRecovery.gaussWindowRep (rescalePoly sqrtTwoPi⁻¹ h) (sqrtTwoPi • t)) 2
        (volume : Measure (RealVec d)) :=
    memLp_comp_smul sqrtTwoPi_ne_zero
      (ModulusRecovery.gaussWindowRep_memLp (rescalePoly sqrtTwoPi⁻¹ h))
  have hfun : (fun t : RealVec d =>
      ModulusRecovery.gaussWindowRep (rescalePoly sqrtTwoPi⁻¹ h) (sqrtTwoPi • t))
      = gaussWindowRep h := funext (gaussWindowRep_smul h)
  rwa [hfun] at hbase

/-- The `MemLp` branch in the definition of `gaussWindow` is the one taken. -/
theorem gaussWindow_eq_toLp (h : MvPolynomial (Fin d) ℝ) :
    gaussWindow h = (gaussWindowRep_memLp h).toLp (gaussWindowRep h) := by
  have hmem := gaussWindowRep_memLp h
  rw [gaussWindow]
  exact dif_pos hmem

/-- The public window is represented by `h(t) e^{-π|t|²}`. -/
theorem gaussWindow_coe (h : MvPolynomial (Fin d) ℝ) :
    (gaussWindow h : RealVec d → ℂ) =ᵐ[(volume : Measure (RealVec d))] gaussWindowRep h := by
  rw [gaussWindow_eq_toLp]
  exact MemLp.coeFn_toLp _

/-- The unit-scale window is represented by `h(t) e^{-|t|²/2}`. -/
theorem gaussWindowUnit_coe (h : MvPolynomial (Fin d) ℝ) :
    (gaussWindowUnit h : RealVec d → ℂ) =ᵐ[(volume : Measure (RealVec d))]
      ModulusRecovery.gaussWindowRep h := by
  rw [ModulusRecovery.gaussWindow_eq_toLp]
  exact MemLp.coeFn_toLp _

/-- **The window identity.**  Dilating the unit-scale window of the rescaled polynomial
`h̃ = rescalePoly (√(2π))⁻¹ h` by `c = √(2π)` gives the public window up to the positive real
factor `c^{d/2}`:  `D_c (h̃(t) e^{-|t|²/2}) = c^{d/2} · h(t) e^{-π|t|²}`. -/
theorem dilate_gaussWindowUnit (h : MvPolynomial (Fin d) ℝ) :
    dilate sqrtTwoPi (gaussWindowUnit (rescalePoly sqrtTwoPi⁻¹ h))
      = ((dilateFactor sqrtTwoPi d : ℝ) : ℂ) • gaussWindow h := by
  refine Lp.ext ?_
  filter_upwards [dilate_coe sqrtTwoPi_ne_zero (gaussWindowUnit (rescalePoly sqrtTwoPi⁻¹ h)),
    ae_comp_smul sqrtTwoPi_ne_zero (gaussWindowUnit_coe (rescalePoly sqrtTwoPi⁻¹ h)),
    Lp.coeFn_smul ((dilateFactor sqrtTwoPi d : ℝ) : ℂ) (gaussWindow h),
    gaussWindow_coe h] with t ht1 ht2 ht3 ht4
  rw [ht1, ht2, gaussWindowRep_smul, ht3, Pi.smul_apply, ht4, smul_eq_mul]

/-! ## The STFT with the public window -/

/-- **The STFT bridge.**  With `c = √(2π)` and `h̃ = rescalePoly c⁻¹ h`, the STFT with the
public window `h(t) e^{-π|t|²}` is, up to the positive real factor `c^{-d/2}`, the unit-scale
STFT of the dilated signal at the dilated phase-space point. -/
theorem stft_gaussWindow (h : MvPolynomial (Fin d) ℝ) (f : L2Real d) (x ξ : RealVec d) :
    stft (gaussWindow h) f x ξ
      = ((dilateFactor sqrtTwoPi d : ℝ) : ℂ)⁻¹ *
          stft (gaussWindowUnit (rescalePoly sqrtTwoPi⁻¹ h))
            (dilate sqrtTwoPi⁻¹ f) (sqrtTwoPi • x) (sqrtTwoPi⁻¹ • ξ) := by
  have hA : ((dilateFactor sqrtTwoPi d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (dilateFactor_pos sqrtTwoPi_pos)
  have hw : gaussWindow h
      = (((dilateFactor sqrtTwoPi d : ℝ) : ℂ)⁻¹) •
          dilate sqrtTwoPi (gaussWindowUnit (rescalePoly sqrtTwoPi⁻¹ h)) := by
    rw [dilate_gaussWindowUnit, smul_smul, inv_mul_cancel₀ hA, one_smul]
  have hf : f = dilate sqrtTwoPi (dilate sqrtTwoPi⁻¹ f) :=
    (dilate_dilate_inv sqrtTwoPi_pos f).symm
  rw [hw]
  nth_rewrite 1 [hf]
  rw [stft_window_smul, stft_dilate sqrtTwoPi_pos]
  congr 1
  rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv]

/-- The modulus form of the STFT bridge. -/
theorem norm_stft_gaussWindow (h : MvPolynomial (Fin d) ℝ) (f : L2Real d) (x ξ : RealVec d) :
    ‖stft (gaussWindow h) f x ξ‖
      = (dilateFactor sqrtTwoPi d)⁻¹ *
          ‖stft (gaussWindowUnit (rescalePoly sqrtTwoPi⁻¹ h))
            (dilate sqrtTwoPi⁻¹ f) (sqrtTwoPi • x) (sqrtTwoPi⁻¹ • ξ)‖ := by
  rw [stft_gaussWindow, norm_mul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (dilateFactor_pos sqrtTwoPi_pos))]

/-! ## The phase-space metric under the dilation -/

/-- **The metric identity.**  Under `(x, ξ) ↦ (√(2π) x, ξ/√(2π))` the unit-scale phase-space
distance `phaseDistUnit` becomes `√π` times the Euclidean distance of `ℝ^d × ℝ^d`. -/
theorem phaseDistUnit_scaled (x ξ x' ξ' : RealVec d) :
    phaseDistUnit (sqrtTwoPi • x) (sqrtTwoPi⁻¹ • ξ) (sqrtTwoPi • x') (sqrtTwoPi⁻¹ • ξ')
      = Real.sqrt Real.pi * Real.sqrt (‖x - x'‖ ^ 2 + ‖ξ - ξ'‖ ^ 2) := by
  have h1 : ‖sqrtTwoPi • x - sqrtTwoPi • x'‖ ^ 2 = (2 * Real.pi) * ‖x - x'‖ ^ 2 := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos sqrtTwoPi_pos, mul_pow, sq_sqrtTwoPi]
  have h2 : ‖sqrtTwoPi⁻¹ • ξ - sqrtTwoPi⁻¹ • ξ'‖ ^ 2 = (2 * Real.pi)⁻¹ * ‖ξ - ξ'‖ ^ 2 := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr sqrtTwoPi_pos), mul_pow,
      inv_pow, sq_sqrtTwoPi]
  rw [phaseDistUnit, h1, h2, ← Real.sqrt_mul Real.pi_pos.le]
  congr 1
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp

end DiscretePR
