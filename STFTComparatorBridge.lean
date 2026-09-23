import STFT
import Showcase

/-!
# Proof bridge for the standalone STFT comparator

This file proves the `window_MemLp` and `STFTPhaseRetrieval` challenges from `Showcase.lean`.
It expands a complex polynomial--Gaussian window as a finite Hermite sum, identifies the
comparator's inner-product STFT with the integral STFT used by the development, and transports
the unit-scale sampling theorem through the required dilation of time-frequency space.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ComparatorBridge

variable {d : ℕ}

private def hermiteSpan (d : ℕ) : Submodule ℂ (DiscretePR.RealVec d → ℂ) :=
  Submodule.span ℂ (Set.range fun α : Fin d → ℕ =>
    (ModulusRecovery.realHermiteTensorRep α : DiscretePR.RealVec d → ℂ))

private lemma mem_hermiteSpan (α : Fin d → ℕ) :
    (ModulusRecovery.realHermiteTensorRep α : DiscretePR.RealVec d → ℂ) ∈ hermiteSpan d :=
  Submodule.subset_span ⟨α, rfl⟩

private lemma exists_finsupp_of_mem {f : DiscretePR.RealVec d → ℂ} (hf : f ∈ hermiteSpan d) :
    ∃ c : (Fin d → ℕ) →₀ ℂ, ∀ x,
      f x = ∑ α ∈ c.support, c α * ModulusRecovery.realHermiteTensorRep α x := by
  rw [hermiteSpan, Finsupp.mem_span_range_iff_exists_finsupp] at hf
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun x => ?_⟩
  rw [← hc]
  simp [Finsupp.sum, Finset.sum_apply]

private lemma monomial_mem_hermiteSpan (β : Fin d → ℕ) :
    (fun x : DiscretePR.RealVec d =>
      (∏ i, (x i : ℂ) ^ β i) *
        ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)) ∈ hermiteSpan d := by
  obtain ⟨c, hc⟩ := ModulusRecovery.monomialGaussian_tensor_mem_span β
  have hfun : (fun x : DiscretePR.RealVec d =>
      (∏ i, (x i : ℂ) ^ β i) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)) =
      ∑ α ∈ c.support, c α •
        (ModulusRecovery.realHermiteTensorRep α : DiscretePR.RealVec d → ℂ) := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc x
  rw [hfun]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (mem_hermiteSpan α)

private def unitWindowRep (h : MvPolynomial (Fin d) ℂ) : DiscretePR.RealVec d → ℂ :=
  fun x => h.eval (fun i => (x i : ℂ)) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)

private lemma unitWindowRep_mem_hermiteSpan (h : MvPolynomial (Fin d) ℂ) :
    unitWindowRep h ∈ hermiteSpan d := by
  classical
  have hpt : unitWindowRep h =
      ∑ β ∈ h.support, h.coeff β • (fun x : DiscretePR.RealVec d =>
        (∏ i, (x i : ℂ) ^ β i) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitWindowRep]
    rw [MvPolynomial.eval_eq', Finset.sum_mul]
    exact Finset.sum_congr rfl fun β _ => by ring
  rw [hpt]
  exact Submodule.sum_mem _ fun β _ =>
    Submodule.smul_mem _ _ (monomial_mem_hermiteSpan β)

private lemma unitWindowRep_eq_sum (h : MvPolynomial (Fin d) ℂ) :
    ∃ c : (Fin d → ℕ) →₀ ℂ, ∀ x,
      unitWindowRep h x =
        ∑ α ∈ c.support, c α * ModulusRecovery.realHermiteTensorRep α x :=
  exists_finsupp_of_mem (unitWindowRep_mem_hermiteSpan h)

private lemma unitWindowRep_memLp (h : MvPolynomial (Fin d) ℂ) :
    MemLp (unitWindowRep h) 2 (volume : Measure (DiscretePR.RealVec d)) := by
  obtain ⟨c, hc⟩ := unitWindowRep_eq_sum h
  have hfun : unitWindowRep h = fun x =>
      ∑ α ∈ c.support, c α * ModulusRecovery.realHermiteTensorRep α x := funext hc
  rw [hfun]
  refine memLp_finsetSum _ fun α _ => MemLp.const_mul ?_ _
  exact ModulusRecovery.realHermiteTensorRep_memLp_of_realHermite1D_memLp α
    ModulusRecovery.realHermite1D_memLp_inner_orthonormal.1

private lemma unitWindowRep_ne_zero {h : MvPolynomial (Fin d) ℂ} (hh : h ≠ 0) :
    unitWindowRep h ≠ 0 := by
  intro hzero
  apply hh
  let s : Fin d → Set ℂ := fun _ => Set.range (fun x : ℝ => (x : ℂ))
  apply MvPolynomial.funext_set s
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  choose x hx using fun i => hz i (Set.mem_univ i)
  let y : DiscretePR.RealVec d := WithLp.toLp 2 x
  have hval := congrFun hzero y
  rw [Pi.zero_apply, unitWindowRep] at hval
  have hexp : ((Real.exp (-‖y‖ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have heval : MvPolynomial.eval (fun i => (y i : ℂ)) h = 0 :=
    (mul_eq_zero.mp hval).resolve_right hexp
  have hy : (fun i => (y i : ℂ)) = z := by
    funext i
    change (x i : ℂ) = z i
    exact hx i
  rwa [← hy]

private lemma unitWindow_coefficients_ne_zero {h : MvPolynomial (Fin d) ℂ} (hh : h ≠ 0) :
    ∃ c : (Fin d → ℕ) →₀ ℂ, c ≠ 0 ∧
      (unitWindowRep_memLp h).toLp (unitWindowRep h) =
        ∑ α ∈ c.support, c α • ModulusRecovery.realHermiteTensorL2 α := by
  obtain ⟨c, hc⟩ := unitWindowRep_eq_sum h
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    apply unitWindowRep_ne_zero hh
    funext x
    rw [hc x, hc0]
    simp
  · apply Lp.ext
    have hae : ∀ α ∈ c.support, ∀ᵐ x ∂(volume : Measure (DiscretePR.RealVec d)),
        ((c α • ModulusRecovery.realHermiteTensorL2 α : DiscretePR.L2Real d) :
            DiscretePR.RealVec d → ℂ) x
          = c α * ModulusRecovery.realHermiteTensorRep α x := by
      intro α _
      filter_upwards [Lp.coeFn_smul (c α) (ModulusRecovery.realHermiteTensorL2 α),
        ModulusRecovery.varphiKappa_coe_ae_eq_realHermiteTensorRep α] with x h1 h2
      rw [h1]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact congrArg (fun y => c α * y) h2
    filter_upwards [(unitWindowRep_memLp h).coeFn_toLp,
      MeasureTheory.Lp.coeFn_fun_finsetSum c.support
        (fun α => c α • ModulusRecovery.realHermiteTensorL2 α),
      (Filter.eventually_all_finset c.support).mpr hae] with x hx hs hα
    rw [hx, hs, hc x]
    exact Finset.sum_congr rfl fun α hmem => by rw [hα α hmem]

private def rescalePoly (c : ℂ) (h : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C c * MvPolynomial.X i) h

private lemma eval_rescalePoly (c : ℂ) (h : MvPolynomial (Fin d) ℂ) (z : Fin d → ℂ) :
    MvPolynomial.eval z (rescalePoly c h) = MvPolynomial.eval (c • z) h := by
  have key := MvPolynomial.comp_aeval_apply
    (f := fun i : Fin d => MvPolynomial.C c * (MvPolynomial.X i : MvPolynomial (Fin d) ℂ))
    (MvPolynomial.aeval z) h
  have hfun : (fun i : Fin d =>
      (MvPolynomial.aeval z) (MvPolynomial.C c * (MvPolynomial.X i : MvPolynomial (Fin d) ℂ)))
      = c • z := by
    funext i
    simp
  rw [hfun] at key
  simpa [rescalePoly] using key

private lemma rescalePoly_ne_zero {c : ℂ} (hc : c ≠ 0)
    {h : MvPolynomial (Fin d) ℂ} (hh : h ≠ 0) :
    rescalePoly c h ≠ 0 := by
  intro hzero
  refine hh (MvPolynomial.funext fun z => ?_)
  have key := eval_rescalePoly c h (c⁻¹ • z)
  rw [hzero, smul_smul, mul_inv_cancel₀ hc, one_smul, map_zero] at key
  rw [map_zero]
  exact key.symm

private def sqrtTwo : ℝ := Real.sqrt 2

private lemma sqrtTwo_pos : 0 < sqrtTwo := Real.sqrt_pos.mpr (by norm_num)
private lemma sqrtTwo_ne_zero : sqrtTwo ≠ 0 := ne_of_gt sqrtTwo_pos
private lemma sq_sqrtTwo : sqrtTwo ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma unitWindowRep_smul (h : MvPolynomial (Fin d) ℂ)
    (x : DiscretePR.RealVec d) :
    unitWindowRep (rescalePoly ((sqrtTwo : ℂ)⁻¹) h) (sqrtTwo • x) =
      DiscretePR_Showcase.window h x := by
  have harg : ((sqrtTwo : ℂ)⁻¹ • fun i : Fin d => ((sqrtTwo • x) i : ℂ)) =
      fun i : Fin d => (x i : ℂ) := by
    funext i
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    field_simp [sqrtTwo_ne_zero]
  have hnorm : Real.exp (-‖sqrtTwo • x‖ ^ 2 / 2) = Real.exp (-‖x‖ ^ 2) := by
    congr 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos sqrtTwo_pos, mul_pow, sq_sqrtTwo]
    ring
  rw [unitWindowRep, eval_rescalePoly, harg, hnorm, DiscretePR_Showcase.window]
  ring

theorem window_MemLp_proved : type_of% @DiscretePR_Showcase.window_MemLp := by
  intro d h
  have hbase : MemLp (fun x : DiscretePR.RealVec d =>
      unitWindowRep (rescalePoly ((sqrtTwo : ℂ)⁻¹) h) (sqrtTwo • x)) 2 volume :=
    DiscretePR.memLp_comp_smul sqrtTwo_ne_zero
      (unitWindowRep_memLp (rescalePoly ((sqrtTwo : ℂ)⁻¹) h))
  have hfun : (fun x : DiscretePR.RealVec d =>
      unitWindowRep (rescalePoly ((sqrtTwo : ℂ)⁻¹) h) (sqrtTwo • x)) =
        DiscretePR_Showcase.window h := funext (unitWindowRep_smul h)
  rwa [hfun] at hbase

/-- The standalone comparator's `L²` window selects its integrable branch. -/
private lemma windowL2_eq_toLp (h : MvPolynomial (Fin d) ℂ) :
    DiscretePR_Showcase.windowL2 h =
      (window_MemLp_proved h).toLp (DiscretePR_Showcase.window h) := by
  rw [DiscretePR_Showcase.windowL2, dif_pos (window_MemLp_proved h)]

private lemma dilate_unitWindow_eq (h : MvPolynomial (Fin d) ℂ) :
    DiscretePR.dilate sqrtTwo
        ((unitWindowRep_memLp (rescalePoly ((sqrtTwo : ℂ)⁻¹) h)).toLp
          (unitWindowRep (rescalePoly ((sqrtTwo : ℂ)⁻¹) h))) =
      ((DiscretePR.dilateFactor sqrtTwo d : ℝ) : ℂ) •
        DiscretePR_Showcase.windowL2 h := by
  rw [windowL2_eq_toLp]
  apply Lp.ext
  filter_upwards [DiscretePR.dilate_coe sqrtTwo_ne_zero
      ((unitWindowRep_memLp (rescalePoly ((sqrtTwo : ℂ)⁻¹) h)).toLp
        (unitWindowRep (rescalePoly ((sqrtTwo : ℂ)⁻¹) h))),
    DiscretePR.ae_comp_smul sqrtTwo_ne_zero
      (unitWindowRep_memLp (rescalePoly ((sqrtTwo : ℂ)⁻¹) h)).coeFn_toLp,
    Lp.coeFn_smul ((DiscretePR.dilateFactor sqrtTwo d : ℝ) : ℂ)
      ((window_MemLp_proved h).toLp (DiscretePR_Showcase.window h)),
    (window_MemLp_proved h).coeFn_toLp] with x h1 h2 h3 h4
  rw [h1, h2, unitWindowRep_smul, h3, Pi.smul_apply, h4, smul_eq_mul]

private lemma stft_window_eq (h : MvPolynomial (Fin d) ℂ) (f : DiscretePR.L2Real d)
    (x ξ : DiscretePR.RealVec d) :
    DiscretePR.stft (DiscretePR_Showcase.windowL2 h) f x ξ =
      ((DiscretePR.dilateFactor sqrtTwo d : ℝ) : ℂ)⁻¹ *
        DiscretePR.stft
          ((unitWindowRep_memLp (rescalePoly ((sqrtTwo : ℂ)⁻¹) h)).toLp
            (unitWindowRep (rescalePoly ((sqrtTwo : ℂ)⁻¹) h)))
          (DiscretePR.dilate sqrtTwo⁻¹ f) (sqrtTwo • x) (sqrtTwo⁻¹ • ξ) := by
  have hfac : ((DiscretePR.dilateFactor sqrtTwo d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (DiscretePR.dilateFactor_pos sqrtTwo_pos)
  have hw : DiscretePR_Showcase.windowL2 h =
      (((DiscretePR.dilateFactor sqrtTwo d : ℝ) : ℂ)⁻¹) •
        DiscretePR.dilate sqrtTwo
          ((unitWindowRep_memLp (rescalePoly ((sqrtTwo : ℂ)⁻¹) h)).toLp
            (unitWindowRep (rescalePoly ((sqrtTwo : ℂ)⁻¹) h))) := by
    rw [dilate_unitWindow_eq, smul_smul, inv_mul_cancel₀ hfac, one_smul]
  have hf : f = DiscretePR.dilate sqrtTwo (DiscretePR.dilate sqrtTwo⁻¹ f) :=
    (DiscretePR.dilate_dilate_inv sqrtTwo_pos f).symm
  rw [hw]
  nth_rewrite 1 [hf]
  rw [DiscretePR.stft_window_smul, DiscretePR.stft_dilate sqrtTwo_pos]
  congr 1
  rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv]

private lemma timeFreqShift_memLp (x ξ : DiscretePR.RealVec d)
    (f : DiscretePR.L2Real d) :
    MemLp (fun t : DiscretePR.RealVec d =>
      Complex.exp ((2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ t : ℝ) : ℂ)) *
        (f : DiscretePR.RealVec d → ℂ) (t - x)) 2 volume := by
  have hshift : MemLp (fun t : DiscretePR.RealVec d =>
      (f : DiscretePR.RealVec d → ℂ) (t - x)) 2 volume := by
    simpa [Function.comp_def] using
      (Lp.memLp f).comp_measurePreserving (measurePreserving_sub_right volume x)
  apply MemLp.of_le_mul (c := 1) hshift
  · exact
      (by fun_prop : Continuous (fun t : DiscretePR.RealVec d =>
        Complex.exp ((2 * Real.pi : ℂ) * Complex.I *
          ((inner ℝ ξ t : ℝ) : ℂ)))).aestronglyMeasurable.mul hshift.aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul, Complex.norm_exp]
    simp

private lemma timeFreqShift_coe (x ξ : DiscretePR.RealVec d) (f : DiscretePR.L2Real d) :
    (DiscretePR_Showcase.timeFreqShift x ξ f : DiscretePR.RealVec d → ℂ) =ᵐ[volume]
      fun t => Complex.exp ((2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ t : ℝ) : ℂ)) *
        (f : DiscretePR.RealVec d → ℂ) (t - x) := by
  rw [DiscretePR_Showcase.timeFreqShift, dif_pos (timeFreqShift_memLp x ξ f)]
  exact MemLp.coeFn_toLp _

private lemma STFT_eq_stft (g f : DiscretePR.L2Real d)
    (z : EuclideanSpace ℂ (Fin d)) :
    DiscretePR_Showcase.STFT g f z = DiscretePR.stft g f z.re z.im := by
  unfold DiscretePR_Showcase.STFT DiscretePR.stft
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [timeFreqShift_coe z.re z.im g] with t ht
  rw [ht]
  simp only [RCLike.inner_apply, map_mul, ← Complex.exp_conj]
  simp
  simp only [map_ofNat]
  ring

private lemma norm_STFT_window_eq (h : MvPolynomial (Fin d) ℂ)
    (f : DiscretePR.L2Real d)
    (z : EuclideanSpace ℂ (Fin d)) :
    ‖DiscretePR_Showcase.STFT
        (DiscretePR_Showcase.windowL2 h) f z‖ =
      (DiscretePR.dilateFactor sqrtTwo d)⁻¹ *
        ‖DiscretePR.stft
          ((unitWindowRep_memLp (rescalePoly ((sqrtTwo : ℂ)⁻¹) h)).toLp
            (unitWindowRep (rescalePoly ((sqrtTwo : ℂ)⁻¹) h)))
          (DiscretePR.dilate sqrtTwo⁻¹ f) (sqrtTwo • z.re) (sqrtTwo⁻¹ • z.im)‖ := by
  rw [STFT_eq_stft, stft_window_eq, norm_mul, ← Complex.ofReal_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (DiscretePR.dilateFactor_pos sqrtTwo_pos))]

private lemma norm_re_im_sq (z w : EuclideanSpace ℂ (Fin d)) :
    ‖z.re - w.re‖ ^ 2 + ‖z.im - w.im‖ ^ 2 = dist z w ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.dist_eq, Real.sq_sqrt]
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      change ((z i).re - (w i).re) ^ 2 + ((z i).im - (w i).im) ^ 2 =
        dist (z i) (w i) ^ 2
      rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im]
      ring
  · exact Finset.sum_nonneg fun i _ => sq_nonneg (dist (z i) (w i))

private lemma phaseDist_scaled_le_four_dist (z w : EuclideanSpace ℂ (Fin d)) :
    DiscretePR.phaseDistUnit (sqrtTwo • z.re) (sqrtTwo⁻¹ • z.im)
        (sqrtTwo • w.re) (sqrtTwo⁻¹ • w.im) ≤ 4 * dist z w := by
  have hreal : sqrtTwo • z.re - sqrtTwo • w.re = sqrtTwo • (z.re - w.re) := by
    module
  have himag : sqrtTwo⁻¹ • z.im - sqrtTwo⁻¹ • w.im =
      sqrtTwo⁻¹ • (z.im - w.im) := by
    module
  have hrad :
      (‖sqrtTwo • z.re - sqrtTwo • w.re‖ ^ 2 +
          (2 * Real.pi) ^ 2 * ‖sqrtTwo⁻¹ • z.im - sqrtTwo⁻¹ • w.im‖ ^ 2) / 2 =
        ‖z.re - w.re‖ ^ 2 + Real.pi ^ 2 * ‖z.im - w.im‖ ^ 2 := by
    rw [hreal, himag, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos sqrtTwo_pos, abs_of_pos (inv_pos.mpr sqrtTwo_pos), mul_pow, mul_pow,
      sq_sqrtTwo]
    field_simp [sqrtTwo_ne_zero]
    rw [sq_sqrtTwo]
    ring
  rw [DiscretePR.phaseDistUnit, hrad]
  have hR : 0 ≤ ‖z.re - w.re‖ ^ 2 := sq_nonneg _
  have hI : 0 ≤ ‖z.im - w.im‖ ^ 2 := sq_nonneg _
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
  have hsq : ‖z.re - w.re‖ ^ 2 + Real.pi ^ 2 * ‖z.im - w.im‖ ^ 2
      ≤ (4 * dist z w) ^ 2 := by
    rw [show (4 * dist z w) ^ 2 = 16 * dist z w ^ 2 by ring, ← norm_re_im_sq]
    nlinarith
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩

private def phaseMap (z : EuclideanSpace ℂ (Fin d)) :
    DiscretePR.RealVec d × DiscretePR.RealVec d :=
  (sqrtTwo • z.re, sqrtTwo⁻¹ • z.im)

private def phaseMapInv (p : DiscretePR.RealVec d × DiscretePR.RealVec d) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i =>
    ((sqrtTwo⁻¹ * p.1 i : ℝ) : ℂ) + Complex.I * ((sqrtTwo * p.2 i : ℝ) : ℂ)

private lemma phaseMap_phaseMapInv (p : DiscretePR.RealVec d × DiscretePR.RealVec d) :
    phaseMap (phaseMapInv p) = p := by
  rcases p with ⟨x, ξ⟩
  rw [phaseMap, Prod.mk.injEq]
  constructor <;> apply WithLp.ofLp_injective 2 <;> funext i
  · simp only [phaseMapInv, EuclideanSpace.re, PiLp.smul_apply]
    simp [Complex.mul_re, sqrtTwo_ne_zero]
  · simp only [phaseMapInv, EuclideanSpace.im, PiLp.smul_apply]
    simp [Complex.mul_im, sqrtTwo_ne_zero]

private lemma phaseMap_injective : Function.Injective (phaseMap (d := d)) := by
  intro z w hzw
  rw [phaseMap, Prod.mk.injEq] at hzw
  have hre : z.re = w.re := smul_right_injective _ sqrtTwo_ne_zero hzw.1
  have him : z.im = w.im :=
    smul_right_injective _ (inv_ne_zero sqrtTwo_ne_zero) hzw.2
  apply WithLp.ofLp_injective 2
  funext i
  apply Complex.ext
  · exact congrFun (congrArg WithLp.ofLp hre) i
  · exact congrFun (congrArg WithLp.ofLp him) i

theorem stft_comparator_proved : type_of% @DiscretePR_Showcase.STFTPhaseRetrieval := by
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
      let q : MvPolynomial (Fin (d + 1)) ℂ :=
        rescalePoly ((sqrtTwo : ℂ)⁻¹) h
      have hq : q ≠ 0 :=
        rescalePoly_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr sqrtTwo_ne_zero)) hnonzero
      let u : DiscretePR.L2Real (d + 1) :=
        (unitWindowRep_memLp q).toLp (unitWindowRep q)
      obtain ⟨c, hc, hcu⟩ := unitWindow_coefficients_ne_zero hq
      obtain ⟨S₀, hsep, hphase⟩ :=
        DiscretePR.STFTDiscretePhaseRetrieval_unit_of_finite_window
          (d + 1) (by omega) u c hc (by simpa [u] using hcu)
      let S : Set (EuclideanSpace ℂ (Fin (d + 1))) := {z | phaseMap z ∈ S₀}
      refine ⟨S, ?_, ?_⟩
      · intro z hz w hw hzw
        have hbound := hsep (phaseMap z).1 (phaseMap z).2 hz
          (phaseMap w).1 (phaseMap w).2 hw (fun heq => hzw (phaseMap_injective heq))
        have hmetric := phaseDist_scaled_le_four_dist z w
        simp only [phaseMap] at hbound
        linarith
      · intro F hF G hG hsample
        obtain ⟨f, rfl⟩ := hF
        obtain ⟨g, rfl⟩ := hG
        obtain ⟨θ, hθ, hfg⟩ := hphase
          (DiscretePR.dilate sqrtTwo⁻¹ f) (DiscretePR.dilate sqrtTwo⁻¹ g) (by
            intro x ξ hxξ
            let z := phaseMapInv (x, ξ)
            have hz : z ∈ S := by
              change phaseMap (phaseMapInv (x, ξ)) ∈ S₀
              rw [phaseMap_phaseMapInv]
              exact hxξ
            have hs := hsample z hz
            rw [norm_STFT_window_eq, norm_STFT_window_eq] at hs
            change (DiscretePR.dilateFactor sqrtTwo (d + 1))⁻¹ *
                ‖DiscretePR.stft u (DiscretePR.dilate sqrtTwo⁻¹ f)
                  (phaseMap (phaseMapInv (x, ξ))).1
                  (phaseMap (phaseMapInv (x, ξ))).2‖ =
              (DiscretePR.dilateFactor sqrtTwo (d + 1))⁻¹ *
                ‖DiscretePR.stft u (DiscretePR.dilate sqrtTwo⁻¹ g)
                  (phaseMap (phaseMapInv (x, ξ))).1
                  (phaseMap (phaseMapInv (x, ξ))).2‖ at hs
            rw [phaseMap_phaseMapInv] at hs
            exact mul_left_cancel₀
              (ne_of_gt (inv_pos.mpr (DiscretePR.dilateFactor_pos sqrtTwo_pos))) hs)
        have hsigeq : f = θ • g := by
          calc
            f = DiscretePR.dilate sqrtTwo (DiscretePR.dilate sqrtTwo⁻¹ f) :=
              (DiscretePR.dilate_dilate_inv sqrtTwo_pos f).symm
            _ = DiscretePR.dilate sqrtTwo (θ • DiscretePR.dilate sqrtTwo⁻¹ g) := by rw [hfg]
            _ = θ • DiscretePR.dilate sqrtTwo (DiscretePR.dilate sqrtTwo⁻¹ g) :=
              DiscretePR.dilate_smul sqrtTwo_ne_zero θ _
            _ = θ • g := by rw [DiscretePR.dilate_dilate_inv sqrtTwo_pos g]
        refine ⟨θ, ?_⟩
        funext z
        rw [hsigeq]
        simp only [DiscretePR_Showcase.STFT, Pi.smul_apply, smul_eq_mul]
        rw [inner_smul_right]

end ComparatorBridge
