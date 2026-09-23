import ContinuousPhaseRetrieval.ModulusRecovery.ExactModulusRecovery

/-!
# The Hermite functions are an orthonormal basis of `L²(ℝ^d)`

`ExactModulusRecovery.lean` provides the orthonormal family `realHermiteTensorL2 : Idx d → L2Real d`
and the expansion map `hermiteExpansion : Coeffs d → L2Real d`, together with its injectivity.
Here we prove that the family is *complete*: its span is dense, it is a `HilbertBasis`, and
`hermiteExpansion` is surjective, with the explicit inverse `hermiteCoeffs`.

The proof uses the generating function `realHermiteGenerating t u = π^{-1/4} e^{-t²/2+√2tu-u²/2}`,
whose Taylor series in `u` is `∑ₙ ψₙ(t) uⁿ/√n!` by the very definition of `realHermite1D`.
Tensorising over the `d` coordinates and interchanging sum and integral, the pairing of
`f ∈ L²(ℝ^d)` with the tensor generating function is a power series whose coefficients are the
Hermite coefficients of `f`.  Evaluating at `u = iξ/√2` turns the tensor generating function into
a Gaussian times `e^{i⟨t,ξ⟩}`, so if all Hermite coefficients of `f` vanish, then the Fourier
transform of `conj(f) · e^{-‖t‖²/2}` vanishes identically; by Fourier injectivity on `L¹ ∩ L²`
(`fourier_l1_l2_eq_zero_ae`) and nonvanishing of the Gaussian, `f = 0`.
-/

noncomputable section

namespace ModulusRecovery

open MeasureTheory FourierTransform Filter
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate Nat Topology

/-! ## The Taylor expansion of the generating function -/

/-- `u ↦ realHermiteGenerating t u` is entire. -/
theorem realHermiteGenerating_differentiable (t : ℝ) :
    Differentiable ℂ (realHermiteGenerating t) := by
  unfold realHermiteGenerating
  fun_prop

/-- The Taylor series of the generating function in `u` is `∑ₙ uⁿ/√n! · ψₙ(t)`; this is just the
definition of `realHermite1D` read backwards. -/
theorem hasSum_realHermiteGenerating (t : ℝ) (u : ℂ) :
    HasSum (fun n : ℕ => u ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t)
      (realHermiteGenerating t u) := by
  have h := Complex.hasSum_taylorSeries_of_entire
    (realHermiteGenerating_differentiable t) 0 u
  have hfun :
      (fun n : ℕ =>
          (n ! : ℂ)⁻¹ • (u - 0) ^ n • iteratedDeriv n (realHermiteGenerating t) 0) =
        fun n : ℕ => u ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t := by
    funext n
    have hfac : ((Nat.factorial n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) : ((Nat.factorial n : ℝ)) ≠ 0)
    have hsqrt : ((Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ) ≠ 0 := by
      have hpos : Real.sqrt (Nat.factorial n : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
        positivity
      exact_mod_cast hpos
    simp only [realHermite1D, sub_zero, smul_eq_mul]
    field_simp
  rwa [hfun] at h

/-- `realHermiteGenerating t u = ∑' n, uⁿ/√n! · ψₙ(t)`. -/
theorem realHermiteGenerating_eq_tsum (t : ℝ) (u : ℂ) :
    realHermiteGenerating t u =
      ∑' n : ℕ, u ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t :=
  (hasSum_realHermiteGenerating t u).tsum_eq.symm

/-! ## Summability of `rⁿ/√n!` -/

/-- `∑ₙ rⁿ/√n!` converges for every `r ≥ 0`: indeed `rⁿ/√n! = √((4r²)ⁿ/n! · 4⁻ⁿ)` is bounded by
the arithmetic mean of two summable sequences. -/
theorem summable_pow_div_sqrt_factorial {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun n : ℕ => r ^ n / Real.sqrt (Nat.factorial n : ℝ)) := by
  have hA : Summable (fun n : ℕ => (4 * r ^ 2) ^ n / (Nat.factorial n : ℝ)) :=
    Real.summable_pow_div_factorial _
  have hB : Summable (fun n : ℕ => ((4 : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hA.add hB).div_const 2)
  set a : ℝ := (4 * r ^ 2) ^ n / (Nat.factorial n : ℝ) with ha
  set b : ℝ := ((4 : ℝ)⁻¹) ^ n with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hab : a * b = (r ^ n) ^ 2 / (Nat.factorial n : ℝ) := by
    rw [ha, hb, div_mul_eq_mul_div, ← mul_pow, show 4 * r ^ 2 * (4 : ℝ)⁻¹ = r ^ 2 by ring]
    ring
  have hkey : r ^ n / Real.sqrt (Nat.factorial n : ℝ) = Real.sqrt (a * b) := by
    rw [hab, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  rw [hkey]
  have hle : Real.sqrt (a * b) ≤ Real.sqrt (((a + b) / 2) ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])
  rwa [Real.sqrt_sq (by positivity)] at hle

/-- The complex-norm version of `summable_pow_div_sqrt_factorial`. -/
theorem summable_norm_pow_div_sqrt_factorial (u : ℂ) :
    Summable (fun n : ℕ => ‖u ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)‖) := by
  have h := summable_pow_div_sqrt_factorial (r := ‖u‖) (norm_nonneg u)
  refine h.congr fun n => ?_
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-! ## Products of series over the multi-indices `Fin d → ℕ` -/

/-- A product of nonnegative summable series over `Fin d → ℕ` is summable. -/
theorem summable_pi_prod {d : ℕ} {g : Fin d → ℕ → ℝ} (hg0 : ∀ i n, 0 ≤ g i n)
    (hgs : ∀ i, Summable (g i)) :
    Summable (fun α : Fin d → ℕ => ∏ i, g i (α i)) := by
  have hnn : ∀ α : Fin d → ℕ, 0 ≤ ∏ i, g i (α i) :=
    fun α => Finset.prod_nonneg fun i _ => hg0 i (α i)
  refine summable_of_sum_le (c := ∏ i, ∑' n, g i n) hnn (fun S => ?_)
  set M : ℕ := (S.sup fun α => ∑ i, α i) + 1 with hM
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin d => Finset.range M) := by
    intro α hα
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have h1 : α i ≤ ∑ j, α j :=
      Finset.single_le_sum (f := fun j => α j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (∑ j, α j) ≤ S.sup fun α => ∑ i, α i := Finset.le_sup hα
    omega
  calc ∑ α ∈ S, ∏ i, g i (α i)
      ≤ ∑ α ∈ Fintype.piFinset (fun _ : Fin d => Finset.range M), ∏ i, g i (α i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun α _ _ => hnn α)
    _ = ∏ i, ∑ n ∈ Finset.range M, g i n := Finset.sum_prod_piFinset _ _
    _ ≤ ∏ i, ∑' n, g i n := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun n _ => hg0 i n)
          (fun i _ => (hgs i).sum_le_tsum _ (fun n _ => hg0 i n))

/-- The boxes `{0,…,M-1}^d` are cofinal among the finite subsets of `Fin d → ℕ`. -/
theorem tendsto_piFinset_range_atTop (d : ℕ) :
    Tendsto (fun M : ℕ => Fintype.piFinset (fun _ : Fin d => Finset.range M)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun S => ?_
  refine ⟨(S.sup fun α => ∑ i, α i) + 1, fun M hM => ?_⟩
  intro α hα
  simp only [Fintype.mem_piFinset, Finset.mem_range]
  intro i
  have h1 : α i ≤ ∑ j, α j :=
    Finset.single_le_sum (f := fun j => α j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : (∑ j, α j) ≤ S.sup fun α => ∑ i, α i := Finset.le_sup hα
  omega

/-- A product of `d` absolutely convergent complex series, as a single series over `Fin d → ℕ`. -/
theorem summable_and_tsum_pi_prod {d : ℕ} {g : Fin d → ℕ → ℂ}
    (hgs : ∀ i, Summable (fun n => ‖g i n‖)) :
    Summable (fun α : Fin d → ℕ => ∏ i, g i (α i)) ∧
      ∑' α : Fin d → ℕ, ∏ i, g i (α i) = ∏ i, ∑' n, g i n := by
  have hnorm : Summable (fun α : Fin d → ℕ => ∏ i, ‖g i (α i)‖) :=
    summable_pi_prod (g := fun i n => ‖g i n‖) (fun i n => norm_nonneg _) hgs
  have hsum : Summable (fun α : Fin d → ℕ => ∏ i, g i (α i)) := by
    refine Summable.of_norm (hnorm.congr fun α => ?_)
    rw [norm_prod]
  refine ⟨hsum, ?_⟩
  have h1 : Tendsto
      (fun M : ℕ => ∑ α ∈ Fintype.piFinset (fun _ : Fin d => Finset.range M), ∏ i, g i (α i))
      atTop (𝓝 (∑' α : Fin d → ℕ, ∏ i, g i (α i))) :=
    hsum.hasSum.comp (tendsto_piFinset_range_atTop d)
  have h2 : Tendsto (fun M : ℕ => ∏ i, ∑ n ∈ Finset.range M, g i n) atTop
      (𝓝 (∏ i, ∑' n, g i n)) :=
    tendsto_finsetProd _ fun i _ => ((hgs i).of_norm).hasSum.tendsto_sum_nat
  refine tendsto_nhds_unique ?_ h2
  refine h1.congr fun M => ?_
  exact Finset.sum_prod_piFinset _ _

/-! ## The tensor generating function -/

/-- The `d`-dimensional generating function `∏ᵢ G(tᵢ, uᵢ)`. -/
def tensorGenerating {d : ℕ} (t : RealVec d) (u : Fin d → ℂ) : ℂ :=
  ∏ i, realHermiteGenerating (t i) (u i)

/-- The Taylor coefficient `u^α/√α!` of the tensor generating function. -/
def tensorCoeff {d : ℕ} (u : Fin d → ℂ) (α : Idx d) : ℂ :=
  ∏ i, u i ^ α i / (Real.sqrt (Nat.factorial (α i) : ℝ) : ℂ)

/-- The Taylor series of the one-dimensional generating function converges absolutely: this is the
usual "a power series converging everywhere converges absolutely", obtained by comparing the value
at `u` with the value at `2u`. -/
theorem summable_norm_realHermiteGenerating_term (t : ℝ) (u : ℂ) :
    Summable
      (fun n : ℕ => ‖u ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t‖) := by
  have hg : Summable
      (fun n : ℕ =>
        (2 * u) ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t) :=
    (hasSum_realHermiteGenerating t (2 * u)).summable
  obtain ⟨C, hC⟩ := hg.tendsto_atTop_zero.norm.bddAbove_range
  have hCn : ∀ n : ℕ,
      ‖(2 * u) ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t‖ ≤ C :=
    fun n => hC (Set.mem_range_self n)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : ((2 : ℝ)⁻¹) < 1)).mul_left C)
  have hsplit :
      (2 * u) ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t =
        (2 : ℂ) ^ n * (u ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t) := by
    rw [mul_pow]; ring
  have hnorm := hCn n
  rw [hsplit, norm_mul, norm_pow] at hnorm
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [h2] at hnorm
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖u ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t‖ * 2 ^ n
      = 2 ^ n * ‖u ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n t‖ := by ring
    _ ≤ C := hnorm

/-- The multi-dimensional coefficients are absolutely summable. -/
theorem summable_norm_tensorCoeff {d : ℕ} (u : Fin d → ℂ) :
    Summable (fun α : Idx d => ‖tensorCoeff u α‖) := by
  have h : Summable
      (fun α : Idx d => ∏ i, ‖u i ^ α i / (Real.sqrt (Nat.factorial (α i) : ℝ) : ℂ)‖) :=
    summable_pi_prod (g := fun i n => ‖u i ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ)‖)
      (fun i n => norm_nonneg _) (fun i => summable_norm_pow_div_sqrt_factorial (u i))
  refine h.congr fun α => ?_
  rw [tensorCoeff, norm_prod]

/-- Tensorised Taylor expansion of the generating function. -/
theorem tensorGenerating_eq_tsum {d : ℕ} (t : RealVec d) (u : Fin d → ℂ) :
    tensorGenerating t u = ∑' α : Idx d, tensorCoeff u α * realHermiteTensorRep α t := by
  have hkey := summable_and_tsum_pi_prod
    (g := fun (i : Fin d) (n : ℕ) =>
      u i ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n (t i))
    (fun i => summable_norm_realHermiteGenerating_term (t i) (u i))
  have hterm : ∀ α : Idx d,
      (∏ i, u i ^ α i / (Real.sqrt (Nat.factorial (α i) : ℝ) : ℂ) * realHermite1D (α i) (t i)) =
        tensorCoeff u α * realHermiteTensorRep α t := by
    intro α
    rw [tensorCoeff, realHermiteTensorRep, ← Finset.prod_mul_distrib]
  calc tensorGenerating t u
      = ∏ i, ∑' n : ℕ,
          u i ^ n / (Real.sqrt (Nat.factorial n : ℝ) : ℂ) * realHermite1D n (t i) :=
        Finset.prod_congr rfl fun i _ => realHermiteGenerating_eq_tsum (t i) (u i)
    _ = ∑' α : Idx d,
          ∏ i, u i ^ α i / (Real.sqrt (Nat.factorial (α i) : ℝ) : ℂ) *
            realHermite1D (α i) (t i) := hkey.2.symm
    _ = ∑' α : Idx d, tensorCoeff u α * realHermiteTensorRep α t := tsum_congr hterm

/-! ## Pairing a square-integrable function with the generating function -/

/-- The Hermite tensor representatives are square-integrable. -/
theorem realHermiteTensorRep_memLp {d : ℕ} (α : Idx d) :
    MemLp (realHermiteTensorRep α) 2 (volume : Measure (RealVec d)) :=
  realHermiteTensorRep_memLp_of_realHermite1D_memLp α realHermite1D_memLp_inner_orthonormal.1

/-- Each Hermite tensor function has `L²`-norm one. -/
theorem integral_norm_sq_realHermiteTensorRep {d : ℕ} (α : Idx d) :
    (∫ t : RealVec d, ‖realHermiteTensorRep α t‖ ^ 2) = 1 := by
  have h := realHermiteTensorL2_inner_eq_integral_of_memLp α α
    (realHermiteTensorRep_memLp α) (realHermiteTensorRep_memLp α)
  have hone : (inner ℂ (realHermiteTensorL2 α) (realHermiteTensorL2 α) : ℂ) = 1 := by
    simpa using (orthonormal_iff_ite.mp (realHermiteTensorL2_orthonormal (d := d))) α α
  rw [hone] at h
  have h3 : (∫ t : RealVec d, ((‖realHermiteTensorRep α t‖ ^ 2 : ℝ) : ℂ)) =
      ∫ t : RealVec d, realHermiteTensorRep α t * star (realHermiteTensorRep α t) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    change ((‖realHermiteTensorRep α t‖ ^ 2 : ℝ) : ℂ) =
      realHermiteTensorRep α t * star (realHermiteTensorRep α t)
    rw [show star (realHermiteTensorRep α t) = (starRingEnd ℂ) (realHermiteTensorRep α t) from rfl,
      Complex.mul_conj']
    push_cast
    ring
  have h4 : (∫ t : RealVec d, ((‖realHermiteTensorRep α t‖ ^ 2 : ℝ) : ℂ)) = 1 := h3.trans h.symm
  rw [integral_complex_ofReal] at h4
  exact_mod_cast h4

/-- A uniform bound (crude Cauchy–Schwarz) for the `L¹`-norms of `conj f · ψ_α`. -/
theorem integral_norm_conj_mul_realHermiteTensorRep_le {d : ℕ} (f : L2Real d) (α : Idx d) :
    (∫ t : RealVec d, ‖star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t‖) ≤
      ((∫ t : RealVec d, ‖(f : RealVec d → ℂ) t‖ ^ 2) + 1) / 2 := by
  have hf2 : MemLp (f : RealVec d → ℂ) 2 (volume : Measure (RealVec d)) := Lp.memLp f
  have hfsq : Integrable (fun t : RealVec d => ‖(f : RealVec d → ℂ) t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hf2.1).mp hf2
  have hψ := realHermiteTensorRep_memLp (d := d) α
  have hψsq : Integrable (fun t : RealVec d => ‖realHermiteTensorRep α t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hψ.1).mp hψ
  have hprod : Integrable
      (fun t : RealVec d => star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t) :=
    MemLp.integrable_mul (p := 2) (q := 2) hf2.star hψ
  have hmono : (∫ t : RealVec d, ‖star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t‖) ≤
      ∫ t : RealVec d,
        ((‖(f : RealVec d → ℂ) t‖ ^ 2 + ‖realHermiteTensorRep α t‖ ^ 2) / 2) := by
    refine integral_mono hprod.norm ((hfsq.add hψsq).div_const 2) fun t => ?_
    rw [norm_mul, norm_star]
    nlinarith [two_mul_le_add_sq ‖(f : RealVec d → ℂ) t‖ ‖realHermiteTensorRep α t‖]
  rwa [integral_div, integral_add hfsq hψsq, integral_norm_sq_realHermiteTensorRep] at hmono

/-- Integrability of `conj f · ψ_α`. -/
theorem integrable_conj_mul_realHermiteTensorRep {d : ℕ} (f : L2Real d) (α : Idx d) :
    Integrable (fun t : RealVec d => star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t) :=
  MemLp.integrable_mul (p := 2) (q := 2) (Lp.memLp f).star (realHermiteTensorRep_memLp α)

/-- Interchanging sum and integral: the pairing of `f` with the tensor generating function is the
power series in `u` whose coefficients are the Hermite coefficients of `f`. -/
theorem integral_conj_mul_tensorGenerating {d : ℕ} (f : L2Real d) (u : Fin d → ℂ) :
    (∫ t : RealVec d, star ((f : RealVec d → ℂ) t) * tensorGenerating t u) =
      ∑' α : Idx d, tensorCoeff u α *
        ∫ t : RealVec d, star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t := by
  set F : Idx d → RealVec d → ℂ := fun α t =>
    tensorCoeff u α * (star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t) with hF
  have hint : ∀ α : Idx d, Integrable (F α) :=
    fun α => (integrable_conj_mul_realHermiteTensorRep f α).const_mul _
  have hnormint : ∀ α : Idx d, (∫ t : RealVec d, ‖F α t‖) =
      ‖tensorCoeff u α‖ *
        ∫ t : RealVec d, ‖star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t‖ := by
    intro α
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    change ‖tensorCoeff u α * (star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t)‖ = _
    rw [norm_mul]
  have hsummable : Summable (fun α : Idx d => ∫ t : RealVec d, ‖F α t‖) := by
    refine Summable.of_nonneg_of_le (fun α => integral_nonneg fun t => norm_nonneg _)
      (fun α => ?_)
      ((summable_norm_tensorCoeff u).mul_right
        (((∫ t : RealVec d, ‖(f : RealVec d → ℂ) t‖ ^ 2) + 1) / 2))
    rw [hnormint α]
    exact mul_le_mul_of_nonneg_left (integral_norm_conj_mul_realHermiteTensorRep_le f α)
      (norm_nonneg _)
  have hpt : ∀ t : RealVec d,
      (∑' α : Idx d, F α t) = star ((f : RealVec d → ℂ) t) * tensorGenerating t u := by
    intro t
    have hswap : ∀ α : Idx d,
        F α t = star ((f : RealVec d → ℂ) t) * (tensorCoeff u α * realHermiteTensorRep α t) := by
      intro α; rw [hF]; ring
    rw [tsum_congr hswap, tsum_mul_left, ← tensorGenerating_eq_tsum]
  calc (∫ t : RealVec d, star ((f : RealVec d → ℂ) t) * tensorGenerating t u)
      = ∫ t : RealVec d, ∑' α : Idx d, F α t :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => (hpt t).symm)
    _ = ∑' α : Idx d, ∫ t : RealVec d, F α t :=
        (integral_tsum_of_summable_integral_norm hint hsummable).symm
    _ = ∑' α : Idx d, tensorCoeff u α *
          ∫ t : RealVec d, star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t :=
        tsum_congr fun α => integral_const_mul _ _

/-! ## Evaluation at purely imaginary arguments -/

/-- `‖t‖²` in coordinates. -/
theorem norm_sq_eq_sum {d : ℕ} (t : RealVec d) : ‖t‖ ^ 2 = ∑ i, t i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

/-- The real inner product in coordinates. -/
theorem inner_eq_sum {d : ℕ} (t ξ : RealVec d) : (inner ℝ t ξ : ℝ) = ∑ i, t i * ξ i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- At `u = iξ/√2` the tensor generating function is a Gaussian times a character, up to a nonzero
constant depending on `ξ` only. -/
theorem tensorGenerating_imaginary {d : ℕ} (t ξ : RealVec d) :
    tensorGenerating t (fun i => Complex.I * (ξ i : ℂ) / (Real.sqrt 2 : ℂ)) =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ d * Complex.exp (((‖ξ‖ ^ 2 / 4 : ℝ) : ℂ))) *
        (((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((inner ℝ t ξ : ℝ) : ℂ))) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hexp : ∀ i : Fin d,
      realHermiteGenerating (t i) (Complex.I * (ξ i : ℂ) / (Real.sqrt 2 : ℂ)) =
        ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-((t i : ℂ) ^ 2) / 2 + (ξ i : ℂ) ^ 2 / 4 +
            Complex.I * (t i : ℂ) * (ξ i : ℂ)) := by
    intro i
    rw [realHermiteGenerating]
    congr 2
    have key : (Complex.I * (ξ i : ℂ) / (Real.sqrt 2 : ℂ)) ^ 2 = -((ξ i : ℂ) ^ 2 / 2) := by
      rw [div_pow, mul_pow, Complex.I_sq, hs2]; ring
    have key2 : (Real.sqrt 2 : ℂ) * (t i : ℂ) * (Complex.I * (ξ i : ℂ) / (Real.sqrt 2 : ℂ)) =
        Complex.I * (t i : ℂ) * (ξ i : ℂ) := by
      have hsplit : (Real.sqrt 2 : ℂ) * (t i : ℂ) * (Complex.I * (ξ i : ℂ) / (Real.sqrt 2 : ℂ)) =
          ((Real.sqrt 2 : ℂ) / (Real.sqrt 2 : ℂ)) * (Complex.I * (t i : ℂ) * (ξ i : ℂ)) := by
        ring
      rw [hsplit, div_self hs, one_mul]
    rw [key, key2]; ring
  have hnt : ∑ i, ((t i : ℂ)) ^ 2 = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_sq_eq_sum]
    push_cast
    rfl
  have hnξ : ∑ i, ((ξ i : ℂ)) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_sq_eq_sum]
    push_cast
    rfl
  have hti : ∑ i, (t i : ℂ) * (ξ i : ℂ) = ((inner ℝ t ξ : ℝ) : ℂ) := by
    rw [inner_eq_sum]
    push_cast
    rfl
  have e1 : (∑ i, -((t i : ℂ) ^ 2) / 2) = -(∑ i, ((t i : ℂ)) ^ 2) / 2 := by
    rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
  have e2 : (∑ i, (ξ i : ℂ) ^ 2 / 4) = (∑ i, ((ξ i : ℂ)) ^ 2) / 4 := by
    rw [← Finset.sum_div]
  have e3 : (∑ i, Complex.I * (t i : ℂ) * (ξ i : ℂ)) =
      Complex.I * ∑ i, (t i : ℂ) * (ξ i : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : (∑ i, (-((t i : ℂ) ^ 2) / 2 + (ξ i : ℂ) ^ 2 / 4 +
      Complex.I * (t i : ℂ) * (ξ i : ℂ))) =
      ((‖ξ‖ ^ 2 / 4 : ℝ) : ℂ) + ((-(‖t‖ ^ 2) / 2 : ℝ) : ℂ) +
        Complex.I * ((inner ℝ t ξ : ℝ) : ℂ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3, hnt, hnξ, hti]
    push_cast
    ring
  rw [tensorGenerating, Finset.prod_congr rfl (fun i _ => hexp i), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Complex.exp_sum, hsum,
    Complex.ofReal_exp, Complex.exp_add, Complex.exp_add]
  ring

/-! ## Completeness of the Hermite family -/

/-- The Gaussian `e^{-‖t‖²}` is integrable on `ℝ^d`. -/
theorem integrable_exp_neg_sq_norm (d : ℕ) :
    Integrable (fun t : RealVec d => Real.exp (-(‖t‖ ^ 2))) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := RealVec d)
    (b := 1) (by norm_num) 0 0
  refine h.norm.congr ?_
  filter_upwards with t
  rw [Complex.norm_exp]
  simp [← Complex.ofReal_pow]

/-- The Gaussian `e^{-‖t‖²/2}` is square-integrable on `ℝ^d`. -/
theorem memLp_gaussian (d : ℕ) :
    MemLp (fun t : RealVec d => ((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ)) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun t : RealVec d => ((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ)) volume := by
    fun_prop
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  refine (integrable_exp_neg_sq_norm d).congr ?_
  filter_upwards with t
  have hsplit : Real.exp (-(‖t‖ ^ 2)) =
      Real.exp (-(‖t‖ ^ 2) / 2) * Real.exp (-(‖t‖ ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), hsplit]
  ring

/-- The `L²`-coercion of `realHermiteTensorL2 α` is a.e. `realHermiteTensorRep α`. -/
theorem realHermiteTensorL2_coe_ae {d : ℕ} (α : Idx d) :
    ((realHermiteTensorL2 α : L2Real d) : RealVec d → ℂ)
      =ᵐ[(volume : Measure (RealVec d))] realHermiteTensorRep α := by
  simpa [realHermiteTensorL2] using varphiKappa_coe_ae_eq_realHermiteTensorRep (d := d) α

/-- The Hermite pairing as an integral. -/
theorem inner_realHermiteTensorL2_eq_integral {d : ℕ} (f : L2Real d) (α : Idx d) :
    inner ℂ f (realHermiteTensorL2 α) =
      ∫ t : RealVec d, star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [realHermiteTensorL2_coe_ae (d := d) α] with t ht
  rw [RCLike.inner_apply, ht]
  exact mul_comm _ _

/-- A square-integrable function orthogonal to every Hermite function vanishes. -/
theorem eq_zero_of_inner_realHermiteTensorL2_eq_zero {d : ℕ} (f : L2Real d)
    (hf : ∀ α : Idx d, inner ℂ (realHermiteTensorL2 α) f = 0) : f = 0 := by
  have hcoeff : ∀ α : Idx d,
      (∫ t : RealVec d, star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t) = 0 := by
    intro α
    rw [← inner_realHermiteTensorL2_eq_integral f α]
    exact inner_eq_zero_symm.mpr (hf α)
  have hgen : ∀ u : Fin d → ℂ,
      (∫ t : RealVec d, star ((f : RealVec d → ℂ) t) * tensorGenerating t u) = 0 := by
    intro u
    rw [integral_conj_mul_tensorGenerating f u]
    have hz : ∀ α : Idx d, tensorCoeff u α *
        (∫ t : RealVec d, star ((f : RealVec d → ℂ) t) * realHermiteTensorRep α t) = 0 :=
      fun α => by rw [hcoeff α, mul_zero]
    rw [tsum_congr hz, tsum_zero]
  have hfourier : ∀ w : RealVec d,
      𝓕 (fun t : RealVec d =>
        star ((f : RealVec d → ℂ) t) * ((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ)) w = 0 := by
    intro w
    set ξ : RealVec d := (-(2 * Real.pi)) • w with hξ
    set C : ℂ := ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ d *
      Complex.exp (((‖ξ‖ ^ 2 / 4 : ℝ) : ℂ)) with hCdef
    have hC : C ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ ?_) (Complex.exp_ne_zero _)
      have : (0 : ℝ) < Real.pi ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos Real.pi_pos _
      exact_mod_cast this.ne'
    have hzero := hgen (fun i => Complex.I * (ξ i : ℂ) / (Real.sqrt 2 : ℂ))
    have hrw : (∫ t : RealVec d, star ((f : RealVec d → ℂ) t) *
          tensorGenerating t (fun i => Complex.I * (ξ i : ℂ) / (Real.sqrt 2 : ℂ))) =
        C * ∫ t : RealVec d, star ((f : RealVec d → ℂ) t) *
          (((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((inner ℝ t ξ : ℝ) : ℂ))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      rw [tensorGenerating_imaginary t ξ, hCdef]
      ring
    rw [hrw] at hzero
    have hint0 : (∫ t : RealVec d, star ((f : RealVec d → ℂ) t) *
        (((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((inner ℝ t ξ : ℝ) : ℂ)))) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hC
    rw [Real.fourier_eq', ← hint0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    have hinner : (inner ℝ t ξ : ℝ) = -(2 * Real.pi) * (inner ℝ t w : ℝ) := by
      rw [hξ, real_inner_smul_right]
    have harg : Complex.I * ((inner ℝ t ξ : ℝ) : ℂ) =
        ((-2 * Real.pi * (inner ℝ t w : ℝ) : ℝ) : ℂ) * Complex.I := by
      rw [hinner]; push_cast; ring
    rw [smul_eq_mul, harg]
    ring
  have hfmem : MemLp (f : RealVec d → ℂ) 2 (volume : Measure (RealVec d)) := Lp.memLp f
  have hint : Integrable
      (fun t : RealVec d =>
        star ((f : RealVec d → ℂ) t) * ((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ)) volume :=
    MemLp.integrable_mul (p := 2) (q := 2) hfmem.star (memLp_gaussian d)
  have hmem2 : MemLp
      (fun t : RealVec d =>
        star ((f : RealVec d → ℂ) t) * ((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ)) 2 volume := by
    refine hfmem.of_le (hfmem.1.star.mul (memLp_gaussian d).1) ?_
    filter_upwards with t
    rw [norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hle : Real.exp (-(‖t‖ ^ 2) / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖t‖])
    nlinarith [norm_nonneg ((f : RealVec d → ℂ) t), Real.exp_nonneg (-(‖t‖ ^ 2) / 2)]
  have hae := fourier_l1_l2_eq_zero_ae hint hmem2 hfourier
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [hae] with t ht
  have hexp : ((Real.exp (-(‖t‖ ^ 2) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-(‖t‖ ^ 2) / 2))
  have hstar : star ((f : RealVec d → ℂ) t) = 0 := (mul_eq_zero.mp ht).resolve_right hexp
  simpa using star_eq_zero.mp hstar

/-- The Hermite functions span a dense subspace of `L²(ℝ^d)`. -/
theorem realHermiteTensorL2_span_dense (d : ℕ) :
    (Submodule.span ℂ (Set.range (realHermiteTensorL2 (d := d)))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  refine Submodule.eq_bot_iff _ |>.mpr fun f hf => ?_
  refine eq_zero_of_inner_realHermiteTensorL2_eq_zero f fun α => ?_
  exact (Submodule.mem_orthogonal _ f).mp hf _
    (Submodule.subset_span (Set.mem_range_self α))

/-! ## The Hilbert basis and the surjectivity of `hermiteExpansion` -/

/-- The Hermite functions as a Hilbert basis of `L²(ℝ^d)`. -/
def hermiteHilbertBasis (d : ℕ) : HilbertBasis (Idx d) ℂ (L2Real d) :=
  HilbertBasis.mk (realHermiteTensorL2_orthonormal (d := d))
    (le_of_eq (realHermiteTensorL2_span_dense d).symm)

@[simp]
theorem hermiteHilbertBasis_apply {d : ℕ} (α : Idx d) :
    hermiteHilbertBasis d α = realHermiteTensorL2 α := by
  simp only [hermiteHilbertBasis, HilbertBasis.coe_mk]

/-- The Hermite coefficients of `f ∈ L²(ℝ^d)`, as a square-summable family. -/
def hermiteCoeffs {d : ℕ} (f : L2Real d) : Coeffs d where
  coeff := fun α => inner ℂ (realHermiteTensorL2 α) f
  summable_norm_sq := by
    have h := (lp.memℓp ((hermiteHilbertBasis d).repr f)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
    have hfun :
        (fun α : Idx d => ‖((hermiteHilbertBasis d).repr f) α‖ ^ (2 : ENNReal).toReal) =
          fun α : Idx d => ‖inner ℂ (realHermiteTensorL2 α) f‖ ^ (2 : ℕ) := by
      funext α
      rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        HilbertBasis.repr_apply_apply, hermiteHilbertBasis_apply]
    exact hfun ▸ h

@[simp]
theorem coeffAt_hermiteCoeffs {d : ℕ} (f : L2Real d) (α : Idx d) :
    coeffAt (hermiteCoeffs f) α = inner ℂ (realHermiteTensorL2 α) f := rfl

/-- The Hermite expansion of the Hermite coefficients of `f` is `f`. -/
theorem hermiteExpansion_hermiteCoeffs {d : ℕ} (f : L2Real d) :
    hermiteExpansion (hermiteCoeffs f) = f := by
  have h := (hermiteHilbertBasis d).hasSum_repr f
  have hfun :
      (fun α : Idx d => ((hermiteHilbertBasis d).repr f) α • (hermiteHilbertBasis d) α) =
        fun α : Idx d => coeffAt (hermiteCoeffs f) α • realHermiteTensorL2 α := by
    funext α
    rw [HilbertBasis.repr_apply_apply, hermiteHilbertBasis_apply, coeffAt_hermiteCoeffs]
  rw [hfun] at h
  exact h.tsum_eq

/-- Every element of `L²(ℝ^d)` is a Hermite expansion. -/
theorem hermiteExpansion_surjective {d : ℕ} :
    Function.Surjective (hermiteExpansion (d := d)) :=
  fun f => ⟨hermiteCoeffs f, hermiteExpansion_hermiteCoeffs f⟩

/-- `hermiteExpansion` is a bijection between square-summable coefficient families and
`L²(ℝ^d)`. -/
theorem hermiteExpansion_bijective {d : ℕ} :
    Function.Bijective (hermiteExpansion (d := d)) :=
  ⟨hermiteExpansion_injective, hermiteExpansion_surjective⟩

end ModulusRecovery
