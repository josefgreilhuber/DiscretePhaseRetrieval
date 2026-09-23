import ContinuousPhaseRetrieval.ModulusRecovery.MixedLevel
import DiscretePhaseRetrieval.UnitScale

/-!
# Phase-space geometry, the Gaussian window as a Hermite combination, and membership in `𝓕_h`

Three independent ingredients of the STFT corollary (`STFT.lean`).

* **Phase-space geometry.**  The map `phaseToC (x, ξ) = (x - 2πi ξ)/√2` is injective, admits the
  explicit inverse `phaseToCInv`, and turns `DiscretePR.phaseDistUnit` into
  `DiscretePR.euclideanDist`.
* **The window as a finite Hermite combination.**  Triangularity of the one-dimensional Hermite
  functions against the monomial-times-Gaussian family gives, by strong induction,
  `tⁿ e^{-t²/2} ∈ span {ψ_0, …, ψ_n}`; taking products this is the `d`-dimensional statement for
  monomials, and summing over the monomials of a polynomial `h` it is the statement that
  `DiscretePR.gaussWindowUnit h` is a finite combination `∑ c_α ψ_α` of the Hermite basis, both
  pointwise and in `L²`.  The signed family `signedConj c` is the family of level weights whose
  mixed window (`MixedLevel.lean`) is the normalised window.
* **Membership in the comparator's space.**  The mixed-level evaluations `toFunH h U` are exactly
  the functions `DiscretePR.polyanalyticEval h F` of the comparator, they are `L²(γ)` and
  continuous, hence they lie in `DiscretePR.PolyFockSpace h`.
-/

noncomputable section

namespace ModulusRecovery

open MeasureTheory
open scoped BigOperators

variable {d : ℕ}

/-! ## Phase-space geometry -/

/-- The squared modulus of `a - 2πi b` for real `a`, `b`. -/
private theorem norm_sq_sub_two_pi_I_mul (a b : ℝ) :
    ‖(a : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (b : ℂ)‖ ^ 2
      = a ^ 2 + (2 * Real.pi) ^ 2 * b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

/-- The squared modulus of a `phaseToC`-difference. -/
private theorem norm_sq_phaseToC_term (a b : ℝ) :
    ‖((a : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (b : ℂ)) / (Real.sqrt 2 : ℂ)‖ ^ 2
      = (a ^ 2 + (2 * Real.pi) ^ 2 * b ^ 2) / 2 := by
  have h2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [norm_div, div_pow, h2, norm_sq_sub_two_pi_I_mul]

/-- `phaseToC` is an isometry from `phaseDistUnit` to `euclideanDist`. -/
theorem phaseDist_eq (x ξ x' ξ' : RealVec d) :
    DiscretePR.phaseDistUnit x ξ x' ξ' =
      DiscretePR.euclideanDist (phaseToC (x, ξ)) (phaseToC (x', ξ')) := by
  unfold DiscretePR.phaseDistUnit DiscretePR.euclideanDist
  congr 1
  have hterm : ∀ i : Fin d,
      ‖phaseToC (x, ξ) i - phaseToC (x', ξ') i‖ ^ 2
        = ((x i - x' i) ^ 2 + (2 * Real.pi) ^ 2 * (ξ i - ξ' i) ^ 2) / 2 := by
    intro i
    have hsub : phaseToC (x, ξ) i - phaseToC (x', ξ') i
        = (((x i - x' i : ℝ) : ℂ) -
            (2 * Real.pi : ℂ) * Complex.I * ((ξ i - ξ' i : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ) := by
      simp only [phaseToC]
      push_cast
      ring
    rw [hsub, norm_sq_phaseToC_term]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by simp

theorem phaseToC_injective : Function.Injective (phaseToC (d := d)) := by
  rintro ⟨x, ξ⟩ ⟨x', ξ'⟩ hxy
  have hzero : DiscretePR.phaseDistUnit x ξ x' ξ' = 0 := by
    rw [phaseDist_eq]
    simp only [DiscretePR.euclideanDist]
    rw [show phaseToC ((x, ξ) : PhaseSpace d) = phaseToC ((x', ξ') : PhaseSpace d) from hxy]
    simp
  have hA : (0 : ℝ) ≤ ‖x - x'‖ ^ 2 := sq_nonneg _
  have hB : (0 : ℝ) ≤ ‖ξ - ξ'‖ ^ 2 := sq_nonneg _
  have hc : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hle := Real.sqrt_eq_zero'.mp hzero
  have hx' : x = x' := by
    have hx0 : ‖x - x'‖ ^ 2 = 0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hx0))
  have hξ' : ξ = ξ' := by
    have hξ0 : ‖ξ - ξ'‖ ^ 2 = 0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hξ0))
  rw [hx', hξ']

/-- The explicit inverse of `phaseToC`: `x = √2 Re z`, `ξ = -√2 Im z/(2π)`. -/
def phaseToCInv (z : Cd d) : PhaseSpace d :=
  (WithLp.toLp 2 fun q => Real.sqrt 2 * (z q).re,
    WithLp.toLp 2 fun q => -(Real.sqrt 2 * (z q).im) / (2 * Real.pi))

theorem phaseToC_phaseToCInv (z : Cd d) : phaseToC (phaseToCInv z) = z := by
  funext q
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  change (((Real.sqrt 2 * (z q).re : ℝ) : ℂ) -
      (2 * Real.pi : ℂ) * Complex.I *
        ((-(Real.sqrt 2 * (z q).im) / (2 * Real.pi) : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ) = z q
  push_cast
  rw [div_eq_iff h2]
  conv_rhs => rw [← Complex.re_add_im (z q)]
  field_simp
  ring

/-! ## One-dimensional triangularity -/

/-- The coefficient of `tⁿ e^{-t²/2}` in `ψ_n` is nonzero: it is
`(√n!/n!) π^{-1/4} (√2)ⁿ`, by `Polynomial.coeff_hermite_self`. -/
private theorem realHermite1D_lead_ne_zero (n : ℕ) :
    ((Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)) *
        realHermiteGeneratingExpansionCoeff n n ≠ 0 := by
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast n.factorial_pos
  refine mul_ne_zero (div_ne_zero ?_ ?_) ?_
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hfac))
  · exact Nat.cast_ne_zero.mpr n.factorial_ne_zero
  · rw [realHermiteGeneratingExpansionCoeff_eq_scaled_hermite_coeff,
      Polynomial.coeff_hermite_self]
    refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
    · exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _))
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by positivity))
    · norm_num

/-- `tⁿ e^{-t²/2}` is a linear combination of `ψ_0, …, ψ_n` (`Finset.range`-indexed form). -/
private theorem monomialGaussian_expansion_range (n : ℕ) :
    ∃ c : ℕ → ℂ, ∀ t : ℝ,
      complex_monomial_gaussian n t
        = ∑ k ∈ Finset.range (n + 1), c k * realHermite1D k t := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    have IH2 : ∀ k : ℕ, ∃ c : ℕ → ℂ, k < n → ∀ t : ℝ,
        complex_monomial_gaussian k t
          = ∑ j ∈ Finset.range (n + 1), c j * realHermite1D j t := by
      intro k
      by_cases hk : k < n
      · obtain ⟨c, hc⟩ := IH k hk
        refine ⟨fun j => if j < k + 1 then c j else 0, fun _ t => ?_⟩
        have hsub : ∑ j ∈ Finset.range (k + 1),
              (if j < k + 1 then c j else 0) * realHermite1D j t
            = ∑ j ∈ Finset.range (n + 1),
              (if j < k + 1 then c j else 0) * realHermite1D j t :=
          Finset.sum_subset
            (fun j hj => Finset.mem_range.mpr (by
              have := Finset.mem_range.mp hj; omega))
            (fun j _ hj => by rw [if_neg (by simpa using hj), zero_mul])
        rw [hc t, ← hsub]
        exact Finset.sum_congr rfl fun j hj => by
          rw [if_pos (Finset.mem_range.mp hj)]
      · exact ⟨0, fun hkn => absurd hkn hk⟩
    choose C hC using IH2
    set s : ℂ := (Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ) with hs
    have hlead : s * realHermiteGeneratingExpansionCoeff n n ≠ 0 :=
      realHermite1D_lead_ne_zero n
    refine ⟨fun j => (s * realHermiteGeneratingExpansionCoeff n n)⁻¹ *
        ((if j = n then (1 : ℂ) else 0) -
          s * ∑ k ∈ Finset.range n, realHermiteGeneratingExpansionCoeff n k * C k j),
      fun t => ?_⟩
    have hpsi : realHermite1D n t
        = s * ∑ k ∈ Finset.range (n + 1),
            realHermiteGeneratingExpansionCoeff n k * complex_monomial_gaussian k t := by
      rw [realHermite1D, realHermiteGenerating_iteratedDeriv_zero_expansion_monomial, hs]
    have hlow : ∑ k ∈ Finset.range n,
          realHermiteGeneratingExpansionCoeff n k * complex_monomial_gaussian k t
        = ∑ j ∈ Finset.range (n + 1),
            (∑ k ∈ Finset.range n, realHermiteGeneratingExpansionCoeff n k * C k j) *
              realHermite1D j t := by
      rw [Finset.sum_congr rfl (fun k hk => by
        rw [hC k (Finset.mem_range.mp hk) t, Finset.mul_sum]), Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hsplit : realHermite1D n t
        = s * (∑ k ∈ Finset.range n,
              realHermiteGeneratingExpansionCoeff n k * complex_monomial_gaussian k t)
          + (s * realHermiteGeneratingExpansionCoeff n n) * complex_monomial_gaussian n t := by
      rw [hpsi, Finset.sum_range_succ, mul_add]
      ring
    have key : (s * realHermiteGeneratingExpansionCoeff n n) * complex_monomial_gaussian n t
        = ∑ j ∈ Finset.range (n + 1),
            ((if j = n then (1 : ℂ) else 0) -
              s * ∑ k ∈ Finset.range n,
                realHermiteGeneratingExpansionCoeff n k * C k j) * realHermite1D j t := by
      rw [Finset.sum_congr rfl (fun j _ => sub_mul _ _ _), Finset.sum_sub_distrib]
      have h1 : ∑ j ∈ Finset.range (n + 1),
          (if j = n then (1 : ℂ) else 0) * realHermite1D j t = realHermite1D n t := by
        simp
      have h2 : ∑ j ∈ Finset.range (n + 1),
            (s * ∑ k ∈ Finset.range n,
              realHermiteGeneratingExpansionCoeff n k * C k j) * realHermite1D j t
          = s * ∑ j ∈ Finset.range (n + 1),
              (∑ k ∈ Finset.range n,
                realHermiteGeneratingExpansionCoeff n k * C k j) * realHermite1D j t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h1, h2, ← hlow, hsplit]
      ring
    rw [Finset.sum_congr rfl (fun j _ => mul_assoc _ _ _), ← Finset.mul_sum, ← key,
      inv_mul_cancel_left₀ hlead]

/-- `tⁿ e^{-t²/2}` is a finite combination of `ψ_0, …, ψ_n` (pointwise, as functions `ℝ → ℂ`). -/
theorem monomialGaussian_mem_span (n : ℕ) :
    ∃ c : Fin (n + 1) → ℂ, ∀ t : ℝ,
      (t : ℂ) ^ n * Complex.exp (-(t : ℂ) ^ 2 / 2)
        = ∑ k, c k * realHermite1D (k : ℕ) t := by
  obtain ⟨c, hc⟩ := monomialGaussian_expansion_range n
  refine ⟨fun k => c (k : ℕ), fun t => ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun k => c k * realHermite1D k t) (n + 1), ← hc t,
    complex_monomial_gaussian]
  ring_nf

/-! ## The Hermite span in `d` dimensions -/

/-- The `ℂ`-span of the Hermite tensor functions inside the functions `ℝ^d → ℂ`. -/
private def hermiteSpan (d : ℕ) : Submodule ℂ (RealVec d → ℂ) :=
  Submodule.span ℂ (Set.range fun α : Idx d => (realHermiteTensorRep α : RealVec d → ℂ))

private theorem mem_hermiteSpan_of_tensorRep (α : Idx d) :
    (realHermiteTensorRep α : RealVec d → ℂ) ∈ hermiteSpan d :=
  Submodule.subset_span ⟨α, rfl⟩

/-- An element of the Hermite span is an explicit finitely supported combination. -/
private theorem exists_finsupp_of_mem_hermiteSpan {f : RealVec d → ℂ} (hf : f ∈ hermiteSpan d) :
    ∃ c : Idx d →₀ ℂ, ∀ x : RealVec d,
      f x = ∑ α ∈ c.support, c α * realHermiteTensorRep α x := by
  rw [hermiteSpan, Finsupp.mem_span_range_iff_exists_finsupp] at hf
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun x => ?_⟩
  rw [← hc]
  simp [Finsupp.sum, Finset.sum_apply]

/-- `x^β e^{-|x|²/2}` lies in the Hermite span. -/
private theorem monomialGaussian_tensor_mem_hermiteSpan (β : Fin d → ℕ) :
    (fun x : RealVec d =>
        (∏ i, (x i : ℂ) ^ β i) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)) ∈ hermiteSpan d := by
  classical
  choose C hC using fun i : Fin d => monomialGaussian_expansion_range (β i)
  have hpt : (fun x : RealVec d =>
        (∏ i, (x i : ℂ) ^ β i) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ))
      = ∑ α ∈ Fintype.piFinset fun i => Finset.range (β i + 1),
          (∏ i, C i (α i)) • (realHermiteTensorRep α : RealVec d → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hgauss : ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)
        = ∏ i : Fin d, Complex.exp (-((x i : ℂ) ^ 2) / 2) := by
      have h1 : (-‖x‖ ^ 2 / 2 : ℝ) = ∑ i : Fin d, -((x i : ℝ) ^ 2) / 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_div, ← Finset.sum_neg_distrib]
      rw [h1, Real.exp_sum, Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hfac : ∀ i : Fin d,
        (x i : ℂ) ^ β i * Complex.exp (-((x i : ℂ) ^ 2) / 2)
          = ∑ k ∈ Finset.range (β i + 1), C i k * realHermite1D k (x i) := by
      intro i
      rw [← hC i (x i), complex_monomial_gaussian]
      ring_nf
    rw [hgauss, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => hfac i),
      Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.prod_mul_distrib]
    rfl
  rw [hpt]
  exact Submodule.sum_mem _ fun α _ =>
    Submodule.smul_mem _ _ (mem_hermiteSpan_of_tensorRep α)

/-- `x^β e^{-|x|²/2}` on `ℝ^d` as a finite combination of the `ψ_α`. -/
theorem monomialGaussian_tensor_mem_span (β : Fin d → ℕ) :
    ∃ c : (Fin d → ℕ) →₀ ℂ, ∀ x : RealVec d,
      (∏ i, (x i : ℂ) ^ β i) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)
        = ∑ α ∈ c.support, c α * realHermiteTensorRep α x :=
  exists_finsupp_of_mem_hermiteSpan (monomialGaussian_tensor_mem_hermiteSpan β)

/-! ## The polynomial-times-Gaussian window -/

/-- The window function of a real polynomial, `h(x) e^{-|x|²/2}`. -/
def gaussWindowRep (h : MvPolynomial (Fin d) ℝ) : RealVec d → ℂ :=
  fun x => ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)

private theorem gaussWindowRep_def (h : MvPolynomial (Fin d) ℝ) :
    gaussWindowRep h = fun x : RealVec d =>
      ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ) := rfl

theorem gaussWindowRep_apply (h : MvPolynomial (Fin d) ℝ) (x : RealVec d) :
    gaussWindowRep h x =
      ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ) := rfl

private theorem gaussWindowRep_mem_hermiteSpan (h : MvPolynomial (Fin d) ℝ) :
    gaussWindowRep h ∈ hermiteSpan d := by
  classical
  have hpt : gaussWindowRep h
      = ∑ β ∈ h.support, ((MvPolynomial.coeff β h : ℝ) : ℂ) •
          (fun x : RealVec d =>
            (∏ i, (x i : ℂ) ^ (β i)) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gaussWindowRep]
    rw [MvPolynomial.eval_eq', Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    push_cast
    ring
  rw [hpt]
  exact Submodule.sum_mem _ fun β _ =>
    Submodule.smul_mem _ _ (monomialGaussian_tensor_mem_hermiteSpan fun i => β i)

theorem gaussWindowRep_memLp (h : MvPolynomial (Fin d) ℝ) :
    MemLp (gaussWindowRep h) 2 (volume : Measure (RealVec d)) := by
  obtain ⟨c, hc⟩ := exists_finsupp_of_mem_hermiteSpan (gaussWindowRep_mem_hermiteSpan h)
  have hfun : gaussWindowRep h
      = fun x : RealVec d => ∑ α ∈ c.support, c α * realHermiteTensorRep α x := funext hc
  rw [hfun]
  refine memLp_finsetSum _ fun α _ => MemLp.const_mul ?_ _
  exact realHermiteTensorRep_memLp_of_realHermite1D_memLp α
    realHermite1D_memLp_inner_orthonormal.1

theorem gaussWindow_eq_toLp (h : MvPolynomial (Fin d) ℝ) :
    DiscretePR.gaussWindowUnit h = (gaussWindowRep_memLp h).toLp (gaussWindowRep h) := by
  have hmem := gaussWindowRep_memLp h
  rw [DiscretePR.gaussWindowUnit]
  exact dif_pos hmem

/-- The window `h(x) e^{-|x|²/2}` as a finite combination of the Hermite functions `ψ_α`,
pointwise and in `L²`. -/
theorem gaussWindow_eq_sum (h : MvPolynomial (Fin d) ℝ) :
    ∃ c : (Fin d → ℕ) →₀ ℂ,
      (∀ x : RealVec d,
          ((MvPolynomial.eval (fun i => x i) h : ℝ) : ℂ) * ((Real.exp (-‖x‖ ^ 2 / 2) : ℝ) : ℂ)
            = ∑ α ∈ c.support, c α * realHermiteTensorRep α x) ∧
        DiscretePR.gaussWindowUnit h = ∑ α ∈ c.support, c α • realHermiteTensorL2 α := by
  classical
  obtain ⟨c, hc⟩ := exists_finsupp_of_mem_hermiteSpan (gaussWindowRep_mem_hermiteSpan h)
  refine ⟨c, hc, ?_⟩
  have hae : ∀ α ∈ c.support, ∀ᵐ x ∂(volume : Measure (RealVec d)),
      ((c α • realHermiteTensorL2 α : L2Real d) : RealVec d → ℂ) x
        = c α * realHermiteTensorRep α x := by
    intro α _
    filter_upwards [Lp.coeFn_smul (c α) (realHermiteTensorL2 α),
      varphiKappa_coe_ae_eq_realHermiteTensorRep α] with x h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun w => c α * w) h2
  rw [gaussWindow_eq_toLp]
  apply MeasureTheory.Lp.ext
  filter_upwards [(gaussWindowRep_memLp h).coeFn_toLp,
    MeasureTheory.Lp.coeFn_fun_finsetSum c.support
      (fun α => c α • realHermiteTensorL2 α),
    (Filter.eventually_all_finset c.support).mpr hae] with x h1 h2 h3
  rw [h1, h2]
  exact (hc x).trans (Finset.sum_congr rfl fun α hα => (h3 α hα).symm)

theorem gaussWindow_ne_zero {h : MvPolynomial (Fin d) ℝ} (hnonzero : h ≠ 0) :
    DiscretePR.gaussWindowUnit h ≠ 0 := by
  intro hzero
  rw [gaussWindow_eq_toLp] at hzero
  have hcoe := (gaussWindowRep_memLp h).coeFn_toLp
  rw [hzero] at hcoe
  have hae : gaussWindowRep h =ᵐ[(volume : Measure (RealVec d))] (fun _ => 0) :=
    hcoe.symm.trans (MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure (RealVec d)))
  have hcont : Continuous (gaussWindowRep h) := by
    have heq : (fun x : RealVec d => (MvPolynomial.eval (fun i => x i) h : ℝ))
        = fun x : RealVec d => ∑ β ∈ h.support,
            MvPolynomial.coeff β h * ∏ i, (x i : ℝ) ^ (β i) :=
      funext fun x => MvPolynomial.eval_eq' _ _
    have hP : Continuous (fun x : RealVec d => (MvPolynomial.eval (fun i => x i) h : ℝ)) := by
      rw [heq]
      refine continuous_finsetSum _ fun β _ => continuous_const.mul ?_
      exact continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 _ i).pow _
    rw [gaussWindowRep_def]
    exact (Complex.continuous_ofReal.comp hP).mul
      (Complex.continuous_ofReal.comp (by fun_prop))
  have hzero' : gaussWindowRep h = fun _ => 0 :=
    (hcont.ae_eq_iff_eq (volume : Measure (RealVec d)) continuous_const).mp hae
  refine hnonzero (MvPolynomial.funext fun v => ?_)
  have hv0 := congrFun hzero' (WithLp.toLp 2 v)
  rw [gaussWindowRep_apply] at hv0
  have hexp : ((Real.exp (-‖(WithLp.toLp 2 v : RealVec d)‖ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hval : ((MvPolynomial.eval (fun i => (WithLp.toLp 2 v : RealVec d) i) h : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hv0 with hw | hw
    · exact hw
    · exact absurd hw hexp
  have hreal : (MvPolynomial.eval v h : ℝ) = 0 := by exact_mod_cast hval
  rw [hreal, map_zero]

/-! ## The signed family of level weights -/

/-- The level weights of a coefficient family: `h'_α = (-1)^{|α|} conj(c_α)`.  Its `weight`
(`MixedLevel.lean`) is `c_α/‖c‖`, so its mixed window is the normalised window. -/
def signedConj (c : (Fin d → ℕ) →₀ ℂ) : (Fin d → ℕ) →₀ ℂ :=
  Finsupp.onFinset c.support (fun α => (-1 : ℂ) ^ (∑ i, α i) * star (c α)) (by
    intro α hα
    refine Finsupp.mem_support_iff.mpr fun hzero => ?_
    rw [hzero] at hα
    simp at hα)

@[simp] theorem signedConj_apply (c : (Fin d → ℕ) →₀ ℂ) (α : Fin d → ℕ) :
    signedConj c α = (-1 : ℂ) ^ (∑ i, α i) * star (c α) := rfl

theorem signedConj_support (c : (Fin d → ℕ) →₀ ℂ) : (signedConj c).support = c.support := by
  ext α
  simp only [Finsupp.mem_support_iff, signedConj_apply]
  constructor
  · intro hα hzero
    rw [hzero] at hα
    simp at hα
  · exact fun hα => mul_ne_zero (pow_ne_zero _ (by norm_num)) (star_ne_zero.mpr hα)

theorem signedConj_ne_zero {c : (Fin d → ℕ) →₀ ℂ} (hc : c ≠ 0) : signedConj c ≠ 0 := by
  intro h0
  exact hc (by rw [← Finsupp.support_eq_empty, ← signedConj_support, h0, Finsupp.support_zero])

theorem hnorm_signedConj (c : (Fin d → ℕ) →₀ ℂ) : hnorm (signedConj c) = hnorm c := by
  unfold hnorm
  rw [signedConj_support]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [signedConj_apply]
  simp

theorem weight_signedConj (c : (Fin d → ℕ) →₀ ℂ) (α : Fin d → ℕ) :
    weight (signedConj c) α = c α / ((hnorm c : ℝ) : ℂ) := by
  have hsq : ((-1 : ℂ) ^ (∑ i, α i)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [weight, hnorm_signedConj, signedConj_apply]
  congr 1
  rw [star_mul', star_star, (by simp : star ((-1 : ℂ) ^ (∑ i, α i)) = (-1 : ℂ) ^ (∑ i, α i))]
  calc (-1 : ℂ) ^ (∑ i, α i) * ((-1 : ℂ) ^ (∑ i, α i) * c α)
      = ((-1 : ℂ) ^ (∑ i, α i)) ^ 2 * c α := by ring
    _ = c α := by rw [hsq, one_mul]

theorem windowH_signedConj (c : (Fin d → ℕ) →₀ ℂ) :
    windowH (signedConj c)
      = ((hnorm c : ℝ)⁻¹ : ℂ) • ∑ α ∈ c.support, c α • realHermiteTensorL2 α := by
  rw [windowH, signedConj_support, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [weight_signedConj, smul_smul, div_eq_inv_mul]
  rfl

/-! ## The mixed-level functions lie in the comparator's space -/

/-- A coefficient family as an element of the comparator's `ℓ²` (the inverse of the
`toCoeffs` of `ContinuousPR.lean`): the coefficient function is literally the same. -/
def ofCoeffs (U : Coeffs d) : DiscretePR.PolyFock d :=
  ⟨U.coeff, memℓp_gen (by
    have h2 : ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) := by norm_num
    have hfun : (fun α : Fin d → ℕ => ‖U.coeff α‖ ^ (2 : ENNReal).toReal)
        = fun α : Fin d → ℕ => ‖U.coeff α‖ ^ (2 : ℕ) := by
      funext α
      rw [h2, Real.rpow_natCast]
    rw [hfun]
    exact U.summable_norm_sq)⟩

@[simp] theorem ofCoeffs_apply (U : Coeffs d) (α : Fin d → ℕ) :
    ofCoeffs U α = U.coeff α := rfl

theorem toFunH_eq_polyanalyticEval (h : (Fin d → ℕ) →₀ ℂ) (U : Coeffs d) :
    toFunH h U = DiscretePR.polyanalyticEval h (ofCoeffs U) := rfl

theorem memLp_toFun (hd : 0 < d) (kappa : MultiIndex d) (U : Coeffs d) :
    MemLp (toFun kappa U) 2 (gamma_d d) := by
  obtain ⟨hmem, -⟩ := l2_tsum_represents_toFun hd kappa U
  exact hmem

theorem memLp_toFunH (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (U : Coeffs d) :
    MemLp (toFunH h U) 2 (gamma_d d) := by
  have heq : toFunH h U
      = fun z : Cd d => ∑ q ∈ h.support, (h q / ((hnorm h : ℝ) : ℂ)) * toFun q U z :=
    funext fun z => toFunH_eq_finsetSum h U z
  rw [heq]
  exact memLp_finsetSum _ fun q _ => (memLp_toFun hd q U).const_mul _

theorem continuous_toFunH (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (U : Coeffs d) :
    Continuous (toFunH h U) := by
  have heq : toFunH h U
      = fun z : Cd d => ∑ q ∈ h.support, (h q / ((hnorm h : ℝ) : ℂ)) * toFun q U z :=
    funext fun z => toFunH_eq_finsetSum h U z
  rw [heq]
  exact continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_toFun hd q U)

/-- The Gaussian measure of the comparator is the Gaussian measure of this development. -/
theorem gamma_eq_DiscretePR_gamma : (DiscretePR.γ : Measure (Cd d)) = gamma_d d := rfl

theorem toFunH_mem_polyFockSpace (hd : 0 < d) (h : (Fin d → ℕ) →₀ ℂ) (U : Coeffs d) :
    toFunH h U ∈ DiscretePR.PolyFockSpace h := by
  refine ⟨?_, continuous_toFunH hd h U, ofCoeffs U, toFunH_eq_polyanalyticEval h U⟩
  rw [gamma_eq_DiscretePR_gamma]
  exact memLp_toFunH hd h U

end ModulusRecovery
