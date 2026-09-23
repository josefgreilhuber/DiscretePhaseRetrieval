import DiscreteNorming.Defs

/-!
# Claim C3: `|F|` squared minus `|G|` squared is a real polynomial; rational approximation

* `exists_realPoly`: for complex polynomials `F, G` of degree `<= n` in `d` variables there is a
  real polynomial `Q` of degree `<= 2n` in `2d` variables with `Q(x) = diff F G x` for all `x`.
* `continuous_diff`: `diff F G` is continuous.
* `exists_spanning`: a subspace of dimension `N` is spanned by `N` of its elements.
* `exists_rat_approx`: on a bounded set, `diff (comb phi a) (comb phi b)` is uniformly approximated
  by `diff (ratComb phi a') (ratComb phi b')` with Gaussian-rational coefficient vectors.
-/

open MeasureTheory Metric

namespace DiscreteNorming

/-! ### continuity -/

theorem continuous_coord {d : ℕ} (i : Fin (2 * d)) : Continuous fun x : Pt d ↦ x i := by
  fun_prop

theorem continuous_mkC {α : Type*} [TopologicalSpace α] (f g : α → ℝ)
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x ↦ (⟨f x, g x⟩ : ℂ) := by
  have h : (fun x ↦ (⟨f x, g x⟩ : ℂ)) = fun x ↦ (f x : ℂ) + (g x : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp
  rw [h]; fun_prop

theorem continuous_toC {d : ℕ} : Continuous (toC (d := d)) := by
  apply continuous_pi
  intro j
  exact continuous_mkC _ _ (continuous_coord _) (continuous_coord _)

theorem continuous_diff {d : ℕ} (F G : PolyFock.Fock.P d) : Continuous (diff F G) := by
  have h : ∀ H : PolyFock.Fock.P d, Continuous fun x : Pt d ↦ PolyFock.Fock.ev (toC x) H :=
    fun H ↦ (MvPolynomial.continuous_eval H).comp (continuous_pi (Sum.rec
      (fun j ↦ (continuous_apply j).comp continuous_toC)
      fun j ↦ Complex.continuous_conj.comp ((continuous_apply j).comp continuous_toC)))
  unfold diff; exact ((h F).norm.pow 2).sub ((h G).norm.pow 2)

/-! ### real / imaginary part of a complex polynomial -/

open MvPolynomial in
/-- Apply a real-valued function to all coefficients of a complex polynomial. -/
noncomputable def cpart {m : ℕ} (f : ℂ → ℝ) (p : MvPolynomial (Fin m) ℂ) :
    MvPolynomial (Fin m) ℝ :=
  ∑ s ∈ p.support, MvPolynomial.monomial s (f (p.coeff s))

open MvPolynomial in
theorem eval_cpart {m : ℕ} (f : ℂ → ℝ) (p : MvPolynomial (Fin m) ℂ) (x : Fin m → ℝ) :
    MvPolynomial.eval x (cpart f p)
      = ∑ s ∈ p.support, f (p.coeff s) * ∏ i ∈ s.support, x i ^ s i := by
  unfold cpart
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [MvPolynomial.eval_monomial]
  rfl

open MvPolynomial in
theorem totalDegree_cpart_le {m : ℕ} (f : ℂ → ℝ) (p : MvPolynomial (Fin m) ℂ) :
    (cpart f p).totalDegree ≤ p.totalDegree := by
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs ↦ ?_
  refine (MvPolynomial.totalDegree_monomial_le s _).trans ?_
  simpa [Function.id_def] using MvPolynomial.le_totalDegree hs

open MvPolynomial in
theorem re_eval_cpart {m : ℕ} (p : MvPolynomial (Fin m) ℂ) (x : Fin m → ℝ) :
    (MvPolynomial.eval (fun i ↦ ((x i : ℂ))) p).re
      = MvPolynomial.eval x (cpart Complex.re p) := by
  rw [MvPolynomial.eval_eq, eval_cpart, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have h : ∏ i ∈ s.support, ((x i : ℂ)) ^ s i = ((∏ i ∈ s.support, x i ^ s i : ℝ) : ℂ) := by
    push_cast; ring
  rw [h]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

open MvPolynomial in
theorem im_eval_cpart {m : ℕ} (p : MvPolynomial (Fin m) ℂ) (x : Fin m → ℝ) :
    (MvPolynomial.eval (fun i ↦ ((x i : ℂ))) p).im
      = MvPolynomial.eval x (cpart Complex.im p) := by
  rw [MvPolynomial.eval_eq, eval_cpart, Complex.im_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have h : ∏ i ∈ s.support, ((x i : ℂ)) ^ s i = ((∏ i ∈ s.support, x i ^ s i : ℝ) : ℂ) := by
    push_cast; ring
  rw [h]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

/-! ### substitution -/

open MvPolynomial in
theorem eval_aeval' {σ τ : Type*} (f : σ → MvPolynomial τ ℂ) (g : τ → ℂ)
    (p : MvPolynomial σ ℂ) :
    MvPolynomial.eval g (MvPolynomial.aeval f p)
      = MvPolynomial.eval (fun j ↦ MvPolynomial.eval g (f j)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C, MvPolynomial.eval_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp]

open MvPolynomial in
theorem totalDegree_aeval_le {σ τ : Type*} (f : σ → MvPolynomial τ ℂ)
    (hf : ∀ j, (f j).totalDegree ≤ 1) (p : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs ↦ ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h1 : (algebraMap ℂ (MvPolynomial τ ℂ) (p.coeff s)).totalDegree = 0 := by
    simp [MvPolynomial.algebraMap_eq]
  rw [h1, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  have h2 : ∀ i ∈ s.support, ((f i) ^ (s i)).totalDegree ≤ s i := by
    intro i _
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    calc s i * (f i).totalDegree ≤ s i * 1 := by gcongr; exact hf i
      _ = s i := by ring
  refine (Finset.sum_le_sum h2).trans ?_
  have h3 := MvPolynomial.le_totalDegree hs
  simp only [Finsupp.sum] at h3
  exact h3

open MvPolynomial in
/-- The substituted variables `z_j ↦ x_j + i x_{j+d}`, `z̄_j ↦ x_j − i x_{j+d}`. -/
noncomputable def psiVar (d : ℕ) : PolyFock.Fock.Idx d → MvPolynomial (Fin (2 * d)) ℂ :=
  Sum.elim (fun j ↦ MvPolynomial.X ⟨(j : ℕ), by have := j.isLt; omega⟩
      + MvPolynomial.C Complex.I * MvPolynomial.X ⟨(j : ℕ) + d, by have := j.isLt; omega⟩)
    (fun j ↦ MvPolynomial.X ⟨(j : ℕ), by have := j.isLt; omega⟩
      - MvPolynomial.C Complex.I * MvPolynomial.X ⟨(j : ℕ) + d, by have := j.isLt; omega⟩)

/-- Substitution `z_j ↦ x_j + i x_{j+d}`, `z̄_j ↦ x_j − i x_{j+d}`. -/
noncomputable def psi (d : ℕ) : PolyFock.Fock.P d →ₐ[ℂ] MvPolynomial (Fin (2 * d)) ℂ :=
  MvPolynomial.aeval (psiVar d)

open MvPolynomial in
theorem eval_psi {d : ℕ} (F : PolyFock.Fock.P d) (x : Pt d) :
    MvPolynomial.eval (fun i ↦ ((WithLp.ofLp x i : ℝ) : ℂ)) (psi d F)
      = PolyFock.Fock.ev (toC x) F := by
  have hfun : (fun j ↦ MvPolynomial.eval (fun i ↦ ((WithLp.ofLp x i : ℝ) : ℂ)) (psiVar d j))
      = Sum.elim (toC x) fun i ↦ (starRingEnd ℂ) (toC x i) := by
    funext j
    rcases j with j | j <;>
      simp only [psiVar, Sum.elim_inl, Sum.elim_inr, map_add, map_sub, map_mul, eval_X, eval_C] <;>
      apply Complex.ext <;> simp [toC]
  simp only [psi]
  rw [eval_aeval', hfun]; rfl

open MvPolynomial in
theorem totalDegree_psi_le {d : ℕ} (F : PolyFock.Fock.P d) :
    (psi d F).totalDegree ≤ F.totalDegree := by
  refine totalDegree_aeval_le _ (fun j ↦ ?_) F
  rcases j with j | j
  · exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le (by simp) ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))
  · exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (by simp) ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))

/-- `|F|` squared minus `|G|` squared is a real polynomial of degree `<= 2n` in the `2d` real
coordinates. -/
theorem exists_realPoly {d n : ℕ} (F G : PolyFock.Fock.P d)
    (hF : F.totalDegree ≤ n) (hG : G.totalDegree ≤ n) :
    ∃ Q : MvPolynomial (Fin (2 * d)) ℝ, Q.totalDegree ≤ 2 * n ∧
      ∀ x : Pt d, MvPolynomial.eval (WithLp.ofLp x) Q = diff F G x := by
  classical
  refine ⟨(cpart Complex.re (psi d F)) ^ 2 + (cpart Complex.im (psi d F)) ^ 2
      - ((cpart Complex.re (psi d G)) ^ 2 + (cpart Complex.im (psi d G)) ^ 2), ?_, ?_⟩
  · have hb : ∀ (H : PolyFock.Fock.P d) (f : ℂ → ℝ), H.totalDegree ≤ n →
        ((cpart f (psi d H)) ^ 2).totalDegree ≤ 2 * n := by
      intro H f hH
      refine (MvPolynomial.totalDegree_pow _ _).trans ?_
      have h := (totalDegree_cpart_le f (psi d H)).trans ((totalDegree_psi_le H).trans hH)
      omega
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hb F _ hF) (hb F _ hF))
    · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hb G _ hG) (hb G _ hG))
  · intro x
    simp only [map_sub, map_add, map_pow]
    rw [← re_eval_cpart (psi d F) (WithLp.ofLp x), ← im_eval_cpart (psi d F) (WithLp.ofLp x),
      ← re_eval_cpart (psi d G) (WithLp.ofLp x), ← im_eval_cpart (psi d G) (WithLp.ofLp x),
      eval_psi F x, eval_psi G x]
    simp only [diff, Complex.sq_norm, Complex.normSq_apply]
    ring

/-- A subspace of dimension `N` is spanned by `N` of its elements.

Note: the hypothesis `hN : 1 ≤ N` had to be added to the original statement.  Without it the
claim is false: if `d ≥ 1` and the subspace is `⊤`, then it is infinite dimensional, so its
`Module.finrank` over `ℂ` is `0 = N`, and the conclusion would force every element to be the
empty sum `0`. -/
theorem exists_spanning {d N : ℕ} (𝒱 : Submodule ℂ (PolyFock.Fock.P d))
    (h𝒱 : Module.finrank ℂ 𝒱 = N) (hN : 1 ≤ N) :
    ∃ φ : Fin N → PolyFock.Fock.P d, (∀ j, φ j ∈ 𝒱) ∧
      ∀ F ∈ 𝒱, ∃ a : Fin N → ℂ, F = comb φ a := by
  have hfin : Module.Finite ℂ 𝒱 := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin N) ℂ 𝒱 := Module.finBasisOfFinrankEq ℂ 𝒱 h𝒱
  refine ⟨fun j ↦ ((b j : 𝒱) : PolyFock.Fock.P d), fun j ↦ (b j).2, ?_⟩
  intro F hF
  refine ⟨fun j ↦ b.repr ⟨F, hF⟩ j, ?_⟩
  have h := congrArg (fun v : 𝒱 ↦ (v : PolyFock.Fock.P d)) (b.sum_repr ⟨F, hF⟩)
  simp only [Submodule.coe_sum, SetLike.val_smul] at h
  rw [comb]
  exact h.symm.trans (Finset.sum_congr rfl fun j _ ↦ MvPolynomial.smul_eq_C_mul _ _)

theorem comb_mem {d N : ℕ} {𝒱 : Submodule ℂ (PolyFock.Fock.P d)}
    {φ : Fin N → PolyFock.Fock.P d} (hφ : ∀ j, φ j ∈ 𝒱) (a : Fin N → ℂ) :
    comb φ a ∈ 𝒱 := by
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (hφ j)

theorem totalDegree_comb_le {d N n : ℕ} {φ : Fin N → PolyFock.Fock.P d}
    (hφ : ∀ j, (φ j).totalDegree ≤ n) (a : Fin N → ℂ) : (comb φ a).totalDegree ≤ n := by
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ ↦ ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simpa using hφ j

private theorem abs_sq_norm_sub (u v : ℂ) {M ε : ℝ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M)
    (h : ‖u - v‖ ≤ ε) : |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * M * ε := by
  have h1 : |‖u‖ - ‖v‖| ≤ ε := (abs_norm_sub_norm_le u v).trans h
  have h0 : (0:ℝ) ≤ ‖u‖ + ‖v‖ := by positivity
  have h2 : ‖u‖ + ‖v‖ ≤ 2 * M := by linarith
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) h1
  have hrw : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
  rw [hrw, abs_mul, abs_of_nonneg h0]
  calc |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) ≤ ε * (2 * M) := mul_le_mul h1 h2 h0 hε
    _ = 2 * M * ε := by ring

/-- Uniform rational approximation on a bounded set. -/
theorem exists_rat_approx {d N : ℕ} (φ : Fin N → PolyFock.Fock.P d) {Ω : Set (Pt d)}
    (hb : Bornology.IsBounded Ω) (a b : Fin N → ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ a' b' : Fin N → ℚ × ℚ, ∀ x ∈ Ω,
      |diff (comb φ a) (comb φ b) x - diff (ratComb φ a') (ratComb φ b') x| ≤ η := by
  classical
  have heval : ∀ (c : Fin N → ℂ) (x : Pt d),
      PolyFock.Fock.ev (toC x) (comb φ c) = ∑ j, c j * PolyFock.Fock.ev (toC x) (φ j) := by
    intro c x; simp [comb]
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : Pt d)
  have hScont : Continuous fun x : Pt d ↦ ∑ j, ‖PolyFock.Fock.ev (toC x) (φ j)‖ := by
    refine continuous_finsetSum _ fun j _ ↦ ?_
    simpa [diff, Real.sqrt_sq_eq_abs] using (continuous_diff (φ j) 0).sqrt
  obtain ⟨B0, hB0⟩ := (isCompact_closedBall (0 : Pt d) R).exists_bound_of_continuousOn
    hScont.continuousOn
  set B : ℝ := |B0| + 1 with hBdef
  have hB1 : (1:ℝ) ≤ B := by
    have : (0:ℝ) ≤ |B0| := abs_nonneg _
    rw [hBdef]; linarith
  have hB0' : (0:ℝ) < B := by linarith
  have hSB : ∀ x ∈ Ω, (∑ j, ‖PolyFock.Fock.ev (toC x) (φ j)‖) ≤ B := by
    intro x hx
    have h1 := hB0 x (hR hx)
    have h3 : |B0| ≤ B := by rw [hBdef]; linarith
    calc (∑ j, ‖PolyFock.Fock.ev (toC x) (φ j)‖)
        ≤ ‖∑ j, ‖PolyFock.Fock.ev (toC x) (φ j)‖‖ := le_abs_self _
      _ ≤ B0 := h1
      _ ≤ |B0| := le_abs_self _
      _ ≤ B := h3
  set A : ℝ := 1 + (∑ j, ‖a j‖) + (∑ j, ‖b j‖) with hAdef
  have hsum_a : (0:ℝ) ≤ ∑ j, ‖a j‖ := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hsum_b : (0:ℝ) ≤ ∑ j, ‖b j‖ := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  have hA1 : (1:ℝ) ≤ A := by rw [hAdef]; linarith
  have hAa : ∀ j, ‖a j‖ ≤ A := by
    intro j
    have h := Finset.single_le_sum (f := fun j ↦ ‖a j‖) (fun i _ ↦ norm_nonneg (a i))
      (Finset.mem_univ j)
    rw [hAdef]; linarith
  have hAb : ∀ j, ‖b j‖ ≤ A := by
    intro j
    have h := Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun i _ ↦ norm_nonneg (b i))
      (Finset.mem_univ j)
    rw [hAdef]; linarith
  set M : ℝ := (A + 1) * B with hMdef
  set ρ : ℝ := min 1 (η / (4 * B ^ 2 * (A + 1))) with hρdef
  have hApos : (0:ℝ) < A + 1 := by linarith
  have hρ0 : 0 < ρ := by
    refine lt_min zero_lt_one (div_pos hη ?_)
    positivity
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ2 : ρ ≤ η / (4 * B ^ 2 * (A + 1)) := min_le_right _ _
  have hrat : ∀ z : ℂ, ∃ w : ℚ × ℚ, ‖z - gaussRat w‖ ≤ ρ := by
    intro z
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show z.re - ρ/2 < z.re + ρ/2 by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show z.im - ρ/2 < z.im + ρ/2 by linarith)
    refine ⟨(p, q), ?_⟩
    have h1 : (z - gaussRat (p, q)).re = z.re - (p:ℝ) := by simp [gaussRat]
    have h2 : (z - gaussRat (p, q)).im = z.im - (q:ℝ) := by simp [gaussRat]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [h1, h2]
    have e1 : |z.re - (p:ℝ)| ≤ ρ/2 := by rw [abs_le]; constructor <;> linarith
    have e2 : |z.im - (q:ℝ)| ≤ ρ/2 := by rw [abs_le]; constructor <;> linarith
    linarith
  choose a' ha' using fun j ↦ hrat (a j)
  choose b' hb' using fun j ↦ hrat (b j)
  have key : ∀ (c : Fin N → ℂ) (c' : Fin N → ℚ × ℚ), (∀ j, ‖c j‖ ≤ A) →
      (∀ j, ‖c j - gaussRat (c' j)‖ ≤ ρ) → ∀ x ∈ Ω,
      |‖PolyFock.Fock.ev (toC x) (comb φ c)‖ ^ 2
        - ‖PolyFock.Fock.ev (toC x) (ratComb φ c')‖ ^ 2| ≤ 2 * M * (ρ * B) := by
    intro c c' hc hcc x hx
    have hSx := hSB x hx
    rw [heval c x, ratComb, heval _ x]
    have hnu : ‖∑ j, c j * PolyFock.Fock.ev (toC x) (φ j)‖ ≤ A * B := by
      calc ‖∑ j, c j * PolyFock.Fock.ev (toC x) (φ j)‖
          ≤ ∑ j, ‖c j * PolyFock.Fock.ev (toC x) (φ j)‖ := norm_sum_le _ _
        _ ≤ ∑ j, A * ‖PolyFock.Fock.ev (toC x) (φ j)‖ := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _)
        _ = A * ∑ j, ‖PolyFock.Fock.ev (toC x) (φ j)‖ := by rw [Finset.mul_sum]
        _ ≤ A * B := mul_le_mul_of_nonneg_left hSx (by linarith)
    have hd : ‖(∑ j, c j * PolyFock.Fock.ev (toC x) (φ j))
        - (∑ j, gaussRat (c' j) * PolyFock.Fock.ev (toC x) (φ j))‖ ≤ ρ * B := by
      rw [← Finset.sum_sub_distrib]
      simp only [← sub_mul]
      calc ‖∑ j, (c j - gaussRat (c' j)) * PolyFock.Fock.ev (toC x) (φ j)‖
          ≤ ∑ j, ‖(c j - gaussRat (c' j)) * PolyFock.Fock.ev (toC x) (φ j)‖ := norm_sum_le _ _
        _ ≤ ∑ j, ρ * ‖PolyFock.Fock.ev (toC x) (φ j)‖ := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hcc j) (norm_nonneg _)
        _ = ρ * ∑ j, ‖PolyFock.Fock.ev (toC x) (φ j)‖ := by rw [Finset.mul_sum]
        _ ≤ ρ * B := mul_le_mul_of_nonneg_left hSx hρ0.le
    have hnu' : ‖∑ j, gaussRat (c' j) * PolyFock.Fock.ev (toC x) (φ j)‖ ≤ M := by
      have h3 : ‖∑ j, gaussRat (c' j) * PolyFock.Fock.ev (toC x) (φ j)‖
          ≤ ‖∑ j, c j * PolyFock.Fock.ev (toC x) (φ j)‖
            + ‖(∑ j, c j * PolyFock.Fock.ev (toC x) (φ j))
              - (∑ j, gaussRat (c' j) * PolyFock.Fock.ev (toC x) (φ j))‖ := by
        have h4 := norm_sub_le (∑ j, c j * PolyFock.Fock.ev (toC x) (φ j))
          ((∑ j, c j * PolyFock.Fock.ev (toC x) (φ j))
            - (∑ j, gaussRat (c' j) * PolyFock.Fock.ev (toC x) (φ j)))
        simpa using h4
      have h5 : ρ * B ≤ B := by nlinarith
      rw [hMdef]
      nlinarith
    have hnuM : ‖∑ j, c j * PolyFock.Fock.ev (toC x) (φ j)‖ ≤ M := by
      rw [hMdef]; nlinarith
    exact abs_sq_norm_sub _ _ hnuM hnu' hd
  refine ⟨a', b', fun x hx ↦ ?_⟩
  have k1 := key a a' hAa ha' x hx
  have k2 := key b b' hAb hb' x hx
  have hfinal : 4 * M * (ρ * B) ≤ η := by
    have hAB : (0:ℝ) < 4 * B ^ 2 * (A + 1) := by positivity
    have hkey : ρ * (4 * B ^ 2 * (A + 1)) ≤ η := by
      calc ρ * (4 * B ^ 2 * (A + 1)) ≤ (η / (4 * B ^ 2 * (A + 1))) * (4 * B ^ 2 * (A + 1)) :=
            mul_le_mul_of_nonneg_right hρ2 hAB.le
        _ = η := by field_simp
    rw [hMdef]; nlinarith
  have hsplit : diff (comb φ a) (comb φ b) x - diff (ratComb φ a') (ratComb φ b') x
      = (‖PolyFock.Fock.ev (toC x) (comb φ a)‖ ^ 2
          - ‖PolyFock.Fock.ev (toC x) (ratComb φ a')‖ ^ 2)
        + -(‖PolyFock.Fock.ev (toC x) (comb φ b)‖ ^ 2
          - ‖PolyFock.Fock.ev (toC x) (ratComb φ b')‖ ^ 2) := by
    unfold diff; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  linarith

end DiscreteNorming
