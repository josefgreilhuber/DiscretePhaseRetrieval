import DiscreteNorming.Defs
import Warren.SignPatterns.SignPatternBound

/-!
# Claim C4b: shattering by the universal family forces all sign patterns

For `K` points `y^1, …, y^K ∈ ℂ^N` shattered by `univFamily N`, the `K` polynomials
`p_ℓ(a, b) = (|Σ a_j y^ℓ_j|² − |Σ b_j y^ℓ_j|²)² − 1` (degree 4 in the `4N` real variables
`Re a, Im a, Re b, Im b`, read off `v : Fin (4N) → ℝ` by `coords`) realise all `2^K` strict sign
patterns: for `T ⊆ [K]` shattering gives `(a, b)` with `p_ℓ(a,b) ≥ 0 ⟺ ℓ ∈ T`; scaling `(a, b)`
by `λ > 1` close to `1` makes every sign strict (`p_ℓ(λa, λb) = λ⁴ q_ℓ² − 1`).
-/

open MeasureTheory

namespace DiscreteNorming

/-- The universal family `𝒢_N = {{y ∈ ℂ^N : ||Σ a_j y_j|² − |Σ b_j y_j|²| ≥ 1} : a, b ∈ ℂ^N}`. -/
def univFamily (N : ℕ) : Set (Set (Fin N → ℂ)) :=
  {A | ∃ a b : Fin N → ℂ, A = {y | 1 ≤ |‖∑ j, a j * y j‖ ^ 2 - ‖∑ j, b j * y j‖ ^ 2|}}

/-- The quadratic form `q_{a,b}(y) = |Σ a_j y_j|² − |Σ b_j y_j|²` as a real polynomial in the
`4N` real variables `(Re a, Im a, Re b, Im b)` (the point `y` is fixed), and the polynomials
`p_ℓ = q_{a,b}(y^ℓ)² − 1`. `coords v = (a, b)` reads the coefficient vectors off `v : Fin (4N) → ℝ`.
-/
def coords {N : ℕ} (v : Fin (4 * N) → ℝ) : (Fin N → ℂ) × (Fin N → ℂ) :=
  (fun j ↦ ⟨v ⟨j, by omega⟩, v ⟨j + N, by omega⟩⟩,
   fun j ↦ ⟨v ⟨j + 2 * N, by omega⟩, v ⟨j + 3 * N, by omega⟩⟩)

/-! ### Linear forms and the squared norm of a linear combination -/

open MvPolynomial in
/-- The linear form `∑ j, (c j · X (o₁ j) + d j · X (o₂ j))`. -/
noncomputable def linForm {n N : ℕ} (c d : Fin N → ℝ) (o₁ o₂ : Fin N → Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin N, (MvPolynomial.C (c j) * MvPolynomial.X (o₁ j) +
    MvPolynomial.C (d j) * MvPolynomial.X (o₂ j))

open MvPolynomial in
lemma eval_linForm {n N : ℕ} (c d : Fin N → ℝ) (o₁ o₂ : Fin N → Fin n) (v : Fin n → ℝ) :
    MvPolynomial.eval v (linForm c d o₁ o₂) = ∑ j, (c j * v (o₁ j) + d j * v (o₂ j)) := by
  simp only [linForm, map_sum, map_add, map_mul, eval_C, eval_X]

open MvPolynomial in
lemma totalDegree_linForm {n N : ℕ} (c d : Fin N → ℝ) (o₁ o₂ : Fin N → Fin n) :
    (linForm c d o₁ o₂).totalDegree ≤ 1 := by
  refine totalDegree_finsetSum_le fun j _ => ?_
  refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;>
  · refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_C, totalDegree_X]

/-- `|∑ aⱼ wⱼ|²` in terms of the real and imaginary parts of the `aⱼ`. -/
lemma sq_norm_sum_mul {N : ℕ} (a w : Fin N → ℂ) :
    ‖∑ j, a j * w j‖ ^ 2 =
      (∑ j, ((w j).re * (a j).re + -(w j).im * (a j).im)) ^ 2 +
      (∑ j, ((w j).im * (a j).re + (w j).re * (a j).im)) ^ 2 := by
  have h1 : ∑ j, (a j * w j).re = ∑ j, ((w j).re * (a j).re + -(w j).im * (a j).im) :=
    Finset.sum_congr rfl fun j _ => by rw [Complex.mul_re]; ring
  have h2 : ∑ j, (a j * w j).im = ∑ j, ((w j).im * (a j).re + (w j).re * (a j).im) :=
    Finset.sum_congr rfl fun j _ => by rw [Complex.mul_im]; ring
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum, h1, h2]
  ring

/-! ### A right inverse of `coords` -/

/-- Assemble a real coordinate vector out of two complex vectors; a right inverse of `coords`. -/
noncomputable def mkCoords {N : ℕ} (a b : Fin N → ℂ) (i : Fin (4 * N)) : ℝ :=
  if h1 : (i : ℕ) < N then (a ⟨i, h1⟩).re
  else if h2 : (i : ℕ) < 2 * N then (a ⟨(i : ℕ) - N, by omega⟩).im
  else if h3 : (i : ℕ) < 3 * N then (b ⟨(i : ℕ) - 2 * N, by omega⟩).re
  else (b ⟨(i : ℕ) - 3 * N, by omega⟩).im

lemma coords_mkCoords {N : ℕ} (a b : Fin N → ℂ) : coords (mkCoords a b) = (a, b) := by
  have h0 : ∀ j : Fin N, mkCoords a b ⟨(j : ℕ), by omega⟩ = (a j).re := by
    intro j
    have h1 : (j : ℕ) < N := j.isLt
    simp only [mkCoords, dif_pos h1, Fin.eta]
  have h1 : ∀ j : Fin N, mkCoords a b ⟨(j : ℕ) + N, by omega⟩ = (a j).im := by
    intro j
    have hj : (j : ℕ) < N := j.isLt
    have e1 : ¬ ((j : ℕ) + N < N) := by omega
    have e2 : (j : ℕ) + N < 2 * N := by omega
    have e3 : ((j : ℕ) + N - N) = (j : ℕ) := by omega
    simp only [mkCoords, dif_neg e1, dif_pos e2]
    congr 2
    exact Fin.ext e3
  have h2 : ∀ j : Fin N, mkCoords a b ⟨(j : ℕ) + 2 * N, by omega⟩ = (b j).re := by
    intro j
    have hj : (j : ℕ) < N := j.isLt
    have e1 : ¬ ((j : ℕ) + 2 * N < N) := by omega
    have e2 : ¬ ((j : ℕ) + 2 * N < 2 * N) := by omega
    have e3 : (j : ℕ) + 2 * N < 3 * N := by omega
    have e4 : ((j : ℕ) + 2 * N - 2 * N) = (j : ℕ) := by omega
    simp only [mkCoords, dif_neg e1, dif_neg e2, dif_pos e3]
    congr 2
    exact Fin.ext e4
  have h3 : ∀ j : Fin N, mkCoords a b ⟨(j : ℕ) + 3 * N, by omega⟩ = (b j).im := by
    intro j
    have hj : (j : ℕ) < N := j.isLt
    have e1 : ¬ ((j : ℕ) + 3 * N < N) := by omega
    have e2 : ¬ ((j : ℕ) + 3 * N < 2 * N) := by omega
    have e3 : ¬ ((j : ℕ) + 3 * N < 3 * N) := by omega
    have e4 : ((j : ℕ) + 3 * N - 3 * N) = (j : ℕ) := by omega
    simp only [mkCoords, dif_neg e1, dif_neg e2, dif_neg e3]
    congr 2
    exact Fin.ext e4
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · exact Complex.ext (h0 j) (h1 j)
  · exact Complex.ext (h2 j) (h3 j)

/-! ### The sign polynomials -/

theorem exists_signPoly {N K : ℕ} (y : Fin K → Fin N → ℂ) :
    ∃ p : Fin K → MvPolynomial (Fin (4 * N)) ℝ, (∀ ℓ, (p ℓ).totalDegree ≤ 4) ∧
      ∀ ℓ v, MvPolynomial.eval v (p ℓ) =
        (‖∑ j, (coords v).1 j * y ℓ j‖ ^ 2 - ‖∑ j, (coords v).2 j * y ℓ j‖ ^ 2) ^ 2 - 1 := by
  classical
  set i0 : Fin N → Fin (4 * N) := fun j => ⟨(j : ℕ), by omega⟩ with hi0
  set i1 : Fin N → Fin (4 * N) := fun j => ⟨(j : ℕ) + N, by omega⟩ with hi1
  set i2 : Fin N → Fin (4 * N) := fun j => ⟨(j : ℕ) + 2 * N, by omega⟩ with hi2
  set i3 : Fin N → Fin (4 * N) := fun j => ⟨(j : ℕ) + 3 * N, by omega⟩ with hi3
  -- the four linear forms attached to the point `y ℓ`
  set Ra : Fin K → MvPolynomial (Fin (4 * N)) ℝ := fun ℓ =>
    linForm (fun j => (y ℓ j).re) (fun j => -(y ℓ j).im) i0 i1 with hRa
  set Ia : Fin K → MvPolynomial (Fin (4 * N)) ℝ := fun ℓ =>
    linForm (fun j => (y ℓ j).im) (fun j => (y ℓ j).re) i0 i1 with hIa
  set Rb : Fin K → MvPolynomial (Fin (4 * N)) ℝ := fun ℓ =>
    linForm (fun j => (y ℓ j).re) (fun j => -(y ℓ j).im) i2 i3 with hRb
  set Ib : Fin K → MvPolynomial (Fin (4 * N)) ℝ := fun ℓ =>
    linForm (fun j => (y ℓ j).im) (fun j => (y ℓ j).re) i2 i3 with hIb
  refine ⟨fun ℓ => ((Ra ℓ) ^ 2 + (Ia ℓ) ^ 2 - ((Rb ℓ) ^ 2 + (Ib ℓ) ^ 2)) ^ 2 -
      MvPolynomial.C 1, ?_, ?_⟩
  · -- degree bound
    intro ℓ
    have hsq : ∀ c d : Fin N → ℝ, ∀ o₁ o₂ : Fin N → Fin (4 * N),
        ((linForm c d o₁ o₂) ^ 2).totalDegree ≤ 2 := by
      intro c d o₁ o₂
      refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
      have := totalDegree_linForm c d o₁ o₂
      omega
    have hQ : (((Ra ℓ) ^ 2 + (Ia ℓ) ^ 2 - ((Rb ℓ) ^ 2 + (Ib ℓ) ^ 2))).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hsq _ _ _ _) (hsq _ _ _ _))
      · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hsq _ _ _ _) (hsq _ _ _ _))
    refine (MvPolynomial.totalDegree_sub_C_le _ _).trans ?_
    refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
    omega
  · -- evaluation
    intro ℓ v
    have hA : ‖∑ j, (coords v).1 j * y ℓ j‖ ^ 2 =
        (MvPolynomial.eval v (Ra ℓ)) ^ 2 + (MvPolynomial.eval v (Ia ℓ)) ^ 2 := by
      rw [sq_norm_sum_mul, hRa, hIa]
      simp only [eval_linForm, hi0, hi1, coords]
    have hB : ‖∑ j, (coords v).2 j * y ℓ j‖ ^ 2 =
        (MvPolynomial.eval v (Rb ℓ)) ^ 2 + (MvPolynomial.eval v (Ib ℓ)) ^ 2 := by
      rw [sq_norm_sum_mul, hRb, hIb]
      simp only [eval_linForm, hi2, hi3, coords]
    rw [hA, hB]
    simp only [map_sub, map_pow, map_add, MvPolynomial.eval_C]

/-- Shattering `K` points by `univFamily N` forces all `2^K` strict sign patterns of the
polynomials `p_ℓ` (scaling trick). -/
theorem shatter_signPatterns {N K : ℕ} (y : Fin K → Fin N → ℂ) (hinj : Function.Injective y)
    (hsh : ∀ T : Finset (Fin K), ∃ A ∈ univFamily N, ∀ ℓ, y ℓ ∈ A ↔ ℓ ∈ T)
    (p : Fin K → MvPolynomial (Fin (4 * N)) ℝ)
    (hp : ∀ ℓ v, MvPolynomial.eval v (p ℓ) =
        (‖∑ j, (coords v).1 j * y ℓ j‖ ^ 2 - ‖∑ j, (coords v).2 j * y ℓ j‖ ^ 2) ^ 2 - 1) :
    (2 : ℝ) ^ K ≤ ((SignPatterns.strictSignPatterns p).ncard : ℝ) := by
  classical
  -- Every `±1` pattern of the form `σ_T` is realised.
  have key : ∀ T : Finset (Fin K),
      (fun ℓ => if ℓ ∈ T then (1 : SignType) else -1) ∈ SignPatterns.strictSignPatterns p := by
    intro T
    obtain ⟨A, hAmem, hA⟩ := hsh T
    obtain ⟨a, b, rfl⟩ := hAmem
    set f : Fin K → ℝ := fun ℓ => ‖∑ j, a j * y ℓ j‖ ^ 2 - ‖∑ j, b j * y ℓ j‖ ^ 2 with hf
    have hmem : ∀ ℓ, 1 ≤ |f ℓ| ↔ ℓ ∈ T := fun ℓ => hA ℓ
    have hin : ∀ ℓ ∈ T, 1 ≤ (f ℓ) ^ 2 := by
      intro ℓ hℓ
      have h := (hmem ℓ).2 hℓ
      nlinarith [abs_nonneg (f ℓ), sq_abs (f ℓ)]
    have hout : ∀ ℓ, ℓ ∉ T → (f ℓ) ^ 2 < 1 := by
      intro ℓ hℓ
      have h : |f ℓ| < 1 := not_le.1 fun hc => hℓ ((hmem ℓ).1 hc)
      nlinarith [abs_nonneg (f ℓ), sq_abs (f ℓ)]
    -- the largest value of `(f ℓ)²` over `ℓ ∉ T` (or `0` if there is none)
    set g : Fin K → ℝ := fun ℓ => if ℓ ∈ T then 0 else (f ℓ) ^ 2 with hg
    set S : Finset ℝ := insert (0 : ℝ) (Finset.image g Finset.univ) with hS
    have hSne : S.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
    set m : ℝ := S.max' hSne with hm
    have hm0 : (0 : ℝ) ≤ m := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
    have hm1 : m < 1 := by
      rw [hm, Finset.max'_lt_iff]
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · norm_num
      · obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.1 hz
        by_cases h : ℓ ∈ T
        · simp only [hg, if_pos h]; norm_num
        · simpa only [hg, if_neg h] using hout ℓ h
    have hmg : ∀ ℓ, g ℓ ≤ m :=
      fun ℓ => Finset.le_max' _ _
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ ℓ)))
    -- the scaling factor
    set c : ℝ := 2 / (1 + m) with hc
    have h1m : (0 : ℝ) < 1 + m := by linarith
    have hc1 : 1 < c := by rw [hc, lt_div_iff₀ h1m]; linarith
    have hc0 : (0 : ℝ) < c := by linarith
    have hcm : c * m < 1 := by
      rw [hc, div_mul_eq_mul_div, div_lt_one h1m]; linarith
    set lam : ℝ := Real.sqrt (Real.sqrt c) with hlam
    have hlam0 : (0 : ℝ) ≤ lam := Real.sqrt_nonneg _
    have hlam4 : lam ^ 4 = c := by
      have e1 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
      have e2 : lam ^ 2 = Real.sqrt c := Real.sq_sqrt (Real.sqrt_nonneg c)
      calc lam ^ 4 = (lam ^ 2) ^ 2 := by ring
        _ = c := by rw [e2, e1]
    set v : Fin (4 * N) → ℝ :=
      mkCoords (fun j => (lam : ℂ) * a j) (fun j => (lam : ℂ) * b j) with hv
    have hscale : ∀ (w : Fin N → ℂ) (ℓ : Fin K),
        ‖∑ j, ((lam : ℂ) * w j) * y ℓ j‖ ^ 2 = lam ^ 2 * ‖∑ j, w j * y ℓ j‖ ^ 2 := by
      intro w ℓ
      have e : (∑ j, ((lam : ℂ) * w j) * y ℓ j) = (lam : ℂ) * ∑ j, w j * y ℓ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam0]
    have hev : ∀ ℓ, MvPolynomial.eval v (p ℓ) = c * (f ℓ) ^ 2 - 1 := by
      intro ℓ
      rw [hp ℓ v, hv, coords_mkCoords]
      simp only
      rw [hscale a ℓ, hscale b ℓ]
      have e : (lam ^ 2 * ‖∑ j, a j * y ℓ j‖ ^ 2 - lam ^ 2 * ‖∑ j, b j * y ℓ j‖ ^ 2) ^ 2
          = lam ^ 4 * (f ℓ) ^ 2 := by
        simp only [hf]; ring
      rw [e, hlam4]
    refine ⟨fun ℓ => by by_cases h : ℓ ∈ T <;> simp [h], ⟨v, fun ℓ => ?_⟩⟩
    simp only [hev ℓ]
    by_cases h : ℓ ∈ T
    · rw [if_pos h]
      exact sign_pos (by nlinarith [hin ℓ h])
    · rw [if_neg h]
      refine sign_neg ?_
      have h1 : (f ℓ) ^ 2 ≤ m := by simpa only [hg, if_neg h] using hmg ℓ
      nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le]
  -- Counting: the `2^K` patterns `σ_T` are pairwise distinct.
  set Φ : Finset (Fin K) → (Fin K → SignType) :=
    fun T ℓ => if ℓ ∈ T then 1 else -1 with hΦ
  have hinjΦ : Function.Injective Φ := by
    intro T₁ T₂ h
    ext ℓ
    have hℓ := congrFun h ℓ
    simp only [hΦ] at hℓ
    by_cases h1 : ℓ ∈ T₁ <;> by_cases h2 : ℓ ∈ T₂ <;> simp [h1, h2] at hℓ ⊢
  have himg : Φ '' Set.univ ⊆ SignPatterns.strictSignPatterns p := by
    rintro σ ⟨T, -, rfl⟩
    exact key T
  have hcard : (2 : ℕ) ^ K = (Φ '' Set.univ).ncard := by
    rw [Set.ncard_image_of_injective _ hinjΦ, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_finset, Fintype.card_fin]
  have hle : (2 : ℕ) ^ K ≤ (SignPatterns.strictSignPatterns p).ncard := by
    rw [hcard]
    exact Set.ncard_le_ncard himg (Set.toFinite _)
  calc (2 : ℝ) ^ K = (((2 : ℕ) ^ K : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := Nat.cast_le.2 hle

end DiscreteNorming
