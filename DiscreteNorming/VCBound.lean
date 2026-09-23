import DiscreteNorming.Defs
import DiscreteNorming.ComplexPoly
import DiscreteNorming.SignPoly
import Warren.SignPatterns.SignPatternBound

/-!
# Claim C4: Lemma 2.2 (VC-dimension bound)

The family `superlevelFamily Ω 𝒱 = {{z ∈ Ω : ||F(z)|² − |G(z)|²| ≥ τ}}` has VC dimension at most
`36 N`, `N = dim 𝒱`.

Proof (paper, p. 2). Fix a spanning family `φ₁, …, φ_N` of `𝒱` and `Φ(z) = (φ_j(z))_j : ℂ^d → ℂ^N`.
Every set of the family is `Ω ∩ Φ⁻¹(X)` with `X = {y : ||Σ a_j y_j|² − |Σ b_j y_j|²| ≥ 1}` in the
universal family `univFamily N` (rescale `a, b` by `τ^{−1/2}`), and VC dimension does not
increase under pull-back (C4a). If `y¹, …, y^K` are shattered by `univFamily N`, the `K`
polynomials `p_ℓ(a, b) = (|Σ a_j y^ℓ_j|² − |Σ b_j y^ℓ_j|²)² − 1` (degree 4 in the `4N` real
variables `Re a, Im a, Re b, Im b`) realise all `2^K` strict sign patterns: for `S ⊆ [K]` pick
`(a, b)` with `p_ℓ ≥ 0 ⟺ ℓ ∈ S` and scale by `λ > 1` close to `1` (C4b). Warren's bound
(`SignPatterns.sign_patterns_warren`, with `(K+1)` in place of `K`) gives
`2^K ≤ (4e(K+1)/N)^{4N}`, and `2^x > 16e(x + 1/4)` for `x ≥ 9` yields `K ≤ 36N` (C4c).
-/

open MeasureTheory

namespace DiscreteNorming

/-- VC dimension is non-increasing under pull-back: if every set of `ℱ` is `D ∩ Φ⁻¹(A)` for some
`A ∈ 𝒢`, then `vc ℱ ≤ vc 𝒢`. -/
theorem VCDimLE_preimage {X Y : Type*} {Φ : X → Y} {D : Set X} {ℱ : Set (Set X)}
    {𝒢 : Set (Set Y)} (h : ∀ B ∈ ℱ, ∃ A ∈ 𝒢, B = D ∩ Φ ⁻¹' A) {V : ℕ}
    (hG : VCInequality.VCDimLE 𝒢 V) : VCInequality.VCDimLE ℱ V := by
  classical
  intro s hs
  -- Every shattered point lies in `D`.
  have hsD : ∀ y ∈ s, y ∈ D := by
    intro y hy
    obtain ⟨B, hBF, hB⟩ := hs s (le_refl s)
    obtain ⟨A, _, rfl⟩ := h B hBF
    exact ((hB y hy).2 hy).1
  -- `Φ` is injective on `s`.
  have hinj : Set.InjOn Φ s := by
    intro y₁ h₁ y₂ h₂ hEq
    by_contra hne
    obtain ⟨B, hBF, hB⟩ := hs {y₁} (Finset.singleton_subset_iff.2 h₁)
    obtain ⟨A, _, rfl⟩ := h B hBF
    have hy1 : y₁ ∈ D ∩ Φ ⁻¹' A := (hB y₁ h₁).2 (Finset.mem_singleton_self y₁)
    have hy2 : y₂ ∈ D ∩ Φ ⁻¹' A := by
      refine ⟨hsD y₂ h₂, ?_⟩
      have : Φ y₂ ∈ A := by rw [← hEq]; exact hy1.2
      exact this
    have := (hB y₂ h₂).1 hy2
    rw [Finset.mem_singleton] at this
    exact hne this.symm
  have hcard : (s.image Φ).card = s.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  refine hG _ ?_
  intro t' _
  obtain ⟨B, hBF, hB⟩ := hs (s.filter fun y ↦ Φ y ∈ t') (Finset.filter_subset _ _)
  obtain ⟨A, hA, rfl⟩ := h B hBF
  refine ⟨A, hA, ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
  constructor
  · intro hzA
    have hmem : y ∈ D ∩ Φ ⁻¹' A := ⟨hsD y hy, hzA⟩
    exact (Finset.mem_filter.1 ((hB y hy).1 hmem)).2
  · intro hzt
    exact ((hB y hy).2 (Finset.mem_filter.2 ⟨hy, hzt⟩)).2

/-- Arithmetic: `2^K ≤ (4e(K+1)/N)^{4N}` forces `K ≤ 36 N` (for `N ≥ 1`). -/
theorem card_le_of_signPatterns {N K : ℕ} (hN : 1 ≤ N)
    (h : (2 : ℝ) ^ K ≤ (4 * Real.exp 1 * (K + 1) / N) ^ (4 * N)) : K ≤ 36 * N := by
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨x, hKx⟩ : ∃ x : ℝ, (K : ℝ) = x * (4 * N) := ⟨(K : ℝ) / (4 * N), by field_simp⟩
  have hx9 : 9 < x := by
    have hlt : (36 * N : ℝ) < K := by exact_mod_cast hcon
    nlinarith [hN0, hlt, hKx]
  -- rewrite `2 ^ K` as `(2 ^ x) ^ (4 N)`
  have key : ((2 : ℝ) ^ x) ^ (4 * N) = (2 : ℝ) ^ K := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ x) (4 * N), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ) K]
    congr 1
    push_cast
    linarith [hKx]
  -- take `4N`-th roots
  have hbase : (2 : ℝ) ^ x ≤ 4 * Real.exp 1 * ((K : ℝ) + 1) / N := by
    have h1 : ((2 : ℝ) ^ x) ^ (4 * N) ≤ (4 * Real.exp 1 * ((K : ℝ) + 1) / N) ^ (4 * N) := by
      rw [key]; exact h
    have hp1 : (0 : ℝ) ≤ (2 : ℝ) ^ x := (Real.rpow_pos_of_pos (by norm_num) x).le
    have hp2 : (0 : ℝ) ≤ 4 * Real.exp 1 * ((K : ℝ) + 1) / N := by positivity
    exact (pow_le_pow_iff_left₀ hp1 hp2 (by omega)).1 h1
  -- crude linear upper bound on the right-hand side
  have hRHS : 4 * Real.exp 1 * ((K : ℝ) + 1) / N ≤ 16 * Real.exp 1 * x + 4 * Real.exp 1 := by
    have h1 : ((K : ℝ) + 1) / N ≤ 4 * x + 1 := by
      rw [div_le_iff₀ hN0, hKx]
      nlinarith [hNge]
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    calc 4 * Real.exp 1 * ((K : ℝ) + 1) / N = 4 * Real.exp 1 * (((K : ℝ) + 1) / N) := by ring
      _ ≤ 4 * Real.exp 1 * (4 * x + 1) := by nlinarith
      _ = 16 * Real.exp 1 * x + 4 * Real.exp 1 := by ring
  -- but `2 ^ x` grows faster
  have hmain : 16 * Real.exp 1 * x + 4 * Real.exp 1 < (2 : ℝ) ^ x := by
    have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hxpos : (0 : ℝ) < x - 9 := by linarith
    have h9 : (2 : ℝ) ^ (9 : ℝ) = 512 := by
      rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have hsplit : (2 : ℝ) ^ x = 512 * (2 : ℝ) ^ (x - 9) := by
      rw [← h9, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hpow : (2 : ℝ) ^ (x - 9) = Real.exp (Real.log 2 * (x - 9)) :=
      Real.rpow_def_of_pos (by norm_num) _
    have hge : Real.log 2 * (x - 9) + 1 ≤ Real.exp (Real.log 2 * (x - 9)) :=
      Real.add_one_le_exp _
    have hA : Real.exp 1 * (x - 9) < 2.7182818286 * (x - 9) :=
      mul_lt_mul_of_pos_right hexp hxpos
    have hB : 0.6931471803 * (x - 9) < Real.log 2 * (x - 9) :=
      mul_lt_mul_of_pos_right hlog hxpos
    rw [hsplit, hpow]
    nlinarith [hge, hA, hB, hexp, hlog, hxpos]
  linarith

/-- The universal family has VC dimension `≤ 36 N`. -/
theorem vcDim_univFamily {N : ℕ} (hN : 1 ≤ N) : VCInequality.VCDimLE (univFamily N) (36 * N) := by
  classical
  intro s hs
  by_contra hcon
  rw [Nat.not_le] at hcon
  obtain ⟨y, hyinj, hymem, -⟩ :
      ∃ y : Fin s.card → (Fin N → ℂ), Function.Injective y ∧ (∀ ℓ, y ℓ ∈ s) ∧
        ∀ z ∈ s, ∃ ℓ, y ℓ = z := by
    refine ⟨fun ℓ ↦ ((s.equivFin.symm ℓ : s) : Fin N → ℂ), ?_, fun ℓ ↦ (s.equivFin.symm ℓ).2, ?_⟩
    · intro ℓ₁ ℓ₂ hEq
      exact s.equivFin.symm.injective (Subtype.ext hEq)
    · intro z hz
      exact ⟨s.equivFin ⟨z, hz⟩, by simp⟩
  -- translate shattering to an indexed statement
  have hsh : ∀ T : Finset (Fin s.card), ∃ A ∈ univFamily N, ∀ ℓ, y ℓ ∈ A ↔ ℓ ∈ T := by
    intro T
    have hsub : T.image y ⊆ s := by
      intro z hz
      obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.1 hz
      exact hymem ℓ
    obtain ⟨A, hA, hAs⟩ := hs (T.image y) hsub
    refine ⟨A, hA, fun ℓ ↦ ?_⟩
    rw [hAs (y ℓ) (hymem ℓ)]
    exact hyinj.mem_finset_image
  obtain ⟨p, hpdeg, hp⟩ := exists_signPoly y
  have hcount := shatter_signPatterns y hyinj hsh p hp
  have hwarren := SignPatterns.sign_patterns_warren p 4 hpdeg (by omega) (by omega)
  have hfinal : (2 : ℝ) ^ s.card ≤ (4 * Real.exp 1 * ((s.card : ℝ) + 1) / N) ^ (4 * N) := by
    refine hcount.trans (hwarren.trans (le_of_eq ?_))
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hmax : max 2 4 = (4 : ℕ) := by norm_num
    rw [hmax]
    congr 1
    push_cast
    field_simp
  have := card_le_of_signPatterns hN hfinal
  omega

/-- Rescaling the coefficient vector by `(√τ)⁻¹` divides the squared norm by `τ`. -/
private lemma norm_sq_div_sqrt {N : ℕ} {τ : ℝ} (hτ : 0 < τ) (c y : Fin N → ℂ) :
    ‖∑ j, (c j / (Real.sqrt τ : ℂ)) * y j‖ ^ 2 = ‖∑ j, c j * y j‖ ^ 2 / τ := by
  have hs : (0 : ℝ) < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hsC : ((Real.sqrt τ : ℝ) : ℂ) ≠ 0 := by
    simpa using hs.ne'
  have hsum : ∑ j, (c j / (Real.sqrt τ : ℂ)) * y j
      = ((Real.sqrt τ : ℝ) : ℂ)⁻¹ * ∑ j, c j * y j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
  rw [hsum, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    inv_pow, Real.sq_sqrt hτ.le]
  ring

/-- **Lemma 2.2.** The family of superlevel sets `{z ∈ Ω : ||F(z)|² − |G(z)|²| ≥ τ}`,
`F, G ∈ 𝒱`, `τ > 0`, has VC dimension at most `36 N` where `N = dim 𝒱`. -/
theorem vcDim_superlevel_family {d N : ℕ} (hN : 1 ≤ N) (Ω : Set (Pt d))
    (𝒱 : Submodule ℂ (PolyFock.Fock.P d)) (h𝒱 : Module.finrank ℂ 𝒱 = N) :
    VCInequality.VCDimLE (superlevelFamily Ω 𝒱) (36 * N) := by
  classical
  obtain ⟨φ, -, hspan⟩ := exists_spanning 𝒱 h𝒱 hN
  refine VCDimLE_preimage (Φ := fun (x : Pt d) (j : Fin N) ↦ PolyFock.Fock.ev (toC x) (φ j))
    (D := Ω) ?_ (vcDim_univFamily hN)
  have heval : ∀ (c : Fin N → ℂ) (x : Pt d),
      PolyFock.Fock.ev (toC x) (comb φ c)
        = ∑ j, c j * PolyFock.Fock.ev (toC x) (φ j) := by
    intro c x
    simp [comb]
  rintro B ⟨F, hF, G, hG, τ, hτ, rfl⟩
  obtain ⟨a, rfl⟩ := hspan F hF
  obtain ⟨b, rfl⟩ := hspan G hG
  have main : ∀ x : Pt d, (τ ≤ |diff (comb φ a) (comb φ b) x|) ↔
      1 ≤ |‖∑ j, (a j / (Real.sqrt τ : ℂ)) * PolyFock.Fock.ev (toC x) (φ j)‖ ^ 2
          - ‖∑ j, (b j / (Real.sqrt τ : ℂ)) * PolyFock.Fock.ev (toC x) (φ j)‖ ^ 2| := by
    intro x
    have e1 : ‖∑ j, a j * PolyFock.Fock.ev (toC x) (φ j)‖ ^ 2
        - ‖∑ j, b j * PolyFock.Fock.ev (toC x) (φ j)‖ ^ 2
        = diff (comb φ a) (comb φ b) x := by
      simp only [diff, heval]
    rw [norm_sq_div_sqrt hτ, norm_sq_div_sqrt hτ, div_sub_div_same, e1, abs_div,
      abs_of_pos hτ, le_div_iff₀ hτ, one_mul]
  refine ⟨{y : Fin N → ℂ | 1 ≤ |‖∑ j, (a j / (Real.sqrt τ : ℂ)) * y j‖ ^ 2
      - ‖∑ j, (b j / (Real.sqrt τ : ℂ)) * y j‖ ^ 2|}, ⟨_, _, rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, main x]

end DiscreteNorming
