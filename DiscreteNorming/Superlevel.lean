import DiscreteNorming.Defs
import DiscreteNorming.Chebyshev
import DiscreteNorming.ComplexPoly

/-!
# Claim C2: superlevel sets of `|F|² − |G|²` are large

Let `Ω ⊆ ℝ^{2d}` be bounded and measurable, `Ω̂ = hull Ω`, `P = diff F G` with `F, G` of degree
`≤ n`, and `x₀ ∈ Ω̂` a maximum point of `|P|` on `Ω̂`, `K = |P(x₀)|`. For `0 < t < 1` put
`θ = (t|Ω| + |Ω̂ \ Ω|)/|Ω̂|` and `β = θ^{1/(2d)}`. Then

    |{z ∈ Ω : |P(z)| ≥ K / T_{2n}((1+β)/(1−β))}| ≥ t |Ω|,

and, when `θ ≤ 2^{−4d}`, `|{z ∈ Ω : |P(z)| ≥ exp(−8 n θ^{1/(4d)}) K}| ≥ t |Ω|` (paper, p. 3).

Proof (by contradiction): if the superlevel set `S` has measure `< t|Ω|`, apply the Remez
inequality on `V = Ω̂` to `E = Ω \ S` (measurable, `|E| > (1−t)|Ω| > 0`,
`|V \ E| = |V \ Ω| + |S| < θ|V|`), where `|P| < K/T(β)`; since `T_{2n}` is strictly increasing
and `β' = (|V \ E|/|V|)^{1/(2d)} < β`, this gives `K = |P(x₀)| < K`. (For `n = 0`, `P` is constant
and `S = Ω`.) The transport between `Pt d` and `Fin (2d) → ℝ` is `WithLp.ofLp`
(`EuclideanSpace.volume_preserving_measurableEquiv`, `EuclideanSpace.equiv`).
-/

open MeasureTheory Metric Polynomial Polynomial.Chebyshev

namespace DiscreteNorming

theorem isCompact_hull {d : ℕ} {Ω : Set (Pt d)} (hb : Bornology.IsBounded Ω) :
    IsCompact (hull Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (Bornology.IsBounded.closure (isBounded_convexHull.2 hb))

theorem convex_hull' {d : ℕ} (Ω : Set (Pt d)) : Convex ℝ (hull Ω) :=
  (convex_convexHull ℝ Ω).closure

theorem subset_hull {d : ℕ} (Ω : Set (Pt d)) : Ω ⊆ hull Ω :=
  (subset_convexHull ℝ Ω).trans subset_closure

theorem measurableSet_hull {d : ℕ} (Ω : Set (Pt d)) : MeasurableSet (hull Ω) :=
  isClosed_closure.measurableSet

/-- `|Ω̂| = |Ω| + |Ω̂ \ Ω|`, finite for bounded `Ω`. -/
theorem vol_hull_eq {d : ℕ} {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) :
    vol (hull Ω) = vol Ω + vol (hull Ω \ Ω) := by
  have hfin : volume (hull Ω) ≠ ⊤ := (isCompact_hull hb).measure_lt_top.ne
  have h := measureReal_inter_add_diff (μ := volume) (s := hull Ω) hΩ hfin
  rw [Set.inter_eq_self_of_subset_right (subset_hull Ω)] at h
  exact h.symm

/-- `|P|` attains its maximum on `Ω̂`. -/
theorem exists_max_on_hull {d : ℕ} {Ω : Set (Pt d)} (hb : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (F G : PolyFock.Fock.P d) :
    ∃ x₀ ∈ hull Ω, ∀ x ∈ hull Ω, |diff F G x| ≤ |diff F G x₀| := by
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_hull hb).exists_isMaxOn (hne.mono (subset_hull Ω))
    ((continuous_diff F G).abs.continuousOn)
  exact ⟨x₀, hx₀, fun x hx => hmax hx⟩

/-! ### Transport between `Pt d` and `Fin (2d) → ℝ` -/

lemma convex_ofLp_image {d : ℕ} {A : Set (Pt d)} (hA : Convex ℝ A) :
    Convex ℝ ((WithLp.ofLp : Pt d → (Fin (2 * d) → ℝ)) '' A) := by
  have h := hA.linear_image (WithLp.linearEquiv 2 ℝ (Fin (2 * d) → ℝ)).toLinearMap
  simpa using h

lemma isCompact_ofLp_image {d : ℕ} {A : Set (Pt d)} (hA : IsCompact A) :
    IsCompact ((WithLp.ofLp : Pt d → (Fin (2 * d) → ℝ)) '' A) :=
  hA.image (PiLp.continuous_ofLp _ _)

lemma volume_ofLp_image {d : ℕ} {A : Set (Pt d)} (hA : MeasurableSet A) :
    volume ((WithLp.ofLp : Pt d → (Fin (2 * d) → ℝ)) '' A) = volume A := by
  have himg : (WithLp.ofLp : Pt d → (Fin (2 * d) → ℝ)) '' A
      = (WithLp.toLp 2 : (Fin (2 * d) → ℝ) → Pt d) ⁻¹' A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨WithLp.toLp 2 y, hy, rfl⟩
  rw [himg]
  exact (PiLp.volume_preserving_toLp (Fin (2 * d))).measure_preimage hA.nullMeasurableSet

lemma vol_ofLp_image {d : ℕ} {A : Set (Pt d)} (hA : MeasurableSet A) :
    (volume ((WithLp.ofLp : Pt d → (Fin (2 * d) → ℝ)) '' A)).toReal = vol A := by
  rw [volume_ofLp_image hA]; rfl

/-! ### Auxiliary elementary inequalities -/

/-- `y ↦ (1+y)/(1−y)` is strictly monotone on `[0, 1)`. -/
lemma div_lt_div_of_lt_one {a b : ℝ} (_ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    (1 + a) / (1 - a) < (1 + b) / (1 - b) := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - b := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

lemma one_le_div_one_sub {a : ℝ} (_ha : 0 ≤ a) (ha1 : a < 1) : (1 : ℝ) ≤ (1 + a) / (1 - a) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-! ### The main estimate -/

/-- **Superlevel sets are large, Chebyshev form.** -/
theorem superlevel_measure_ge_T {d n : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < vol Ω)
    {F G : PolyFock.Fock.P d} (hF : F.totalDegree ≤ n) (hG : G.totalDegree ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x₀ : Pt d} (hx₀ : x₀ ∈ hull Ω) (hmax : ∀ x ∈ hull Ω, |diff F G x| ≤ |diff F G x₀|) :
    t * vol Ω ≤ vol {x ∈ Ω |
      |diff F G x₀| / (T ℝ (2 * n)).eval
        ((1 + theta Ω t ^ (1 / (2 * d : ℝ))) / (1 - theta Ω t ^ (1 / (2 * d : ℝ))))
      ≤ |diff F G x|} := by
  classical
  -- notation
  have hdR : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hexp : 0 < 1 / (2 * d : ℝ) := by positivity
  set V : Set (Pt d) := hull Ω with hV_def
  have hVcpt : IsCompact V := isCompact_hull hb
  have hVconv : Convex ℝ V := convex_hull' Ω
  have hVmeas : MeasurableSet V := measurableSet_hull Ω
  have hΩV : Ω ⊆ V := subset_hull Ω
  have hVfin : volume V ≠ ⊤ := hVcpt.measure_lt_top.ne
  have hΩfin : volume Ω ≠ ⊤ := ne_top_of_le_ne_top hVfin (measure_mono hΩV)
  have hvolΩV : vol Ω ≤ vol V := ENNReal.toReal_mono hVfin (measure_mono hΩV)
  have hVpos : 0 < vol V := lt_of_lt_of_le hpos hvolΩV
  have hhull := vol_hull_eq hΩ hb
  rw [← hV_def] at hhull
  -- the parameter θ
  have hdiffnn : 0 ≤ vol (V \ Ω) := ENNReal.toReal_nonneg
  have hθ_eq : theta Ω t = (t * vol Ω + vol (V \ Ω)) / vol V := rfl
  have hθ0 : 0 ≤ theta Ω t := by
    rw [hθ_eq]
    apply div_nonneg _ hVpos.le
    nlinarith
  have hθ1 : theta Ω t < 1 := by
    rw [hθ_eq, div_lt_one hVpos]
    nlinarith
  set β : ℝ := theta Ω t ^ (1 / (2 * d : ℝ)) with hβ_def
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hθ0 _
  have hβ1 : β < 1 := Real.rpow_lt_one hθ0 hθ1 hexp
  set y : ℝ := (1 + β) / (1 - β) with hy_def
  have hy1 : (1 : ℝ) ≤ y := one_le_div_one_sub hβ0 hβ1
  set C : ℝ := (T ℝ (2 * n)).eval y with hC_def
  have hCcast : C = (T ℝ ((2 * n : ℕ) : ℤ)).eval y := by rw [hC_def]; push_cast; ring_nf
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCcast]
    have := Remez.monotoneOn_eval_T (2 * n) (Set.self_mem_Ici) (Set.mem_Ici.2 hy1) hy1
    simpa using this
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  set K : ℝ := |diff F G x₀| with hK_def
  have hK0 : 0 ≤ K := abs_nonneg _
  set S : Set (Pt d) := {x ∈ Ω | K / C ≤ |diff F G x|} with hS_def
  change t * vol Ω ≤ vol S
  have hSΩ : S ⊆ Ω := fun x hx => hx.1
  have hSm : MeasurableSet S := by
    have : S = Ω ∩ {x : Pt d | K / C ≤ |diff F G x|} := rfl
    rw [this]
    exact hΩ.inter (isClosed_le continuous_const (continuous_diff F G).abs).measurableSet
  -- the real polynomial representing `diff F G`
  obtain ⟨Q, hQdeg, hQeval⟩ := exists_realPoly F G hF hG
  -- if the whole of `Ω` works, we are done
  have easy : S = Ω → t * vol Ω ≤ vol S := by
    intro h
    rw [h]
    nlinarith
  rcases eq_or_lt_of_le hK0 with hKzero | hKpos
  · -- `K = 0`: every point of `Ω` belongs to `S`
    refine easy (Set.eq_of_subset_of_subset hSΩ fun x hx => ⟨hx, ?_⟩)
    rw [← hKzero]
    simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: `diff F G` is constant
    refine easy ?_
    have hQ0 : Q.totalDegree = 0 := Nat.le_zero.1 (by simpa using hQdeg)
    have hQC : Q = MvPolynomial.C (Q.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 hQ0
    have hconst : ∀ x : Pt d, diff F G x = Q.coeff 0 := by
      intro x
      rw [← hQeval x, hQC]
      simp
    have hKval : K = |Q.coeff 0| := by rw [hK_def, hconst x₀]
    apply Set.eq_of_subset_of_subset hSΩ
    intro x hx
    refine ⟨hx, ?_⟩
    rw [hconst x, ← hKval]
    exact div_le_self hK0 hC1
  -- the main case: `n ≥ 1` and `K > 0`; argue by contradiction
  by_contra hcon
  push Not at hcon
  set E : Set (Pt d) := Ω \ S with hE_def
  have hEΩ : E ⊆ Ω := Set.diff_subset
  have hEV : E ⊆ V := hEΩ.trans hΩV
  have hEm : MeasurableSet E := hΩ.diff hSm
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hΩfin (measure_mono hEΩ)
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hΩfin (measure_mono hSΩ)
  have hVEfin : volume (V \ E) ≠ ⊤ := ne_top_of_le_ne_top hVfin (measure_mono Set.diff_subset)
  -- `|S| + |E| = |Ω|`
  have hSE : vol S + vol E = vol Ω := by
    have h0 : volume S + volume E = volume Ω := by
      rw [hE_def, ← measure_inter_add_diff Ω hSm, Set.inter_eq_self_of_subset_right hSΩ]
    simp only [vol, measureReal_def]
    rw [← h0, ENNReal.toReal_add hSfin hEfin]
  -- `|V \ E| + |E| = |V|`
  have hVE : vol (V \ E) + vol E = vol V := by
    have h0 : volume (V \ E) + volume E = volume V := by
      rw [add_comm, ← measure_inter_add_diff V hEm, Set.inter_eq_self_of_subset_right hEV]
    simp only [vol, measureReal_def]
    rw [← h0, ENNReal.toReal_add hVEfin hEfin]
  have hEpos : 0 < vol E := by nlinarith
  have hEvolpos : 0 < volume E := (ENNReal.toReal_pos_iff.1 hEpos).1
  have hVne : vol V ≠ 0 := hVpos.ne'
  -- transport to `Fin (2d) → ℝ`
  set V' : Set (Fin (2 * d) → ℝ) := WithLp.ofLp '' V with hV'_def
  set E' : Set (Fin (2 * d) → ℝ) := WithLp.ofLp '' E with hE'_def
  have hV'conv : Convex ℝ V' := convex_ofLp_image hVconv
  have hV'cpt : IsCompact V' := isCompact_ofLp_image hVcpt
  have hE'V' : E' ⊆ V' := Set.image_mono hEV
  have hE'vol : 0 < volume E' := by rw [hE'_def, volume_ofLp_image hEm]; exact hEvolpos
  have hvolE' : (volume E').toReal = vol E := vol_ofLp_image hEm
  have hvolV' : (volume V').toReal = vol V := vol_ofLp_image hVmeas
  have hbound : ∀ z ∈ E', |MvPolynomial.eval z Q| ≤ K / C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hQeval x]
    have hns : ¬ (K / C ≤ |diff F G x|) := fun h => hx.2 ⟨hx.1, h⟩
    linarith [not_le.1 hns]
  have hx₀' : WithLp.ofLp x₀ ∈ V' := ⟨x₀, hx₀, rfl⟩
  have key := Remez.brudnyi_ganzburg (m := 2 * d) (by omega) hV'conv hV'cpt hE'V' hE'vol
    hQdeg hbound hx₀'
  rw [hQeval x₀, ← hK_def] at key
  -- identify the Remez parameter
  have hone_sub : 1 - vol E / vol V = vol (V \ E) / vol V := by
    field_simp
    linarith
  have hlam0 : 0 ≤ vol (V \ E) / vol V := div_nonneg ENNReal.toReal_nonneg hVpos.le
  have hβ' : Remez.beta (2 * d) ((volume E').toReal / (volume V').toReal)
      = (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ)) := by
    rw [hvolE', hvolV']
    simp only [Remez.beta]
    rw [hone_sub]
    push_cast
    ring_nf
  rw [hβ'] at key
  -- `|V \ E| / |V| < θ`
  have hlamθ : vol (V \ E) / vol V < theta Ω t := by
    rw [hθ_eq, div_lt_div_iff₀ hVpos hVpos]
    nlinarith
  have hβ'lt : (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ)) < β :=
    Real.rpow_lt_rpow hlam0 hlamθ hexp
  have hβ'0 : 0 ≤ (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ)) := Real.rpow_nonneg hlam0 _
  have hy'1 : (1 : ℝ) ≤ (1 + (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ))) /
      (1 - (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ))) :=
    one_le_div_one_sub hβ'0 (hβ'lt.trans hβ1)
  have hylt : (1 + (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ))) /
      (1 - (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ))) < y :=
    div_lt_div_of_lt_one hβ'0 hβ'lt hβ1
  have hTlt : (T ℝ ((2 * n : ℕ) : ℤ)).eval
      ((1 + (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ))) /
        (1 - (vol (V \ E) / vol V) ^ (1 / (2 * d : ℝ)))) < C := by
    rw [hCcast]
    exact strictMonoOn_eval_T (k := 2 * n) (by omega) (Set.mem_Ici.2 hy'1)
      (Set.mem_Ici.2 hy1) hylt
  have hKC : 0 < K / C := div_pos hKpos hC0
  have hCK : C * (K / C) = K := by field_simp
  have hfinal := mul_lt_mul_of_pos_right hTlt hKC
  rw [hCK] at hfinal
  linarith

/-- **Superlevel sets are large, exponential form** (paper, p. 3): if `θ ≤ 2^{−4d}` then
`|{z ∈ Ω : |P(z)| ≥ exp(−8 n θ^{1/(4d)}) ‖P‖_{L∞(Ω̂)}}| ≥ t |Ω|`. -/
theorem superlevel_measure_ge {d n : ℕ} (hd : 1 ≤ d) {Ω : Set (Pt d)} (hΩ : MeasurableSet Ω)
    (hb : Bornology.IsBounded Ω) (hpos : 0 < vol Ω)
    {F G : PolyFock.Fock.P d} (hF : F.totalDegree ≤ n) (hG : G.totalDegree ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hθ : theta Ω t ≤ (1 / 2) ^ (4 * d))
    {x₀ : Pt d} (hx₀ : x₀ ∈ hull Ω) (hmax : ∀ x ∈ hull Ω, |diff F G x| ≤ |diff F G x₀|) :
    t * vol Ω ≤ vol {x ∈ Ω |
      Real.exp (-(8 * n * theta Ω t ^ (1 / (4 * d : ℝ)))) * |diff F G x₀| ≤ |diff F G x|} := by
  classical
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  have hexpos : 0 < 1 / (2 * d : ℝ) := by positivity
  have hθ0 : 0 ≤ theta Ω t := by
    refine div_nonneg ?_ ENNReal.toReal_nonneg
    have h1 : (0 : ℝ) ≤ vol Ω := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) ≤ vol (hull Ω \ Ω) := ENNReal.toReal_nonneg
    nlinarith
  -- the Chebyshev form of the estimate
  have key := superlevel_measure_ge_T hd hΩ hb hpos hF hG ht0 ht1 hx₀ hmax
  set β : ℝ := theta Ω t ^ (1 / (2 * d : ℝ)) with hβ_def
  set C : ℝ := (T ℝ (2 * n)).eval ((1 + β) / (1 - β)) with hC_def
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hθ0 _
  -- `β ≤ 1/4`
  have hβ4 : β ≤ 1 / 4 := by
    have h1 : β ≤ ((1 / 2 : ℝ) ^ (4 * d)) ^ (1 / (2 * d : ℝ)) :=
      Real.rpow_le_rpow hθ0 hθ hexpos.le
    refine h1.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast (1 / 2 : ℝ) (4 * d), ← Real.rpow_mul (by norm_num)]
    rw [show ((4 * d : ℕ) : ℝ) * (1 / (2 * d : ℝ)) = ((2 : ℕ) : ℝ) by
      push_cast; field_simp; ring]
    rw [Real.rpow_natCast]
    norm_num
  have hβ1 : β < 1 := by linarith
  have hy1 : (1 : ℝ) ≤ (1 + β) / (1 - β) := one_le_div_one_sub hβ0 hβ1
  have hCcast : C = (T ℝ ((2 * n : ℕ) : ℤ)).eval ((1 + β) / (1 - β)) := by
    rw [hC_def]; push_cast; ring_nf
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCcast]
    have := Remez.monotoneOn_eval_T (2 * n) Set.self_mem_Ici (Set.mem_Ici.2 hy1) hy1
    simpa using this
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  -- `√β = θ^{1/(4d)}`
  have hsq : Real.sqrt β = theta Ω t ^ (1 / (4 * d : ℝ)) := by
    rw [hβ_def, Real.sqrt_eq_rpow, ← Real.rpow_mul hθ0]
    congr 1
    field_simp
    norm_num
  -- `C ≤ exp(8 n θ^{1/(4d)})`
  have hCexp : C ≤ Real.exp (8 * n * theta Ω t ^ (1 / (4 * d : ℝ))) := by
    have h := T_eval_le_exp (2 * n) hβ0 hβ4
    rw [hsq] at h
    rw [hCcast]
    refine h.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  -- comparison of the two thresholds
  have hK0 : (0 : ℝ) ≤ |diff F G x₀| := abs_nonneg _
  have hle : Real.exp (-(8 * n * theta Ω t ^ (1 / (4 * d : ℝ)))) * |diff F G x₀| ≤
      |diff F G x₀| / C := by
    rw [Real.exp_neg, inv_mul_eq_div]
    gcongr
  refine key.trans ?_
  have hfin : volume {x ∈ Ω |
      Real.exp (-(8 * n * theta Ω t ^ (1 / (4 * d : ℝ)))) * |diff F G x₀| ≤
        |diff F G x|} ≠ ⊤ :=
    ne_top_of_le_ne_top hb.measure_lt_top.ne (measure_mono fun x hx => hx.1)
  exact ENNReal.toReal_mono hfin (measure_mono fun x hx => ⟨hx.1, hle.trans hx.2⟩)

end DiscreteNorming
