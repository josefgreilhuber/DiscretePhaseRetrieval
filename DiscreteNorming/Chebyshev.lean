import DiscreteNorming.Defs
import Remez.Multivariate.BrudnyiGanzburgRemez

/-!
# Claim C1: the Remez inequality in exponential form

`T_k(cosh u) = cosh(k u)`; hence `T_k` is strictly increasing on `[1, ∞)` for `k ≥ 1`,
`T_k(y) ≤ (y + √(y² − 1))^k = exp(k · arcosh y)`, and for `0 ≤ β ≤ 1/4`
`T_k((1+β)/(1−β)) ≤ exp(4 k √β)` (since `(1+√β)/(1−√β) ≤ e^{4√β}` for `√β ≤ 1/2`).
Combined with `Remez.brudnyi_ganzburg` (`β = (|V \ E|/|V|)^{1/m}`) this is the form
`‖p‖_V ≤ exp(4 k (|V \ E|/|V|)^{1/(2m)}) ‖p‖_E` for `|V \ E| ≤ 2^{−2m}|V|` quoted in the paper.
-/

open Polynomial Polynomial.Chebyshev MeasureTheory

namespace DiscreteNorming

theorem T_eval_cosh (k : ℕ) (u : ℝ) : (T ℝ k).eval (Real.cosh u) = Real.cosh (k * u) := by
  simp

/-- `T_k(y) = cosh (k · arcosh y)` for `y ≥ 1`. -/
theorem eval_T_eq_cosh_arcosh (k : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    (T ℝ k).eval y = Real.cosh (k * Real.arcosh y) := by
  conv_lhs => rw [← Real.cosh_arcosh hy]
  exact T_eval_cosh k _

/-- `cosh x ≤ exp x` for `x ≥ 0`. -/
theorem cosh_le_exp {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.2 (by linarith)
  linarith

theorem strictMonoOn_eval_T {k : ℕ} (hk : 1 ≤ k) :
    StrictMonoOn (fun y : ℝ ↦ (T ℝ k).eval y) (Set.Ici 1) := by
  intro y hy y' hy' hyy'
  have hy1 : (1 : ℝ) ≤ y := hy
  have hy1' : (1 : ℝ) ≤ y' := hy'
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : Real.arcosh y < Real.arcosh y' :=
    (Real.arcosh_lt_arcosh (by linarith) (by linarith)).2 hyy'
  have ha0 : 0 ≤ Real.arcosh y := Real.arcosh_nonneg hy1
  have ha0' : 0 ≤ Real.arcosh y' := Real.arcosh_nonneg hy1'
  simp only
  rw [eval_T_eq_cosh_arcosh k hy1, eval_T_eq_cosh_arcosh k hy1', Real.cosh_lt_cosh,
    abs_of_nonneg (mul_nonneg hk0.le ha0), abs_of_nonneg (mul_nonneg hk0.le ha0')]
  exact mul_lt_mul_of_pos_left ha hk0

/-- `T_k(y) ≤ (y + √(y² − 1))^k` for `y ≥ 1`. -/
theorem T_eval_le_pow (k : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    (T ℝ k).eval y ≤ (y + Real.sqrt (y ^ 2 - 1)) ^ k := by
  have h0 : 0 ≤ Real.arcosh y := Real.arcosh_nonneg hy
  calc (T ℝ k).eval y = Real.cosh (k * Real.arcosh y) := eval_T_eq_cosh_arcosh k hy
    _ ≤ Real.exp (k * Real.arcosh y) := cosh_le_exp (by positivity)
    _ = Real.exp (Real.arcosh y) ^ k := Real.exp_nat_mul _ k
    _ = (y + Real.sqrt (y ^ 2 - 1)) ^ k := by rw [Real.exp_arcosh hy]

/-- `T_k((1+β)/(1−β)) ≤ exp(4 k √β)` for `0 ≤ β ≤ 1/4`. -/
theorem T_eval_le_exp (k : ℕ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 4) :
    (T ℝ k).eval ((1 + β) / (1 - β)) ≤ Real.exp (4 * k * Real.sqrt β) := by
  obtain ⟨s, hs0, hs2, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 / 2 ∧ β = s ^ 2 := by
    refine ⟨Real.sqrt β, Real.sqrt_nonneg _, ?_, (Real.sq_sqrt hβ0).symm⟩
    have h := Real.sqrt_le_sqrt (show β ≤ (1 / 2 : ℝ) ^ 2 by norm_num; linarith)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)] at h
  rw [Real.sqrt_sq hs0]
  have hs1 : s < 1 := by linarith
  have hden : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hden' : (0 : ℝ) < 1 - s := by linarith
  have hne : (1 - s ^ 2) ≠ 0 := ne_of_gt hden
  have hne' : (1 - s) ≠ 0 := ne_of_gt hden'
  have hy : (1 : ℝ) ≤ (1 + s ^ 2) / (1 - s ^ 2) := by
    rw [le_div_iff₀ hden]; nlinarith
  have hroot : Real.sqrt (((1 + s ^ 2) / (1 - s ^ 2)) ^ 2 - 1) = 2 * s / (1 - s ^ 2) := by
    rw [show ((1 + s ^ 2) / (1 - s ^ 2)) ^ 2 - 1 = (2 * s / (1 - s ^ 2)) ^ 2 by
      field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have hbase : (1 + s ^ 2) / (1 - s ^ 2) + Real.sqrt (((1 + s ^ 2) / (1 - s ^ 2)) ^ 2 - 1)
      = (1 + s) / (1 - s) := by
    rw [hroot]
    field_simp
    ring
  have hexp : (1 + s) / (1 - s) ≤ Real.exp (4 * s) := by
    rw [div_le_iff₀ hden']
    have h := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 4 * s)
    nlinarith [mul_le_mul_of_nonneg_right h hden'.le,
      mul_nonneg (mul_nonneg hs0 hs0) (by linarith : (0 : ℝ) ≤ 1 / 2 - s)]
  calc (T ℝ k).eval ((1 + s ^ 2) / (1 - s ^ 2))
      ≤ ((1 + s ^ 2) / (1 - s ^ 2)
          + Real.sqrt (((1 + s ^ 2) / (1 - s ^ 2)) ^ 2 - 1)) ^ k := T_eval_le_pow k hy
    _ = ((1 + s) / (1 - s)) ^ k := by rw [hbase]
    _ ≤ Real.exp (4 * s) ^ k := pow_le_pow_left₀ (by positivity) hexp k
    _ = Real.exp (4 * k * s) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- **Remez inequality, exponential form** (Ganzburg 2001, (4.1) with `T_k` estimated):
for a compact convex `V ⊆ ℝ^m`, a measurable `E ⊆ V` with `|V \ E| ≤ 2^{−2m} |V|`, and a real
polynomial `p` of degree `≤ k` bounded by `K` on `E`,
`|p(x)| ≤ exp(4 k (|V \ E|/|V|)^{1/(2m)}) K` for all `x ∈ V`. -/
theorem remez_exp {m : ℕ} (hm : 0 < m) {V : Set (Fin m → ℝ)} (hVc : Convex ℝ V)
    (hVcpt : IsCompact V) {E : Set (Fin m → ℝ)} (hE : E ⊆ V) (hEm : MeasurableSet E)
    (hvol : 0 < volume E)
    (hsmall : (volume (V \ E)).toReal ≤ (1 / 2) ^ (2 * m) * (volume V).toReal)
    {p : MvPolynomial (Fin m) ℝ} {k : ℕ} (hp : p.totalDegree ≤ k)
    {K : ℝ} (hpE : ∀ y ∈ E, |MvPolynomial.eval y p| ≤ K) {x : Fin m → ℝ} (hx : x ∈ V) :
    |MvPolynomial.eval x p| ≤
      Real.exp (4 * k * ((volume (V \ E)).toReal / (volume V).toReal) ^ (1 / (2 * m : ℝ))) * K := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hVfin : volume V ≠ ⊤ := hVcpt.isBounded.measure_lt_top.ne
  have hEV : volume E ≤ volume V := measure_mono hE
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hVfin hEV
  have hVpos : 0 < volume V := hvol.trans_le hEV
  have hVr : 0 < (volume V).toReal := ENNReal.toReal_pos hVpos.ne' hVfin
  -- `|V \ E| = |V| − |E|`
  have hdiff : (volume (V \ E)).toReal = (volume V).toReal - (volume E).toReal := by
    rw [measure_diff hE hEm.nullMeasurableSet hEfin, ENNReal.toReal_sub_of_le hEV hVfin]
  set lam := (volume (V \ E)).toReal / (volume V).toReal with hlam_def
  have hlam0 : 0 ≤ lam := by positivity
  -- `1 − |E|/|V| = λ`
  have hlt : 1 - (volume E).toReal / (volume V).toReal = lam := by
    rw [hlam_def, hdiff]; field_simp
  -- `λ ≤ (1/2)^(2m)`
  have hlam_le : lam ≤ (1 / 2 : ℝ) ^ (2 * m) := by
    rw [hlam_def, div_le_iff₀ hVr]
    linarith [hsmall]
  set β := lam ^ (1 / (m : ℝ)) with hβ_def
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hlam0 _
  -- `β ≤ 1/4`
  have hq : ((1 / 2 : ℝ) ^ (2 * m)) ^ (1 / (m : ℝ)) = 1 / 4 := by
    rw [pow_mul, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ 2) m, ← Real.rpow_mul (by norm_num),
      mul_one_div, div_self hm0, Real.rpow_one]
    norm_num
  have hβ4 : β ≤ 1 / 4 := by
    rw [hβ_def, ← hq]
    exact Real.rpow_le_rpow hlam0 hlam_le (by positivity)
  -- `√β = λ^{1/(2m)}`
  have hsqrtβ : Real.sqrt β = lam ^ (1 / (2 * m : ℝ)) := by
    rw [hβ_def, Real.sqrt_eq_rpow, ← Real.rpow_mul hlam0]
    congr 1
    field_simp
  -- the Brudnyi–Ganzburg inequality
  have hbeta : Remez.beta m ((volume E).toReal / (volume V).toReal) = β := by
    rw [Remez.beta, hlt, hβ_def]
  have key := Remez.brudnyi_ganzburg hm hVc hVcpt hE hvol hp hpE hx
  rw [hbeta] at key
  have hK0 : 0 ≤ K :=
    (abs_nonneg _).trans (hpE _ (nonempty_of_measure_ne_zero hvol.ne').some_mem)
  refine key.trans (mul_le_mul_of_nonneg_right ?_ hK0)
  have := T_eval_le_exp k hβ0 hβ4
  rwa [hsqrtβ] at this

end DiscreteNorming
