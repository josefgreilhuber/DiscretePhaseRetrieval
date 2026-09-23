/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.PhiBound
import PolyFock.Rotation
import PolyFock.RadialReduction

/-!
# The tail bound for the reproducing kernel of the true polyanalytic Fock space

Let `K_{L,N}` be the tail of the reproducing kernel of `𝓕^d_L`, whose diagonal is
`PolyFock.tailKernelDiag`.  The main results are

* `PolyFock.tailKernelDiag_radialPoint_le` — the estimate at a radial point `(x,0,…,0)`,
  proved from scratch;
* `PolyFock.tail_bound` — the estimate at an arbitrary `z ∈ ℂ^d`, obtained from the previous
  one and the proved rotation invariance of the diagonal
  (`PolyFock.tailKernelDiag_le_of_radial_bound`);
* `PolyFock.tail_bound_sqrt` — the same in the form
  `‖K_{L,N}(z,·)‖ ≤ C_L (1 - e|z|²/N)^{-1/2} N^{L/2} (e|z|²/N)^{(N-2L)/2}`.

Note that `tailKernelDiag L N z = K_{L,N}(z,z) = ‖K_{L,N}(z,·)‖²_{L²(ℂ^d ; e^{-|·|²})}`, by
the reproducing property; so `tail_bound_sqrt` is exactly the lemma of the paper.
-/

namespace PolyFock

open Finset
open DiscretePR (euclideanDist HermitePoly Φ)
open scoped DiscretePR

noncomputable section

variable {d : ℕ}

/-! ### Evaluation of the basis at a radial point -/

lemma norm_phi_zero_le_one (m n : ℕ) : ‖HermitePoly m n 0‖ ≤ 1 := by
  rw [phi_zero]
  split
  · simp
  · simp

/-- `Φ_{𝐧,𝐪}` vanishes at `(x,0,…,0)` unless `nᵢ = qᵢ` for all `i ≠ 0`. -/
lemma Phi_radialPoint_eq_zero [NeZero d] {n q : Fin d → ℕ} {x : ℝ} {i : Fin d}
    (hi : i ≠ 0) (h : n i ≠ q i) : Φ n q (radialPoint (d := d) x) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [radialPoint_apply, if_neg hi]
  exact phi_zero_of_ne h

/-- At a radial point the norm of `Φ_{𝐧,𝐪}` is controlled by its first factor. -/
lemma norm_Phi_radialPoint_le [NeZero d] (n q : Fin d → ℕ) (x : ℝ) :
    ‖Φ n q (radialPoint (d := d) x)‖ ≤ ‖HermitePoly (n 0) (q 0) (x : ℂ)‖ := by
  rw [Φ, norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin d))]
  rw [radialPoint_apply, if_pos rfl]
  have hrest : ∏ i ∈ Finset.univ.erase (0 : Fin d),
      ‖HermitePoly (n i) (q i) (radialPoint (d := d) x i)‖ ≤ 1 := by
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i hi => ?_
    rw [radialPoint_apply, if_neg (Finset.ne_of_mem_erase hi)]
    exact norm_phi_zero_le_one _ _
  calc ‖HermitePoly (n 0) (q 0) (x : ℂ)‖ *
        ∏ i ∈ Finset.univ.erase (0 : Fin d), ‖HermitePoly (n i) (q i) (radialPoint (d := d) x i)‖
      ≤ ‖HermitePoly (n 0) (q 0) (x : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
    _ = ‖HermitePoly (n 0) (q 0) (x : ℂ)‖ := mul_one _

/-! ### The dominating series -/

/-- The dominating term for the `m`-th layer of the tail. -/
def tailTerm (L N : ℕ) (t : ℝ) (m : ℕ) : ℝ :=
  if N - L + 1 ≤ m then
    (((L : ℝ) + 1) * 2 ^ L) ^ 2 * ((m : ℝ) ^ (2 * L) * t ^ (m - L) / m.factorial)
  else 0

lemma tailTerm_nonneg (L N : ℕ) {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : 0 ≤ tailTerm L N t m := by
  rw [tailTerm]
  split
  · positivity
  · exact le_rfl

/-- On the range of summation, `t ≤ m`. -/
lemma le_cast_of_mem_tail {L N : ℕ} (hN3 : 3 * L ≤ N) {m : ℕ} (hm : N - L + 1 ≤ m) {t : ℝ}
    (ht0 : 0 ≤ t) (hxN : Real.exp 1 * t < N) : t ≤ (m : ℝ) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by simpa using le_exp_nat (n := 1) (by norm_num)
  have hNm : (N : ℝ) + 1 ≤ (m : ℝ) + L := by exact_mod_cast (by omega : N + 1 ≤ m + L)
  have h3L : 3 * (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [mul_nonneg (sub_nonneg.mpr he2) ht0]

/-- Comparison of the dominating term with a geometric series. -/
lemma tailTerm_le_geom {L N : ℕ} (hN3 : 3 * L ≤ N) (hN0 : 0 < N) {t : ℝ} (ht0 : 0 ≤ t)
    (m : ℕ) :
    tailTerm L N t m ≤ (((L : ℝ) + 1) * 2 ^ L) ^ 2 * Real.exp (3 * L) * t ^ L *
      (if N - L + 1 ≤ m then (Real.exp 1 * t / N) ^ (m - 2 * L) else 0) := by
  set θ : ℝ := Real.exp 1 * t / N with hθ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hθ0 : 0 ≤ θ := by positivity
  rw [tailTerm]
  split
  · rename_i hm
    have hm2L : 2 * L < m := by omega
    have hm1 : 1 ≤ m := by omega
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hstep1 := pow_div_factorial_le L m hm1 hm2L.le ht0
    have hsplit : Real.exp 1 * t / (m : ℝ) = ((N : ℝ) / m) * θ := by
      rw [hθ]; field_simp
    have hstep2 : (Real.exp 1 * t / (m : ℝ)) ^ (m - 2 * L) ≤ Real.exp L * θ ^ (m - 2 * L) := by
      rw [hsplit, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_ratio_le L N m hm2L (by omega)) (by positivity)
    have hexp : Real.exp (2 * (L : ℝ)) * Real.exp (L : ℝ) = Real.exp (3 * (L : ℝ)) := by
      rw [← Real.exp_add]; ring_nf
    calc (((L : ℝ) + 1) * 2 ^ L) ^ 2 * ((m : ℝ) ^ (2 * L) * t ^ (m - L) / m.factorial)
        ≤ (((L : ℝ) + 1) * 2 ^ L) ^ 2 *
            (Real.exp (2 * L) * t ^ L * (Real.exp 1 * t / (m : ℝ)) ^ (m - 2 * L)) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ ≤ (((L : ℝ) + 1) * 2 ^ L) ^ 2 *
            (Real.exp (2 * L) * t ^ L * (Real.exp L * θ ^ (m - 2 * L))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ = (((L : ℝ) + 1) * 2 ^ L) ^ 2 * Real.exp (3 * L) * t ^ L * θ ^ (m - 2 * L) := by
          rw [← hexp]; ring
  · simp

lemma summable_tailTerm {L N : ℕ} (hN3 : 3 * L ≤ N) (hN0 : 0 < N) {t : ℝ} (ht0 : 0 ≤ t)
    (hxN : Real.exp 1 * t < N) : Summable (tailTerm L N t) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hθ0 : 0 ≤ Real.exp 1 * t / N := by positivity
  have hθ1 : Real.exp 1 * t / N < 1 := by rw [div_lt_one hNpos]; exact hxN
  have hg := summable_geom_tail (N - L + 1) (2 * L) (by omega) hθ0 hθ1
  refine Summable.of_nonneg_of_le (tailTerm_nonneg L N ht0)
    (tailTerm_le_geom hN3 hN0 ht0) (hg.mul_left _)

lemma tsum_tailTerm_le {L N : ℕ} (hN3 : 3 * L ≤ N) (hN0 : 0 < N) {t : ℝ} (ht0 : 0 ≤ t)
    (hxN : Real.exp 1 * t < N) :
    ∑' m, tailTerm L N t m ≤ (((L : ℝ) + 1) * 2 ^ L) ^ 2 * Real.exp (3 * L) * t ^ L *
      ((Real.exp 1 * t / N) ^ ((N - L + 1) - 2 * L) / (1 - Real.exp 1 * t / N)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hθ0 : 0 ≤ Real.exp 1 * t / N := by positivity
  have hθ1 : Real.exp 1 * t / N < 1 := by rw [div_lt_one hNpos]; exact hxN
  have hg := summable_geom_tail (N - L + 1) (2 * L) (by omega) hθ0 hθ1
  calc ∑' m, tailTerm L N t m
      ≤ ∑' m, (((L : ℝ) + 1) * 2 ^ L) ^ 2 * Real.exp (3 * L) * t ^ L *
          (if N - L + 1 ≤ m then (Real.exp 1 * t / N) ^ (m - 2 * L) else 0) :=
        (summable_tailTerm hN3 hN0 ht0 hxN).tsum_le_tsum
          (tailTerm_le_geom hN3 hN0 ht0) (hg.mul_left _)
    _ = (((L : ℝ) + 1) * 2 ^ L) ^ 2 * Real.exp (3 * L) * t ^ L *
          ∑' m, (if N - L + 1 ≤ m then (Real.exp 1 * t / N) ^ (m - 2 * L) else 0) :=
        tsum_mul_left
    _ = (((L : ℝ) + 1) * 2 ^ L) ^ 2 * Real.exp (3 * L) * t ^ L *
          ((Real.exp 1 * t / N) ^ ((N - L + 1) - 2 * L) / (1 - Real.exp 1 * t / N)) := by
        rw [tsum_geom_tail (N - L + 1) (2 * L) (by omega) hθ0 hθ1]

/-! ### The estimate at a radial point -/

/-- The constant appearing in the tail bound. -/
def tailConst (d L : ℕ) : ℝ :=
  ((Finset.Nat.antidiagonalTuple d L).card : ℝ) * (((L : ℝ) + 1) * 2 ^ L) ^ 2 *
    Real.exp (3 * L)

lemma tailConst_nonneg (d L : ℕ) : 0 ≤ tailConst d L := by
  rw [tailConst]; positivity

/-- Every summand of `tailKernelDiag` at a radial point is dominated by `tailTerm`. -/
lemma diagTerm_le [NeZero d] {L N : ℕ} (hN3 : 3 * L ≤ N) {x : ℝ} (hx : 0 ≤ x)
    (hxN : Real.exp 1 * x ^ 2 < N) (p : (Fin d → ℕ) × (Fin d → ℕ)) :
    (if ‖p.2‖₁ = L ∧ N < ‖p.1‖₁ then
        ‖Φ p.1 p.2 (radialPoint (d := d) x)‖ ^ 2 else 0)
      ≤ (if ‖p.2‖₁ = L ∧ p.1 = Function.update p.2 0 (p.1 0) then
          tailTerm L N (x ^ 2) (p.1 0) else 0) := by
  have ht0 : (0 : ℝ) ≤ x ^ 2 := by positivity
  by_cases hcond : ‖p.2‖₁ = L ∧ N < ‖p.1‖₁
  · rw [if_pos hcond]
    obtain ⟨hq, hn⟩ := hcond
    by_cases hupd : ∀ i, i ≠ 0 → p.1 i = p.2 i
    · -- the surviving case
      have hupd' : p.1 = Function.update p.2 0 (p.1 0) := by
        funext i
        by_cases hi : i = 0
        · subst hi; simp
        · rw [Function.update_of_ne hi, hupd i hi]
      rw [if_pos ⟨hq, hupd'⟩]
      -- degree bookkeeping (the two sizes are unfolded once, so that `omega` sees the sums)
      simp only [DiscretePR.size] at hq hn
      have hsum1 : ∑ i, p.1 i = p.1 0 + ∑ i ∈ Finset.univ.erase (0 : Fin d), p.1 i :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin d))).symm
      have hsum2 : ∑ i, p.2 i = p.2 0 + ∑ i ∈ Finset.univ.erase (0 : Fin d), p.2 i :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin d))).symm
      have hrest : ∑ i ∈ Finset.univ.erase (0 : Fin d), p.1 i
          = ∑ i ∈ Finset.univ.erase (0 : Fin d), p.2 i :=
        Finset.sum_congr rfl fun i hi => hupd i (Finset.ne_of_mem_erase hi)
      have hq0 : p.2 0 ≤ L := by omega
      have hm : N - L + 1 ≤ p.1 0 := by omega
      have hm2L : 2 * L < p.1 0 := by omega
      have hmt : x ^ 2 ≤ (p.1 0 : ℝ) := le_cast_of_mem_tail hN3 hm ht0 hxN
      have hnormx : ‖(x : ℂ)‖ = x := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      have hbase : ‖Φ p.1 p.2 (radialPoint (d := d) x)‖ ^ 2
          ≤ ‖HermitePoly (p.1 0) (p.2 0) (x : ℂ)‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_Phi_radialPoint_le _ _ _) 2
      refine hbase.trans ?_
      have := sq_norm_phi_le L (p.1 0) (p.2 0) hq0 (by omega) (by omega) (x : ℂ)
        (by rw [hnormx]; exact hmt)
      rw [tailTerm, if_pos hm]
      rw [hnormx] at this
      exact this
    · -- some coordinate `i ≠ 0` has `nᵢ ≠ qᵢ`, so `Φ` vanishes
      simp only [not_forall] at hupd
      obtain ⟨i, hi, hne⟩ := hupd
      rw [Phi_radialPoint_eq_zero hi hne]
      simp only [norm_zero]
      have : (0 : ℝ) ≤ if ‖p.2‖₁ = L ∧ p.1 = Function.update p.2 0 (p.1 0) then
          tailTerm L N (x ^ 2) (p.1 0) else 0 := by
        split
        · exact tailTerm_nonneg L N ht0 _
        · exact le_rfl
      simpa using this
  · rw [if_neg hcond]
    split
    · exact tailTerm_nonneg L N ht0 _
    · exact le_rfl

/-- A uniform bound on every finite partial sum of the tail at a radial point. -/
lemma tailDiag_finset_le [NeZero d] {L N : ℕ} (hN3 : 3 * L ≤ N) (hN0 : 0 < N)
    {x : ℝ} (hx : 0 ≤ x) (hxN : Real.exp 1 * x ^ 2 < N)
    (S : Finset ((Fin d → ℕ) × (Fin d → ℕ))) :
    ∑ p ∈ S, (if ‖p.2‖₁ = L ∧ N < ‖p.1‖₁ then
        ‖Φ p.1 p.2 (radialPoint (d := d) x)‖ ^ 2 else 0)
      ≤ ((Finset.Nat.antidiagonalTuple d L).card : ℝ) * ∑' m, tailTerm L N (x ^ 2) m := by
  classical
  have ht0 : (0 : ℝ) ≤ x ^ 2 := by positivity
  have hBsummable := summable_tailTerm (L := L) (N := N) hN3 hN0 ht0 hxN
  set P : (Fin d → ℕ) × (Fin d → ℕ) → Prop :=
    fun p => ‖p.2‖₁ = L ∧ p.1 = Function.update p.2 0 (p.1 0) with hP
  set f : (Fin d → ℕ) × (Fin d → ℕ) → (Fin d → ℕ) × ℕ := fun p => (p.2, p.1 0) with hf
  have hstep1 : ∑ p ∈ S, (if ‖p.2‖₁ = L ∧ N < ‖p.1‖₁ then
      ‖Φ p.1 p.2 (radialPoint (d := d) x)‖ ^ 2 else 0)
      ≤ ∑ p ∈ S, (if P p then tailTerm L N (x ^ 2) (p.1 0) else 0) :=
    Finset.sum_le_sum fun p _ => diagTerm_le hN3 hx hxN p
  refine hstep1.trans ?_
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn f ↑(S.filter P) := by
    intro p hp p' hp' hfe
    rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
    have h2 : p.2 = p'.2 := congrArg Prod.fst hfe
    have h1 : p.1 0 = p'.1 0 := congrArg Prod.snd hfe
    refine Prod.ext ?_ h2
    rw [hp.2.2, hp'.2.2, h1, h2]
  rw [← Finset.sum_image (f := fun y : (Fin d → ℕ) × ℕ => tailTerm L N (x ^ 2) y.2) hinj]
  set M : Finset ℕ := ((S.filter P).image f).image Prod.snd with hM
  have hsub : (S.filter P).image f ⊆ (Finset.Nat.antidiagonalTuple d L) ×ˢ M := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_product]
    refine ⟨Finset.Nat.mem_antidiagonalTuple.mpr hp.2.1, ?_⟩
    rw [hM]
    exact Finset.mem_image_of_mem Prod.snd (Finset.mem_image_of_mem f
      (Finset.mem_filter.mpr hp))
  calc ∑ y ∈ (S.filter P).image f, tailTerm L N (x ^ 2) y.2
      ≤ ∑ y ∈ (Finset.Nat.antidiagonalTuple d L) ×ˢ M, tailTerm L N (x ^ 2) y.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun y _ _ => tailTerm_nonneg L N ht0 _)
    _ = ((Finset.Nat.antidiagonalTuple d L).card : ℝ) * ∑ m ∈ M, tailTerm L N (x ^ 2) m := by
        rw [Finset.sum_product]
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Finset.Nat.antidiagonalTuple d L).card : ℝ) * ∑' m, tailTerm L N (x ^ 2) m := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hBsummable.sum_le_tsum M (fun m _ => tailTerm_nonneg L N ht0 m)

/-- The dominating series is bounded by the closed-form expression of the lemma. -/
lemma card_mul_tsum_tailTerm_le {L N : ℕ} (hN3 : 3 * L ≤ N) (hN0 : 0 < N)
    {x : ℝ} (_hx : 0 ≤ x) (hxN : Real.exp 1 * x ^ 2 < N) :
    ((Finset.Nat.antidiagonalTuple d L).card : ℝ) * ∑' m, tailTerm L N (x ^ 2) m ≤
      tailConst d L * (N : ℝ) ^ L * (Real.exp 1 * x ^ 2 / N) ^ (N - 2 * L) /
        (1 - Real.exp 1 * x ^ 2 / N) := by
  classical
  have ht0 : (0 : ℝ) ≤ x ^ 2 := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  set θ : ℝ := Real.exp 1 * x ^ 2 / N with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by rw [hθdef, div_lt_one hNpos]; exact hxN
  have hgeom := tsum_tailTerm_le (L := L) (N := N) hN3 hN0 ht0 hxN
  have hcard : (0 : ℝ) ≤ ((Finset.Nat.antidiagonalTuple d L).card : ℝ) := by positivity
  refine (mul_le_mul_of_nonneg_left hgeom hcard).trans ?_
  -- Step 4: rewrite `t^L` in terms of `θ` and collect powers.
  have htL : (x ^ 2) ^ L ≤ (N : ℝ) ^ L * θ ^ L := by
    have hxt : x ^ 2 = (N : ℝ) / Real.exp 1 * θ := by
      rw [hθdef]
      have hne : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
      field_simp
    have hNe : (N : ℝ) / Real.exp 1 ≤ (N : ℝ) := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      exact le_mul_of_one_le_right (Nat.cast_nonneg N) (Real.one_le_exp zero_le_one)
    calc (x ^ 2) ^ L = ((N : ℝ) / Real.exp 1) ^ L * θ ^ L := by rw [hxt, mul_pow]
      _ ≤ (N : ℝ) ^ L * θ ^ L :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hNe L) (by positivity)
  have hpow : θ ^ L * θ ^ ((N - L + 1) - 2 * L) = θ ^ (N + 1 - 2 * L) := by
    rw [← pow_add]; congr 1; omega
  have hmono : θ ^ (N + 1 - 2 * L) ≤ θ ^ (N - 2 * L) :=
    pow_le_pow_of_le_one hθ0 hθ1.le (by omega)
  have hden : 0 < 1 - θ := by linarith
  rw [div_eq_mul_inv, tailConst]
  calc ((Finset.Nat.antidiagonalTuple d L).card : ℝ) *
        ((((L : ℝ) + 1) * 2 ^ L) ^ 2 * Real.exp (3 * L) * (x ^ 2) ^ L *
          (θ ^ ((N - L + 1) - 2 * L) / (1 - θ)))
      ≤ ((Finset.Nat.antidiagonalTuple d L).card : ℝ) *
        ((((L : ℝ) + 1) * 2 ^ L) ^ 2 * Real.exp (3 * L) * ((N : ℝ) ^ L * θ ^ L) *
          (θ ^ ((N - L + 1) - 2 * L) / (1 - θ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hcard
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left htL (by positivity)
    _ = ((Finset.Nat.antidiagonalTuple d L).card : ℝ) * (((L : ℝ) + 1) * 2 ^ L) ^ 2 *
          Real.exp (3 * L) * (N : ℝ) ^ L * θ ^ (N + 1 - 2 * L) * (1 - θ)⁻¹ := by
        rw [← hpow]; field_simp
    _ ≤ ((Finset.Nat.antidiagonalTuple d L).card : ℝ) * (((L : ℝ) + 1) * 2 ^ L) ^ 2 *
          Real.exp (3 * L) * (N : ℝ) ^ L * θ ^ (N - 2 * L) * (1 - θ)⁻¹ := by
        gcongr

/-- **The tail bound at a radial point.** -/
theorem tailKernelDiag_radialPoint_le [NeZero d] {L N : ℕ} (hN3 : 3 * L ≤ N) (hN0 : 0 < N)
    {x : ℝ} (hx : 0 ≤ x) (hxN : Real.exp 1 * x ^ 2 < N) :
    tailKernelDiag L N (radialPoint (d := d) x) ≤
      tailConst d L * (N : ℝ) ^ L * (Real.exp 1 * x ^ 2 / N) ^ (N - 2 * L) /
        (1 - Real.exp 1 * x ^ 2 / N) :=
  (Real.tsum_le_of_sum_le (fun p => diagTerm_nonneg L N _ p)
      (fun S => tailDiag_finset_le (d := d) hN3 hN0 hx hxN S)).trans
    (card_mul_tsum_tailTerm_le hN3 hN0 hx hxN)

/-! ### The tail bound at an arbitrary point -/

/-- **The tail bound.**  If `N ≥ max (L+9) (3L)` and `e |z|² < N`, then

`K_{L,N}(z,z) ≤ C_{d,L} · N^L · (e|z|²/N)^{N-2L} / (1 - e|z|²/N)`.

Since `K_{L,N}(z,z) = ‖K_{L,N}(z,·)‖²_{L²(ℂ^d; e^{-|·|²})}`, this is the squared form of the
lemma.  It is proved from the definitions alone. -/
theorem tail_bound [NeZero d] {L N : ℕ} (hN3 : 3 * L ≤ N) (hN9 : L + 9 ≤ N)
    (z : Fin d → ℂ) (hz : Real.exp 1 * euclideanDist z 0 ^ 2 < N) :
    tailKernelDiag L N z ≤
      tailConst d L * (N : ℝ) ^ L * (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * L) /
        (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N) := by
  have hN0 : 0 < N := by omega
  refine (tailKernelDiag_le_of_radial_bound L N z _
    (fun S => tailDiag_finset_le (d := d) hN3 hN0
      (DiscretePR.euclideanDist_zero_nonneg z) hz S)).trans ?_
  exact card_mul_tsum_tailTerm_le hN3 hN0 (DiscretePR.euclideanDist_zero_nonneg z) hz

/-- **The tail bound, in the form of the lemma.**

`‖K_{L,N}(z,·)‖ ≤ (C_{d,L})^{1/2} (1 - e|z|²/N)^{-1/2} N^{L/2} (e|z|²/N)^{(N-2L)/2}`,

where `‖K_{L,N}(z,·)‖ = (K_{L,N}(z,z))^{1/2}` by the reproducing property. -/
theorem tail_bound_sqrt [NeZero d] {L N : ℕ} (hN3 : 3 * L ≤ N) (hN9 : L + 9 ≤ N)
    (z : Fin d → ℂ) (hz : Real.exp 1 * euclideanDist z 0 ^ 2 < N) :
    Real.sqrt (tailKernelDiag L N z) ≤
      Real.sqrt (tailConst d L) * Real.sqrt (1 - Real.exp 1 * euclideanDist z 0 ^ 2 / N)⁻¹ *
        Real.sqrt ((N : ℝ) ^ L) *
        Real.sqrt ((Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * L)) := by
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hθ0 : 0 ≤ Real.exp 1 * euclideanDist z 0 ^ 2 / N := by positivity
  have hθ1 : Real.exp 1 * euclideanDist z 0 ^ 2 / N < 1 := by rw [div_lt_one hNpos]; exact hz
  have hmain := tail_bound hN3 hN9 z hz
  refine (Real.sqrt_le_sqrt hmain).trans_eq ?_
  have hC : (0 : ℝ) ≤ tailConst d L := tailConst_nonneg d L
  have hA : (0 : ℝ) ≤ tailConst d L * (N : ℝ) ^ L := mul_nonneg hC (by positivity)
  have hB : (0 : ℝ) ≤ tailConst d L * (N : ℝ) ^ L *
      (Real.exp 1 * euclideanDist z 0 ^ 2 / N) ^ (N - 2 * L) := mul_nonneg hA (by positivity)
  rw [div_eq_mul_inv, Real.sqrt_mul hB, Real.sqrt_mul hA, Real.sqrt_mul hC]
  ring

end

end PolyFock
