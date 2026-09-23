/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.BoundedComponents.Main

/-! # Sign patterns: Counting

Pure bookkeeping.  Given a family `q : Fin m → MvPolynomial (Fin n) ℝ` of degree `≤ D` and a set
`S` of nowhere-zero sign patterns, suppose every pattern `σ ∈ S` that is not identically `1` is
"charged" to a bounded component `C` of the joint zero set of a nonempty subfamily `(q j)_{j ∈ J}`
with `|J| ≤ n`, in such a way that `σ` is determined outside `J` by the signs of the `q k` on `C`.
Then
`|S| ≤ ∑_{l ≤ n} C(m, l) · 2^l · (2D)^n`  (`card_le_of_charge`).

The `(2D)^n` factor comes from `BoundedComponents.bounded_components` applied to the
reindexed subfamily; the `2^l` factor bounds the number of patterns charged to the same component
(they can differ only on `J`); the binomial coefficient counts the subfamilies.
-/

namespace SignPatterns

open MvPolynomial Finset

variable {n m : ℕ}

/-- The joint zero set of the subfamily `(q j)_{j ∈ J}`. -/
def zeroSetOn (q : Fin m → MvPolynomial (Fin n) ℝ) (J : Finset (Fin m)) : Set (Fin n → ℝ) :=
  {y | ∀ j ∈ J, eval y (q j) = 0}

/-- The subfamily `(q j)_{j ∈ J}` reindexed by `Fin J.card`. -/
noncomputable def subfamily (q : Fin m → MvPolynomial (Fin n) ℝ) (J : Finset (Fin m)) :
    Fin J.card → MvPolynomial (Fin n) ℝ :=
  fun i => q (J.equivFin.symm i)

/-- (a) Reindexing: vanishing of the reindexed subfamily at a point. -/
theorem forall_subfamily_eval_eq_zero (q : Fin m → MvPolynomial (Fin n) ℝ) (J : Finset (Fin m))
    (x : Fin n → ℝ) :
    (∀ i, eval x (subfamily q J i) = 0) ↔ ∀ j ∈ J, eval x (q j) = 0 := by
  constructor
  · intro h j hj
    have := h (J.equivFin ⟨j, hj⟩)
    simpa [subfamily] using this
  · intro h i
    exact h _ (J.equivFin.symm i).2

/-- (a) Reindexing: the zero set of the reindexed subfamily is `zeroSetOn q J`. -/
theorem zeroSet_subfamily (q : Fin m → MvPolynomial (Fin n) ℝ) (J : Finset (Fin m)) :
    {y | ∀ i, eval y (subfamily q J i) = 0} = zeroSetOn q J := by
  ext y
  exact forall_subfamily_eval_eq_zero q J y

/-- The bounded components of the joint zero set of the subfamily `(q j)_{j ∈ J}`. -/
def boundedComponentsOn (q : Fin m → MvPolynomial (Fin n) ℝ) (J : Finset (Fin m)) :
    Set (Set (Fin n → ℝ)) :=
  {C | ∃ x, (∀ j ∈ J, eval x (q j) = 0) ∧ C = connectedComponentIn (zeroSetOn q J) x ∧
    Bornology.IsBounded C}

/-- (b) The `(2D)^n` bound for the bounded components of a subfamily. -/
theorem finite_and_ncard_boundedComponentsOn_le (q : Fin m → MvPolynomial (Fin n) ℝ) (D : ℕ)
    (hD : 1 ≤ D) (hdeg : ∀ j, (q j).totalDegree ≤ D) (J : Finset (Fin m)) :
    (boundedComponentsOn q J).Finite ∧ (boundedComponentsOn q J).ncard ≤ (2 * D) ^ n := by
  have h := BoundedComponents.bounded_components (subfamily q J) D hD
    (fun i => hdeg _)
  have hz : BoundedComponents.zeroSet (subfamily q J) = zeroSetOn q J := zeroSet_subfamily q J
  have heq : boundedComponentsOn q J = BoundedComponents.boundedComponents (subfamily q J) := by
    ext C
    simp only [boundedComponentsOn, BoundedComponents.boundedComponents, Set.mem_setOf_eq, hz,
      forall_subfamily_eval_eq_zero]
  rw [heq]
  exact h

/-- What the charging hypothesis provides for a pattern `σ`: a subfamily `J` and a base point
`x₀` of a bounded component of `zeroSetOn q J` on which the signs of the `q k`, `k ∉ J`, agree
with `σ`. -/
def IsCharge (q : Fin m → MvPolynomial (Fin n) ℝ) (σ : Fin m → SignType) (J : Finset (Fin m))
    (x₀ : Fin n → ℝ) : Prop :=
  J.Nonempty ∧ J.card ≤ n ∧ (∀ j ∈ J, eval x₀ (q j) = 0) ∧
    Bornology.IsBounded (connectedComponentIn (zeroSetOn q J) x₀) ∧
    ∀ c ∈ connectedComponentIn (zeroSetOn q J) x₀, ∀ k ∉ J, SignType.sign (eval c (q k)) = σ k

theorem SignType.eq_one_of_ne_zero_of_ne_neg_one {s : SignType} (h0 : s ≠ 0) (h1 : s ≠ -1) :
    s = 1 := by
  revert h0 h1
  cases s <;> decide

theorem SignType.mem_pair_of_ne_zero {s : SignType} (h0 : s ≠ 0) :
    s ∈ ({1, -1} : Finset SignType) := by
  revert h0
  cases s <;> decide

/-- (c) Fiber injectivity: two patterns charged to the same component of `zeroSetOn q J` agree
outside `J`, so restriction to `J` is injective on the fiber. -/
theorem injOn_restrict_of_isCharge (q : Fin m → MvPolynomial (Fin n) ℝ) (J : Finset (Fin m))
    (T : Finset (Fin m → SignType)) (x : (Fin m → SignType) → (Fin n → ℝ))
    (hx : ∀ σ ∈ T, IsCharge q σ J (x σ)) (C : Set (Fin n → ℝ)) :
    Set.InjOn (fun σ : Fin m → SignType => fun j : J => σ j)
      (T.filter (fun σ => connectedComponentIn (zeroSetOn q J) (x σ) = C)) := by
  intro σ hσ σ' hσ' hEq
  have hσ := Finset.mem_filter.1 hσ
  have hσ' := Finset.mem_filter.1 hσ'
  funext k
  by_cases hk : k ∈ J
  · exact congrFun hEq ⟨k, hk⟩
  · have hc : x σ ∈ connectedComponentIn (zeroSetOn q J) (x σ) :=
      mem_connectedComponentIn (hx σ hσ.1).2.2.1
    have e1 := (hx σ hσ.1).2.2.2.2 (x σ) hc k hk
    have hc' : x σ ∈ connectedComponentIn (zeroSetOn q J) (x σ') := by
      rw [hσ'.2, ← hσ.2]; exact hc
    have e2 := (hx σ' hσ'.1).2.2.2.2 (x σ) hc' k hk
    rw [← e1, ← e2]

/-- The nowhere-zero functions `J → SignType` number at most `2 ^ J.card`. -/
theorem card_le_two_pow_of_forall_ne_zero (J : Finset (Fin m)) (U : Finset (J → SignType))
    (hU : ∀ τ ∈ U, ∀ j, τ j ≠ 0) : U.card ≤ 2 ^ J.card := by
  classical
  calc U.card ≤ (Fintype.piFinset fun _ : J => ({1, -1} : Finset SignType)).card := by
        apply Finset.card_le_card
        intro τ hτ
        rw [Fintype.mem_piFinset]
        intro j
        exact SignType.mem_pair_of_ne_zero (hU τ hτ j)
    _ = 2 ^ J.card := by
        rw [Fintype.card_piFinset]
        have h2 : ({1, -1} : Finset SignType).card = 2 := Finset.card_pair (by decide)
        simp [h2]

/-- (d) The number of patterns charged to subfamily `J` is at most `2 ^ J.card * (2D)^n`. -/
theorem card_le_of_isCharge (q : Fin m → MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ j, (q j).totalDegree ≤ D) (J : Finset (Fin m))
    (T : Finset (Fin m → SignType)) (hT0 : ∀ σ ∈ T, ∀ j, σ j ≠ 0)
    (x : (Fin m → SignType) → (Fin n → ℝ)) (hx : ∀ σ ∈ T, IsCharge q σ J (x σ)) :
    T.card ≤ 2 ^ J.card * (2 * D) ^ n := by
  classical
  let f : (Fin m → SignType) → Set (Fin n → ℝ) :=
    fun σ => connectedComponentIn (zeroSetOn q J) (x σ)
  have h1 : T.card ≤ 2 ^ J.card * (T.image f).card := by
    apply Finset.card_le_mul_card_image
    intro C _
    have hinj := injOn_restrict_of_isCharge q J T x hx C
    rw [← Finset.card_image_of_injOn hinj]
    apply card_le_two_pow_of_forall_ne_zero
    intro τ hτ
    rw [Finset.mem_image] at hτ
    obtain ⟨σ, hσ, rfl⟩ := hτ
    intro j
    exact hT0 σ (Finset.mem_filter.1 hσ).1 j
  have h2 : (T.image f).card ≤ (2 * D) ^ n := by
    rw [← Set.ncard_coe_finset]
    have hB := finite_and_ncard_boundedComponentsOn_le q D hD hdeg J
    refine (Set.ncard_le_ncard ?_ hB.1).trans hB.2
    intro C hC
    rw [Finset.mem_coe, Finset.mem_image] at hC
    obtain ⟨σ, hσ, rfl⟩ := hC
    exact ⟨x σ, (hx σ hσ).2.2.1, rfl, (hx σ hσ).2.2.2.1⟩
  exact h1.trans (Nat.mul_le_mul_left _ h2)

/-- (e) The final regrouping of the sum over subfamilies by cardinality. -/
theorem sum_two_pow_mul_le (n m A : ℕ) (hA : 1 ≤ A) :
    (∑ J ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.Nonempty ∧ J.card ≤ n),
        2 ^ J.card * A) + 1 ≤
      ∑ l ∈ Finset.range (n + 1), Nat.choose m l * 2 ^ l * A := by
  classical
  set Jset : Finset (Finset (Fin m)) :=
    (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.Nonempty ∧ J.card ≤ n) with hJset
  have hmaps : ∀ J ∈ Jset, J.card ∈ Finset.range (n + 1) := by
    intro J hJ
    rw [hJset, Finset.mem_filter] at hJ
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hJ.2.2)
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun l => 2 ^ l * A)]
  have hcnt : ∀ l, (Jset.filter (fun J => J.card = l)).card ≤ Nat.choose m l := by
    intro l
    have : Nat.choose m l = (Finset.powersetCard l (Finset.univ : Finset (Fin m))).card := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [this]
    apply Finset.card_le_card
    intro J hJ
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_filter.1 hJ).2⟩
  have hcnt0 : (Jset.filter (fun J => J.card = 0)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro J hJ
    rw [hJset, Finset.mem_filter] at hJ
    exact (Finset.card_pos.2 hJ.2.1).ne'
  simp only [Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_range_succ', Finset.sum_range_succ', hcnt0, Nat.choose_zero_right]
  simp only [zero_mul, add_zero, pow_zero, one_mul, mul_one]
  apply Nat.add_le_add _ hA
  apply Finset.sum_le_sum
  intro l _
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (hcnt (l + 1))

/-- **Counting sign patterns.**  If every pattern in `S` with some `-1` entry is charged to a
bounded component of the zero set of a nonempty subfamily of size `≤ n`, on which the pattern is
determined outside the subfamily, then `|S| ≤ ∑_{l ≤ n} C(m, l) 2^l (2D)^n`. -/
theorem card_le_of_charge (q : Fin m → MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hdeg : ∀ j, (q j).totalDegree ≤ D)
    (S : Set (Fin m → SignType)) (hS : ∀ σ ∈ S, ∀ j, σ j ≠ 0)
    (charge : ∀ σ ∈ S, (∃ j, σ j = -1) →
      ∃ (J : Finset (Fin m)) (x₀ : Fin n → ℝ),
        J.Nonempty ∧ J.card ≤ n ∧ (∀ j ∈ J, MvPolynomial.eval x₀ (q j) = 0) ∧
        Bornology.IsBounded (connectedComponentIn {y | ∀ j ∈ J, MvPolynomial.eval y (q j) = 0} x₀) ∧
        ∀ c ∈ connectedComponentIn {y | ∀ j ∈ J, MvPolynomial.eval y (q j) = 0} x₀,
          ∀ k ∉ J, SignType.sign (MvPolynomial.eval c (q k)) = σ k) :
    S.ncard ≤ ∑ l ∈ Finset.range (n + 1), Nat.choose m l * 2 ^ l * (2 * D) ^ n := by
  classical
  -- make the charge a function
  have hch : ∀ σ : Fin m → SignType, ∃ (J : Finset (Fin m)) (x₀ : Fin n → ℝ),
      σ ∈ S → (∃ j, σ j = -1) → IsCharge q σ J x₀ := by
    intro σ
    by_cases h : σ ∈ S ∧ ∃ j, σ j = -1
    · obtain ⟨J, x₀, hJ⟩ := charge σ h.1 h.2
      exact ⟨J, x₀, fun _ _ => hJ⟩
    · exact ⟨∅, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose chJ chx hch using hch
  rw [Set.ncard_eq_toFinset_card']
  set T := S.toFinset with hT
  have hmemT : ∀ σ, σ ∈ T ↔ σ ∈ S := fun σ => Set.mem_toFinset
  set Jset : Finset (Finset (Fin m)) :=
    (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.Nonempty ∧ J.card ≤ n) with hJset
  set Sneg := T.filter (fun σ => ∃ j, σ j = -1) with hSneg
  set Spos := T.filter (fun σ => ¬ ∃ j, σ j = -1) with hSpos
  have hsplit : T.card = Sneg.card + Spos.card :=
    (Finset.card_filter_add_card_filter_not _).symm
  -- the all-ones part
  have hpos : Spos.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro σ σ' hσ hσ'
    rw [hSpos, Finset.mem_filter] at hσ hσ'
    funext j
    have h1 : σ j = 1 := SignType.eq_one_of_ne_zero_of_ne_neg_one
      (hS σ ((hmemT σ).1 hσ.1) j) (fun h => hσ.2 ⟨j, h⟩)
    have h2 : σ' j = 1 := SignType.eq_one_of_ne_zero_of_ne_neg_one
      (hS σ' ((hmemT σ').1 hσ'.1) j) (fun h => hσ'.2 ⟨j, h⟩)
    rw [h1, h2]
  -- the charged part, fiberwise over the chosen subfamily
  have hneg : Sneg.card = ∑ J ∈ Jset, (Sneg.filter (fun σ => chJ σ = J)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro σ hσ
    rw [Finset.mem_coe, hSneg, Finset.mem_filter] at hσ
    have := hch σ ((hmemT σ).1 hσ.1) hσ.2
    rw [Finset.mem_coe, hJset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, this.1, this.2.1⟩
  have hfib : ∀ J ∈ Jset,
      (Sneg.filter (fun σ => chJ σ = J)).card ≤ 2 ^ J.card * (2 * D) ^ n := by
    intro J _
    refine card_le_of_isCharge q D hD hdeg J _ ?_ chx ?_
    · intro σ hσ
      exact hS σ ((hmemT σ).1 (Finset.mem_filter.1 (Finset.mem_filter.1 hσ).1).1)
    · intro σ hσ
      obtain ⟨hσ1, hσ2⟩ := Finset.mem_filter.1 hσ
      obtain ⟨hσ3, hσ4⟩ := Finset.mem_filter.1 hσ1
      have := hch σ ((hmemT σ).1 hσ3) hσ4
      rwa [hσ2] at this
  -- combine
  calc T.card = Sneg.card + Spos.card := hsplit
    _ ≤ (∑ J ∈ Jset, 2 ^ J.card * (2 * D) ^ n) + 1 := by
        rw [hneg]; exact Nat.add_le_add (Finset.sum_le_sum hfib) hpos
    _ ≤ ∑ l ∈ Finset.range (n + 1), Nat.choose m l * 2 ^ l * (2 * D) ^ n :=
        sum_two_pow_mul_le n m ((2 * D) ^ n)
          (Nat.one_le_pow _ _ (by omega))

end SignPatterns
