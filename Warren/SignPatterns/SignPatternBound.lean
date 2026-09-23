/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.SignPatterns.Perturb
import Warren.SignPatterns.Counting
import Warren.SignPatterns.Charge
import DiscretePhaseRetrieval.Auxiliary

/-!
# Sign patterns: the Warren bound

Assembling the three previous files we obtain a Warren-type bound on the number of *strict*
sign patterns realised by a family `p 1, ..., p m` of real polynomials in `n` variables of
total degree `≤ d`:

`|{σ ∈ {±1}^m : σ is realised}| ≤ ∑_{l ≤ n} C(m + 1, l) · 2^l · (2D)^n`, where `D = max 2 d`.

The route is *augmentation* rather than degree enlargement: instead of raising the degree of
the whole family to an even number, we adjoin a single auxiliary quadric `q 0 = |x|² − M²`
whose sublevel set `{q 0 ≤ 0}` is a (bounded) ball containing all the witness points, and
perturb the resulting family of `m + 1` polynomials into general position
(`SignPatterns.exists_generic_augmentation`).  Consequently the number of polynomials goes up
by one (`m ↦ m + 1`), while the degree bound is only `D = max 2 d`; no degree is enlarged.

The proof is: augment and perturb `p` to a generic family `q` of `m + 1` polynomials of total
degree `≤ max 2 d` with `{q 0 ≤ 0}` bounded, keeping the signs at one witness point per
realised pattern and making `q 0` negative there
(`SignPatterns.exists_generic_augmentation`); every strict pattern `σ` of `p` thus lifts to the
strict pattern `Fin.cons (-1) σ` of `q`, which is charged to a bounded connected component of
the zero set of a small subfamily of `q` (`SignPatterns.exists_charge`, applied with the
distinguished index `0` providing the required bounded sublevel set); and those components are
counted (`SignPatterns.card_le_of_charge`).
-/

open MvPolynomial

namespace SignPatterns

/-- The set of strict sign patterns realized by `p₁, …, pₘ` on `ℝⁿ`. -/
def strictSignPatterns {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) : Set (Fin m → SignType) :=
  {σ | (∀ j, σ j ≠ 0) ∧ ∃ x, ∀ j, SignType.sign (MvPolynomial.eval x (p j)) = σ j}

theorem mem_strictSignPatterns {n m : ℕ} {p : Fin m → MvPolynomial (Fin n) ℝ}
    {σ : Fin m → SignType} :
    σ ∈ strictSignPatterns p ↔
      (∀ j, σ j ≠ 0) ∧ ∃ x, ∀ j, SignType.sign (MvPolynomial.eval x (p j)) = σ j := Iff.rfl

/-- **Warren-type bound on strict sign patterns** (augmentation route: one auxiliary quadric
`|x|² − M²` is added to the list, so `m ↦ m + 1` and the degree bound is `max 2 d`).

If `p₁, …, pₘ` are real polynomials in `n` variables of total degree `≤ d`, then the number of
sign patterns in `{±1}^m` realised by `p` is at most
`∑_{l ≤ n} C(m + 1, l) · 2^l · (2 · max 2 d)^n`. -/
theorem sign_patterns {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hdeg : ∀ j, (p j).totalDegree ≤ d) :
    (strictSignPatterns p).ncard ≤
      ∑ l ∈ Finset.range (n + 1), Nat.choose (m + 1) l * 2 ^ l * (2 * max 2 d) ^ n := by
  classical
  have hD1 : 1 ≤ max 2 d := le_trans (by norm_num) (le_max_left 2 d)
  have hS : ∀ σ ∈ strictSignPatterns p, ∀ j, σ j ≠ 0 := fun _ hσ => hσ.1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `ℝ^0` is a single point, so at most one pattern is realised.
    have hsub : strictSignPatterns p ⊆
        {fun j => SignType.sign (MvPolynomial.eval (0 : Fin 0 → ℝ) (p j))} := by
      rintro σ ⟨-, x, hx⟩
      have hx0 : x = 0 := funext fun i => i.elim0
      subst hx0
      exact Set.mem_singleton_iff.2 (funext fun j => (hx j).symm)
    calc (strictSignPatterns p).ncard
        ≤ ({fun j => SignType.sign (MvPolynomial.eval (0 : Fin 0 → ℝ) (p j))} :
            Set (Fin m → SignType)).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton _)
      _ = 1 := Set.ncard_singleton _
      _ ≤ _ := by simp
  · -- Choose a witness for each realised pattern.
    have hwit : ∀ σ : Fin m → SignType, ∃ x : Fin n → ℝ,
        σ ∈ strictSignPatterns p → ∀ j, SignType.sign (MvPolynomial.eval x (p j)) = σ j := by
      intro σ
      by_cases h : σ ∈ strictSignPatterns p
      · obtain ⟨x, hx⟩ := h.2
        exact ⟨x, fun _ => hx⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose w hw using hwit
    -- The finite set of witnesses.
    set X : Set (Fin n → ℝ) := w '' strictSignPatterns p with hXdef
    have hX : X.Finite := (Set.toFinite _).image w
    have hXne : ∀ x ∈ X, ∀ j, MvPolynomial.eval x (p j) ≠ 0 := by
      rintro _ ⟨σ, hσ, rfl⟩ j
      intro hzero
      exact hS σ hσ j (by rw [← hw σ hσ j, hzero, sign_zero])
    -- Augment by a quadric with bounded sublevel set and perturb into general position.
    obtain ⟨q, hdegq, hgp, hbdd0, hq0, hqsucc⟩ :=
      exists_generic_augmentation p d hdeg X hX hXne
    -- The lifted patterns: strict patterns of `q` whose zeroth entry is `-1`.
    set S' : Set (Fin (m + 1) → SignType) :=
      {τ | τ ∈ strictSignPatterns q ∧ τ 0 = -1} with hS'def
    have hS' : ∀ τ ∈ S', ∀ j, τ j ≠ 0 := fun _ hτ => hτ.1.1
    -- Charging, via the distinguished index `0`.
    have hcharge : ∀ τ ∈ S', (∃ j, τ j = -1) →
        ∃ (J : Finset (Fin (m + 1))) (x₀ : Fin n → ℝ),
          J.Nonempty ∧ J.card ≤ n ∧ (∀ j ∈ J, MvPolynomial.eval x₀ (q j) = 0) ∧
          Bornology.IsBounded
            (connectedComponentIn {y | ∀ j ∈ J, MvPolynomial.eval y (q j) = 0} x₀) ∧
          ∀ c ∈ connectedComponentIn {y | ∀ j ∈ J, MvPolynomial.eval y (q j) = 0} x₀,
            ∀ k ∉ J, SignType.sign (MvPolynomial.eval c (q k)) = τ k := by
      rintro τ ⟨⟨hτne, x₁, hx₁⟩, hτ0⟩ -
      exact exists_charge hn q hgp τ hτne x₁ hx₁ ⟨0, hτ0, hbdd0⟩
    -- The lift `σ ↦ (-1) :: σ` is injective and lands in `S'`.
    have hinj : Function.Injective
        (fun σ : Fin m → SignType => (Fin.cons (-1) σ : Fin (m + 1) → SignType)) := by
      intro σ σ' h
      simpa [Fin.tail_cons] using congrArg Fin.tail h
    have hsub : (fun σ : Fin m → SignType => (Fin.cons (-1) σ : Fin (m + 1) → SignType)) ''
        strictSignPatterns p ⊆ S' := by
      rintro _ ⟨σ, hσ, rfl⟩
      have hwσ : w σ ∈ X := ⟨σ, hσ, rfl⟩
      refine ⟨mem_strictSignPatterns.2 ⟨?_, w σ, ?_⟩, ?_⟩
      · refine Fin.cases ?_ (fun i => ?_)
        · simp only [Fin.cons_zero]; decide
        · simp only [Fin.cons_succ]; exact hS σ hσ i
      · refine Fin.cases ?_ (fun i => ?_)
        · simp only [Fin.cons_zero]; exact hq0 (w σ) hwσ
        · simp only [Fin.cons_succ]
          rw [hqsucc (w σ) hwσ i]; exact hw σ hσ i
      · simp only [Fin.cons_zero]
    calc (strictSignPatterns p).ncard
        = ((fun σ : Fin m → SignType => (Fin.cons (-1) σ : Fin (m + 1) → SignType)) ''
            strictSignPatterns p).ncard := (Set.ncard_image_of_injective _ hinj).symm
      _ ≤ S'.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ _ := card_le_of_charge q (max 2 d) hD1 hdegq S' hS' hcharge

/-! ## Warren's Theorem 3 form -/

/-- **Warren's Theorem 3.**  For `1 ≤ n ≤ m + 1`, the number of strict sign patterns realised by
`m` real polynomials of degree `≤ d` in `n` variables is at most
`(4 e · max 2 d · (m + 1) / n)^n`. -/
theorem sign_patterns_warren {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hdeg : ∀ j, (p j).totalDegree ≤ d) (hn : 1 ≤ n) (hnm : n ≤ m + 1) :
    ((strictSignPatterns p).ncard : ℝ) ≤ (4 * Real.exp 1 * max 2 d * (m + 1) / n) ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmax0 : (0 : ℝ) ≤ max 2 (d : ℝ) := le_trans (by norm_num) (le_max_left 2 _)
  have hmain := sign_patterns p d hdeg
  have hcast : ((strictSignPatterns p).ncard : ℝ)
      ≤ ((∑ l ∈ Finset.range (n + 1),
            Nat.choose (m + 1) l * 2 ^ l * (2 * max 2 d) ^ n : ℕ) : ℝ) := by
    exact_mod_cast hmain
  refine hcast.trans ?_
  -- bound each term by `C(m + 1, l) * 2^n * (2 * max 2 d)^n`
  have hterm : ((∑ l ∈ Finset.range (n + 1),
        Nat.choose (m + 1) l * 2 ^ l * (2 * max 2 d) ^ n : ℕ) : ℝ)
      ≤ ((∑ l ∈ Finset.range (n + 1), Nat.choose (m + 1) l : ℕ) : ℝ) *
        (2 ^ n * (2 * max 2 (d : ℝ)) ^ n) := by
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have h2 : (2 : ℝ) ^ l ≤ 2 ^ n := pow_le_pow_right₀ one_le_two (by omega)
    have hc : (0 : ℝ) ≤ (Nat.choose (m + 1) l : ℝ) := by positivity
    have hmn : (0 : ℝ) ≤ (2 * max 2 (d : ℝ)) ^ n := pow_nonneg (by linarith) n
    calc (Nat.choose (m + 1) l : ℝ) * 2 ^ l * (2 * max 2 (d : ℝ)) ^ n
        ≤ (Nat.choose (m + 1) l : ℝ) * 2 ^ n * (2 * max 2 (d : ℝ)) ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc) hmn
      _ = (Nat.choose (m + 1) l : ℝ) * (2 ^ n * (2 * max 2 (d : ℝ)) ^ n) := by ring
  refine hterm.trans ?_
  have hsum := DiscretePR.sum_choose_le_exp_pow_range (n := m + 1) (V := n) hn hnm
  have hpos : (0 : ℝ) ≤ 2 ^ n * (2 * max 2 (d : ℝ)) ^ n :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) n)
  refine (mul_le_mul_of_nonneg_right hsum hpos).trans_eq ?_
  rw [← mul_pow, ← mul_pow]
  congr 1
  push_cast
  field_simp
  ring

end SignPatterns

#print axioms SignPatterns.sign_patterns
