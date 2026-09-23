/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import PolyFock.Basic

/-!
# The Fock inner product on `ℂ[z, z̄]`, defined algebraically

The inner product of `L²(ℂ^d ; e^{-|·|²} dm/π^d)` restricted to polynomials in `z` and `z̄` is
determined by the Gaussian moments

`∫ z^μ z̄^ν e^{-|z|²} dm/π^d = δ_{μν} · μ!`.

We *define* the corresponding linear functional `T` on `ℂ[z, z̄]` by that formula, and the
form by `⟪p, q⟫ = T (p · σ q)`, where `σ` conjugates coefficients and swaps `z ↔ z̄`.  No
measure theory is used anywhere: everything below is polynomial algebra.

## Main definitions

* `PolyFock.Fock.P d` — `ℂ[z₁,…,z_d, z̄₁,…,z̄_d]`, realised as `MvPolynomial (Fin d ⊕ Fin d) ℂ`,
  where `Sum.inl i` is the variable `zᵢ` and `Sum.inr i` is the variable `z̄ᵢ`.
* `PolyFock.Fock.ev z` — evaluation at a point `z ∈ ℂ^d` (with `Sum.inr i ↦ conj (zᵢ)`).
* `PolyFock.Fock.T` — the Gaussian expectation.
* `PolyFock.Fock.sig` — the conjugation `σ`.
* `PolyFock.Fock.form p q` — the Fock inner product `⟪p, q⟫ = T (p · σ q)`.

## Main results

* `PolyFock.Fock.T_X_inl_mul`, `PolyFock.Fock.T_X_inr_mul` — the integration-by-parts
  identities `T (zᵢ · u) = T (∂_{z̄ᵢ} u)` and `T (z̄ᵢ · u) = T (∂_{zᵢ} u)`.  These are the
  algebraic heart of the creation/annihilation calculus.
* `PolyFock.Fock.form_conj_symm` — `⟪p, q⟫ = conj ⟪q, p⟫`.
-/

namespace PolyFock.Fock

open Finset MvPolynomial

noncomputable section

variable {d : ℕ}

/-- The variables: `Sum.inl i` stands for `zᵢ`, `Sum.inr i` for `z̄ᵢ`. -/
abbrev Idx (d : ℕ) := Fin d ⊕ Fin d

/-- Polynomials in `z` and `z̄` on `ℂ^d`. -/
abbrev P (d : ℕ) := MvPolynomial (Idx d) ℂ

/-- Evaluation of a polynomial in `z, z̄` at a point of `ℂ^d`. -/
def ev (z : Fin d → ℂ) : P d →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (Sum.elim z fun i => (starRingEnd ℂ) (z i))

@[simp] lemma ev_X_inl (z : Fin d → ℂ) (i : Fin d) : ev z (X (Sum.inl i)) = z i := by
  simp [ev]

@[simp] lemma ev_X_inr (z : Fin d → ℂ) (i : Fin d) :
    ev z (X (Sum.inr i)) = (starRingEnd ℂ) (z i) := by
  simp [ev]

/-! ### The Gaussian expectation -/

/-- The Gaussian moment of a monomial: `∫ z^μ z̄^ν e^{-|z|²} dm/π^d = δ_{μν} μ!`. -/
def wt (ν : Idx d →₀ ℕ) : ℂ :=
  if ∀ i, ν (Sum.inl i) = ν (Sum.inr i) then ∏ i : Fin d, ((ν (Sum.inl i)).factorial : ℂ) else 0

/-- The Gaussian expectation `T p = ∫ p e^{-|z|²} dm/π^d`, defined combinatorially. -/
def T (p : P d) : ℂ := ∑ ν ∈ p.support, coeff ν p * wt ν

lemma T_eq_sum {p : P d} {s : Finset (Idx d →₀ ℕ)} (h : p.support ⊆ s) :
    T p = ∑ ν ∈ s, coeff ν p * wt ν := by
  refine Finset.sum_subset h fun ν _ hν => ?_
  rw [MvPolynomial.notMem_support_iff.mp hν, zero_mul]

@[simp] lemma T_zero : T (0 : P d) = 0 := by simp [T]

lemma T_add (p q : P d) : T (p + q) = T p + T q := by
  classical
  have h1 : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  rw [T_eq_sum h1, T_eq_sum (Finset.subset_union_left (s₂ := q.support)),
    T_eq_sum (Finset.subset_union_right (s₁ := p.support)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ν _ => by rw [MvPolynomial.coeff_add, add_mul]

lemma T_smul (c : ℂ) (p : P d) : T (c • p) = c * T p := by
  classical
  have h1 : (c • p).support ⊆ p.support := MvPolynomial.support_smul
  rw [T_eq_sum h1, T_eq_sum (le_refl p.support), Finset.mul_sum]
  exact Finset.sum_congr rfl fun ν _ => by rw [MvPolynomial.coeff_smul]; ring

@[simp] lemma T_monomial (ν : Idx d →₀ ℕ) (c : ℂ) : T (monomial ν c) = c * wt ν := by
  classical
  rw [T_eq_sum (MvPolynomial.support_monomial_subset (s := ν) (a := c))]
  simp [MvPolynomial.coeff_monomial]

/-- The Gaussian expectation as a linear map. -/
def Tl : P d →ₗ[ℂ] ℂ where
  toFun := T
  map_add' := T_add
  map_smul' c p := by simpa using T_smul c p

@[simp] lemma Tl_apply (p : P d) : Tl p = T p := rfl

@[simp] lemma T_one : T (1 : P d) = 1 := by
  have : (1 : P d) = monomial 0 1 := by simp
  rw [this, T_monomial, wt]
  simp

/-! ### Integration by parts -/

/-- `∏ⱼ (fⱼ + δᵢⱼ)! = (fᵢ + 1) ∏ⱼ fⱼ!`. -/
lemma prod_factorial_succ (f : Fin d → ℕ) (i : Fin d) :
    (∏ j : Fin d, (((f j + if j = i then 1 else 0)).factorial : ℂ))
      = ((f i : ℂ) + 1) * ∏ j : Fin d, ((f j).factorial : ℂ) := by
  classical
  have h : ∀ j : Fin d, (((f j + if j = i then 1 else 0)).factorial : ℂ)
      = (if j = i then ((f i : ℂ) + 1) else 1) * ((f j).factorial : ℂ) := by
    intro j
    split_ifs with hj
    · subst hj; push_cast [Nat.factorial_succ]; ring
    · simp
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_mul_distrib]
  congr 1
  simp

/-- The key combinatorial identity behind `T (zᵢ u) = T (∂_{z̄ᵢ} u)`. -/
lemma wt_single_inl_add (i : Fin d) (ν : Idx d →₀ ℕ) :
    wt (Finsupp.single (Sum.inl i) 1 + ν) = (ν (Sum.inr i) : ℂ) *
      wt (ν - Finsupp.single (Sum.inr i) 1) := by
  classical
  set μ := Finsupp.single (Sum.inl i) 1 + ν with hμ
  set ρ := ν - Finsupp.single (Sum.inr i) 1 with hρ
  have hμl : ∀ j, μ (Sum.inl j) = ν (Sum.inl j) + (if j = i then 1 else 0) := by
    intro j
    simp [hμ, Finsupp.add_apply, Finsupp.single_apply, eq_comm, add_comm]
  have hμr : ∀ j, μ (Sum.inr j) = ν (Sum.inr j) := by
    intro j; simp [hμ, Finsupp.add_apply]
  have hρl : ∀ j, ρ (Sum.inl j) = ν (Sum.inl j) := by
    intro j; simp [hρ, Finsupp.tsub_apply]
  have hρr : ∀ j, ρ (Sum.inr j) = ν (Sum.inr j) - (if j = i then 1 else 0) := by
    intro j
    simp [hρ, Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
  by_cases hb : ν (Sum.inr i) = 0
  · rw [hb]
    have hne : ¬ ∀ j, μ (Sum.inl j) = μ (Sum.inr j) := by
      intro h
      have h2 := h i
      rw [hμl i, hμr i, hb, if_pos rfl] at h2
      omega
    rw [wt, if_neg hne]
    simp
  · have hiff : (∀ j, μ (Sum.inl j) = μ (Sum.inr j)) ↔ (∀ j, ρ (Sum.inl j) = ρ (Sum.inr j)) := by
      constructor
      · intro h j
        have h2 := h j
        rw [hμl j, hμr j] at h2
        rw [hρl j, hρr j]
        split_ifs at h2 ⊢ <;> omega
      · intro h j
        have h2 := h j
        rw [hρl j, hρr j] at h2
        rw [hμl j, hμr j]
        split_ifs at h2 ⊢ with hj
        · subst hj; omega
        · omega
    by_cases hcond : ∀ j, ρ (Sum.inl j) = ρ (Sum.inr j)
    · rw [wt, wt, if_pos (hiff.mpr hcond), if_pos hcond]
      have hci := hcond i
      rw [hρl i, hρr i, if_pos rfl] at hci
      have h2 : ν (Sum.inr i) = ν (Sum.inl i) + 1 := by omega
      calc ∏ j : Fin d, ((μ (Sum.inl j)).factorial : ℂ)
          = ∏ j : Fin d, (((ν (Sum.inl j) + if j = i then 1 else 0)).factorial : ℂ) :=
            Finset.prod_congr rfl fun j _ => by rw [hμl j]
        _ = ((ν (Sum.inl i) : ℂ) + 1) * ∏ j : Fin d, ((ν (Sum.inl j)).factorial : ℂ) :=
            prod_factorial_succ _ i
        _ = (ν (Sum.inr i) : ℂ) * ∏ j : Fin d, ((ρ (Sum.inl j)).factorial : ℂ) := by
            rw [h2]
            push_cast
            congr 1
            exact Finset.prod_congr rfl fun j _ => by rw [hρl j]
    · rw [wt, wt, if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]
      simp

lemma T_X_inl_mul (i : Fin d) (u : P d) :
    T (X (Sum.inl i) * u) = T ((pderiv (Sum.inr i)) u) := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial ν c =>
      rw [X, MvPolynomial.monomial_mul, one_mul, pderiv_monomial, T_monomial, T_monomial,
        wt_single_inl_add]
      ring
  | add p q hp hq =>
      rw [mul_add, T_add, hp, hq, map_add, T_add]

/-- The companion identity, obtained from `wt` by symmetry in `z ↔ z̄`. -/
lemma wt_single_inr_add (i : Fin d) (ν : Idx d →₀ ℕ) :
    wt (Finsupp.single (Sum.inr i) 1 + ν) = (ν (Sum.inl i) : ℂ) *
      wt (ν - Finsupp.single (Sum.inl i) 1) := by
  classical
  set μ := Finsupp.single (Sum.inr i) 1 + ν with hμ
  set ρ := ν - Finsupp.single (Sum.inl i) 1 with hρ
  have hμr : ∀ j, μ (Sum.inr j) = ν (Sum.inr j) + (if j = i then 1 else 0) := by
    intro j
    simp [hμ, Finsupp.add_apply, Finsupp.single_apply, eq_comm, add_comm]
  have hμl : ∀ j, μ (Sum.inl j) = ν (Sum.inl j) := by
    intro j; simp [hμ, Finsupp.add_apply]
  have hρr : ∀ j, ρ (Sum.inr j) = ν (Sum.inr j) := by
    intro j; simp [hρ, Finsupp.tsub_apply]
  have hρl : ∀ j, ρ (Sum.inl j) = ν (Sum.inl j) - (if j = i then 1 else 0) := by
    intro j
    simp [hρ, Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
  by_cases ha : ν (Sum.inl i) = 0
  · rw [ha]
    have hne : ¬ ∀ j, μ (Sum.inl j) = μ (Sum.inr j) := by
      intro h
      have h2 := h i
      rw [hμl i, hμr i, ha, if_pos rfl] at h2
      omega
    rw [wt, if_neg hne]
    simp
  · have hiff : (∀ j, μ (Sum.inl j) = μ (Sum.inr j)) ↔ (∀ j, ρ (Sum.inl j) = ρ (Sum.inr j)) := by
      constructor
      · intro h j
        have h2 := h j
        rw [hμl j, hμr j] at h2
        rw [hρl j, hρr j]
        split_ifs at h2 ⊢ <;> omega
      · intro h j
        have h2 := h j
        rw [hρl j, hρr j] at h2
        rw [hμl j, hμr j]
        split_ifs at h2 ⊢ with hj
        · subst hj; omega
        · omega
    by_cases hcond : ∀ j, ρ (Sum.inl j) = ρ (Sum.inr j)
    · rw [wt, wt, if_pos (hiff.mpr hcond), if_pos hcond]
      have hg : ∀ j : Fin d, ν (Sum.inl j) = ρ (Sum.inl j) + (if j = i then 1 else 0) := by
        intro j
        rw [hρl j]
        split_ifs with hj
        · subst hj; omega
        · simp
      have hgi := hg i
      rw [if_pos rfl] at hgi
      calc ∏ j : Fin d, ((μ (Sum.inl j)).factorial : ℂ)
          = ∏ j : Fin d, (((ρ (Sum.inl j) + if j = i then 1 else 0)).factorial : ℂ) :=
            Finset.prod_congr rfl fun j _ => by rw [hμl j, hg j]
        _ = ((ρ (Sum.inl i) : ℂ) + 1) * ∏ j : Fin d, ((ρ (Sum.inl j)).factorial : ℂ) :=
            prod_factorial_succ _ i
        _ = (ν (Sum.inl i) : ℂ) * ∏ j : Fin d, ((ρ (Sum.inl j)).factorial : ℂ) := by
            congr 1
            rw [hgi]
            push_cast
            ring
    · rw [wt, wt, if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]
      simp

lemma T_X_inr_mul (i : Fin d) (u : P d) :
    T (X (Sum.inr i) * u) = T ((pderiv (Sum.inl i)) u) := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial ν c =>
      rw [X, MvPolynomial.monomial_mul, one_mul, pderiv_monomial, T_monomial, T_monomial,
        wt_single_inr_add]
      ring
  | add p q hp hq =>
      rw [mul_add, T_add, hp, hq, map_add, T_add]

/-! ### The conjugation `σ` and the Fock form -/

/-- The conjugation `σ`: conjugate the coefficients and swap the roles of `z` and `z̄`.
It is a ring homomorphism, and conjugate-linear over `ℂ`. -/
def sig : P d →+* P d :=
  (MvPolynomial.rename (Sum.swap : Idx d → Idx d)).toRingHom.comp
    (MvPolynomial.map (starRingEnd ℂ))

@[simp] lemma sig_monomial (ν : Idx d →₀ ℕ) (c : ℂ) :
    sig (monomial ν c) = monomial (ν.mapDomain Sum.swap) ((starRingEnd ℂ) c) := by
  simp [sig, MvPolynomial.map_monomial, MvPolynomial.rename_monomial]

@[simp] lemma sig_X_inl (i : Fin d) : sig (X (Sum.inl i) : P d) = X (Sum.inr i) := by
  simp [sig]

@[simp] lemma sig_X_inr (i : Fin d) : sig (X (Sum.inr i) : P d) = X (Sum.inl i) := by
  simp [sig]

@[simp] lemma sig_C (c : ℂ) : sig (C c : P d) = C ((starRingEnd ℂ) c) := by
  simp [sig]

lemma sig_smul (c : ℂ) (p : P d) : sig (c • p) = (starRingEnd ℂ) c • sig p := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, sig_C, ← MvPolynomial.smul_eq_C_mul]

@[simp] lemma sig_sig (p : P d) : sig (sig p) = p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial ν c =>
      rw [sig_monomial, sig_monomial, Complex.conj_conj, ← Finsupp.mapDomain_comp]
      congr 1
      have : (Sum.swap ∘ Sum.swap : Idx d → Idx d) = id := by
        funext x; cases x <;> rfl
      rw [this, Finsupp.mapDomain_id]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

lemma wt_conj (ν : Idx d →₀ ℕ) : (starRingEnd ℂ) (wt ν) = wt ν := by
  rw [wt]
  split
  · rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => Complex.conj_natCast _
  · simp

lemma wt_mapDomain_swap (ν : Idx d →₀ ℕ) : wt (ν.mapDomain Sum.swap) = wt ν := by
  classical
  have hinj : Function.Injective (Sum.swap : Idx d → Idx d) := fun a b h => by
    have h2 := congrArg Sum.swap h
    simpa using h2
  have hl : ∀ i, (ν.mapDomain Sum.swap) (Sum.inl i) = ν (Sum.inr i) := by
    intro i
    have := Finsupp.mapDomain_apply hinj ν (Sum.inr i)
    simpa using this
  have hr : ∀ i, (ν.mapDomain Sum.swap) (Sum.inr i) = ν (Sum.inl i) := by
    intro i
    have := Finsupp.mapDomain_apply hinj ν (Sum.inl i)
    simpa using this
  rw [wt, wt]
  by_cases h : ∀ i, ν (Sum.inl i) = ν (Sum.inr i)
  · rw [if_pos h, if_pos (fun i => by rw [hl i, hr i]; exact (h i).symm)]
    exact Finset.prod_congr rfl fun i _ => by rw [hl i, h i]
  · rw [if_neg h, if_neg (fun hh => h (fun i => by
      have := hh i; rw [hl i, hr i] at this; exact this.symm))]

lemma T_sig (p : P d) : T (sig p) = (starRingEnd ℂ) (T p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial ν c => rw [sig_monomial, T_monomial, T_monomial, map_mul, wt_mapDomain_swap, wt_conj]
  | add p q hp hq => rw [map_add, T_add, T_add, hp, hq, map_add]

/-- The Fock inner product on `ℂ[z, z̄]`:
`⟪p, q⟫ = T (p · σ q) = ∫ p conj(q) e^{-|z|²} dm/π^d`. -/
def form (p q : P d) : ℂ := T (p * sig q)

lemma form_add_left (p₁ p₂ q : P d) : form (p₁ + p₂) q = form p₁ q + form p₂ q := by
  rw [form, form, form, add_mul, T_add]

lemma form_add_right (p q₁ q₂ : P d) : form p (q₁ + q₂) = form p q₁ + form p q₂ := by
  rw [form, form, form, map_add, mul_add, T_add]

lemma form_smul_left (c : ℂ) (p q : P d) : form (c • p) q = c * form p q := by
  rw [form, form, smul_mul_assoc, T_smul]

lemma form_smul_right (c : ℂ) (p q : P d) :
    form p (c • q) = (starRingEnd ℂ) c * form p q := by
  rw [form, form, sig_smul, mul_smul_comm, T_smul]

@[simp] lemma form_zero_left (q : P d) : form 0 q = 0 := by simp [form]

@[simp] lemma form_zero_right (p : P d) : form p 0 = 0 := by simp [form]

/-- Conjugate symmetry of the Fock form. -/
lemma form_conj_symm (p q : P d) : form p q = (starRingEnd ℂ) (form q p) := by
  rw [form, form, ← T_sig, map_mul, sig_sig, mul_comm]

@[simp] lemma form_one_one : form (1 : P d) 1 = 1 := by simp [form]


end

end PolyFock.Fock
