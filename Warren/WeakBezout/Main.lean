/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.WeakBezout.GradedDim
import Warren.WeakBezout.Interpolation
import Warren.WeakBezout.NullstellensatzStep
import Warren.WeakBezout.Count
import Warren.WeakBezout.Degeneration
import Warren.WeakBezout.Regularity

/-! # Weak Bezout: Main theorem

The sharp weak Bézout theorem `WeakBezout.weak_bezout`: over an algebraically closed
field `k`, if `p₁, …, pₙ ∈ k[X₁, …, Xₙ]` have `totalDegree pᵢ ≤ dᵢ` and their degree-`dᵢ`
homogeneous components (leading forms) have no common zero except the origin, then the common
zero set of the `pᵢ` is finite with at most `d₁ ⋯ dₙ` points.

The proof assembles the ingredients from the sibling files:
* `NullstellensatzStep.exists_pow_le` gives a power of the irrelevant ideal inside the
  leading-form ideal `J = (L₁, …, Lₙ)`, so all homogeneous polynomials of large degree lie
  in `J`;
* `Regularity.isWeaklyRegular_ofFn` makes `L₁, …, Lₙ` a weakly regular sequence;
* `Count.finrank_quotient_span_eq_prod` computes `dim_k (R ⧸ J) = ∏ dᵢ`;
* `Degeneration.finrank_quotient_le` bounds `dim_k (R ⧸ I) ≤ dim_k (R ⧸ J)` for
  `I = (p₁, …, pₙ)`;
* `Interpolation.card_le_finrank_quotient` bounds the number of common zeros by
  `dim_k (R ⧸ I)`.
-/

namespace WeakBezout

open MvPolynomial

/-- A set all of whose finite injective families have size at most `B` is finite with at most
`B` elements. -/
private theorem finite_and_ncard_le {α : Type*} {Z : Set α} {B : ℕ}
    (h : ∀ (N : ℕ) (x : Fin N → α), Function.Injective x → (∀ j, x j ∈ Z) → N ≤ B) :
    Z.Finite ∧ Z.ncard ≤ B := by
  classical
  -- every finite subset of `Z` has at most `B` elements
  have hfinset : ∀ T : Finset α, ↑T ⊆ Z → T.card ≤ B := by
    intro T hT
    have hinj : Function.Injective fun j : Fin T.card => (T.equivFin.symm j : α) :=
      Subtype.coe_injective.comp T.equivFin.symm.injective
    exact h T.card _ hinj fun j => hT (Finset.mem_coe.mpr (T.equivFin.symm j).2)
  have hfin : Z.Finite := by
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (B + 1)
    have := hfinset T hTsub
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card Z hfin]
  exact hfinset hfin.toFinset hfin.coe_toFinset.subset

/-- **Sharp weak Bézout theorem.** Let `k` be an algebraically closed field and
`p₁, …, pₙ` polynomials in `n` variables with `deg pᵢ ≤ dᵢ`. If the degree-`dᵢ`
homogeneous components (leading forms) have no common zero except the origin, then
the common zero set of the `pᵢ` is finite with at most `d₁ ⋯ dₙ` points. -/
theorem weak_bezout {n : ℕ} {k : Type*} [Field k] [IsAlgClosed k]
    (p : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hdeg : ∀ i, (p i).totalDegree ≤ d i)
    (hlead : ∀ x : Fin n → k,
      (∀ i, MvPolynomial.eval x (MvPolynomial.homogeneousComponent (d i) (p i)) = 0) → x = 0) :
    {x : Fin n → k | ∀ i, MvPolynomial.eval x (p i) = 0}.Finite ∧
    {x : Fin n → k | ∀ i, MvPolynomial.eval x (p i) = 0}.ncard ≤ ∏ i, d i := by
  classical
  -- the leading forms
  have hhom : ∀ i, (homogeneousComponent (d i) (p i)).IsHomogeneous (d i) :=
    fun i => homogeneousComponent_isHomogeneous _ _
  -- Nullstellensatz step: a power of the irrelevant ideal lies in the leading-form ideal
  obtain ⟨s, hpow⟩ :=
    exists_pow_le (fun i => homogeneousComponent (d i) (p i)) d hhom hd hlead
  -- hence all homogeneous polynomials of degree `≥ s` lie in the leading-form ideal
  have hT : ∀ t, s ≤ t → homogeneousSubmodule (Fin n) k t ≤
      Submodule.restrictScalars k
        (Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) := by
    intro t hst f hf
    rw [Submodule.restrictScalars_mem]
    exact isHomogeneous_mem_of_le hst f ((mem_homogeneousSubmodule _ _).mp hf) hpow
  -- the leading forms are a weakly regular sequence
  have hreg := isWeaklyRegular_ofFn (fun i => homogeneousComponent (d i) (p i)) d hhom hd hlead
  -- dimension of the quotient by the leading-form ideal
  obtain ⟨hJfd, hJrank⟩ := finrank_quotient_span_eq_prod
    (fun i => homogeneousComponent (d i) (p i)) d hhom hd hreg s hT
  -- degeneration: the quotient by `(p₁, …, pₙ)` is at most as large
  obtain ⟨hIfd, hIle⟩ := finrank_quotient_le p d hdeg s hT
  haveI := hIfd
  -- count the zeros by Lagrange interpolation
  apply finite_and_ncard_le
  intro N x hinj hmem
  have hbound : N ≤ Module.finrank k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p)) := by
    refine card_le_finrank_quotient (Ideal.span (Set.range p)) x hinj ?_
    intro j f hf
    have hker : Ideal.span (Set.range p) ≤ RingHom.ker (MvPolynomial.eval (x j)) := by
      rw [Ideal.span_le]
      rintro g ⟨i, rfl⟩
      exact SetLike.mem_coe.mpr (RingHom.mem_ker.mpr (hmem j i))
    exact RingHom.mem_ker.mp (hker hf)
  calc N ≤ Module.finrank k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p)) := hbound
    _ ≤ Module.finrank k (MvPolynomial (Fin n) k ⧸
          Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) := hIle
    _ = ∏ i, d i := hJrank

end WeakBezout
