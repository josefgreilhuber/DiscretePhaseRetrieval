/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-! # Weak Bezout: Nullstellensatz step

For a family `L : Fin n → MvPolynomial (Fin n) k` of homogeneous polynomials of positive
degrees whose only common zero is the origin (`k` algebraically closed), the radical of
`Ideal.span (Set.range L)` is the ideal `m` of all variables. Consequently some power of `m`
is contained in the span, and homogeneous polynomials of large degree lie in the span.
-/

namespace WeakBezout

open MvPolynomial

variable {n : ℕ} {k : Type*} [Field k]

/-- A homogeneous polynomial of positive degree lies in the ideal of variables. -/
theorem mem_idealOfVars_of_isHomogeneous {f : MvPolynomial (Fin n) k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 1 ≤ d) :
    f ∈ MvPolynomial.idealOfVars (Fin n) k := by
  rw [← pow_one (MvPolynomial.idealOfVars (Fin n) k), mem_pow_idealOfVars_iff']
  intro x hx
  exact hf.coeff_eq_zero (by omega)

/-- The ideal of variables is the vanishing ideal of the origin. -/
theorem idealOfVars_eq_vanishingIdeal :
    MvPolynomial.idealOfVars (Fin n) k =
      MvPolynomial.vanishingIdeal k ({0} : Set (Fin n → k)) := by
  ext p
  rw [← pow_one (MvPolynomial.idealOfVars (Fin n) k)]
  simp only [mem_pow_idealOfVars_iff', mem_vanishingIdeal_singleton_iff,
    aeval_eq_eval, eval_zero, constantCoeff_eq]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h x hx
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
    rwa [hx0]

/-- If the homogeneous family `L` (of positive degrees) has the origin as its only common
zero, then the radical of the ideal spanned by `L` is the ideal of variables. -/
theorem radical_span_eq [IsAlgClosed k]
    (L : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hhom : ∀ i, (L i).IsHomogeneous (d i)) (hd : ∀ i, 1 ≤ d i)
    (hL : ∀ x : Fin n → k, (∀ i, MvPolynomial.eval x (L i) = 0) → x = 0) :
    (Ideal.span (Set.range L)).radical = MvPolynomial.idealOfVars (Fin n) k := by
  have hzero : MvPolynomial.zeroLocus k (Ideal.span (Set.range L)) =
      ({0} : Set (Fin n → k)) := by
    rw [MvPolynomial.zeroLocus_span]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.forall_mem_range, aeval_eq_eval]
    constructor
    · exact hL x
    · rintro rfl i
      rw [eval_zero, constantCoeff_eq]
      refine (hhom i).coeff_eq_zero ?_
      have h1 := hd i
      simp only [map_zero]
      omega
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k), hzero,
    idealOfVars_eq_vanishingIdeal]

/-- Some power of the ideal of variables is contained in the span of `L`. -/
theorem exists_pow_le [IsAlgClosed k]
    (L : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hhom : ∀ i, (L i).IsHomogeneous (d i)) (hd : ∀ i, 1 ≤ d i)
    (hL : ∀ x : Fin n → k, (∀ i, MvPolynomial.eval x (L i) = 0) → x = 0) :
    ∃ s : ℕ, MvPolynomial.idealOfVars (Fin n) k ^ s ≤ Ideal.span (Set.range L) :=
  Ideal.exists_pow_le_of_le_radical_of_fg (radical_span_eq L d hhom hd hL).ge
    (MvPolynomial.idealOfVars_fg (Fin n) k)

/-- A homogeneous polynomial of degree at least `s` lies in any ideal containing the `s`-th
power of the ideal of variables. -/
theorem isHomogeneous_mem_of_le {Jarg : Ideal (MvPolynomial (Fin n) k)} {s t : ℕ}
    (hst : s ≤ t) (f : MvPolynomial (Fin n) k) (hf : f.IsHomogeneous t)
    (hpow : MvPolynomial.idealOfVars (Fin n) k ^ s ≤ Jarg) : f ∈ Jarg := by
  refine hpow (Ideal.pow_le_pow_right hst ?_)
  rw [mem_pow_idealOfVars_iff']
  exact fun x hx => hf.coeff_eq_zero (by omega)

end WeakBezout
