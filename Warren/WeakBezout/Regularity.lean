/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.WeakBezout.DepthFragment
import Warren.WeakBezout.NullstellensatzStep
import Warren.WeakBezout.GradedDim

/-! # Weak Bezout: Regularity

The main theorem `WeakBezout.isWeaklyRegular_ofFn`: a family `L : Fin n → k[X₁, …, Xₙ]` of
homogeneous polynomials of positive degrees whose only common zero is the origin (`k`
algebraically closed) forms a weakly regular sequence on the polynomial ring.

The proof localizes at the irrelevant ideal `m = (X₁, …, Xₙ)`:
* the variables `X₁, …, Xₙ` form a weakly regular sequence on `R = k[X₁, …, Xₙ]`
  (`isWeaklyRegular_ofFn_X`), hence on `A = R_m` by flatness;
* by the Nullstellensatz step, `√(L) = m`, so the quotient of `A` by the localized ideal `(L)`
  has a one-point spectrum and Krull dimension `≤ 0`;
* the depth-fragment criterion `isWeaklyRegular_of_dim_quotient_le` then makes the localized
  family weakly regular on `A` (`isWeaklyRegular_localization_ofFn`);
* regularity descends back to `R` by graded faithfulness: colon ideals of homogeneously
  generated ideals by homogeneous elements are spanned by homogeneous elements, and a
  polynomial outside `m` has an invertible constant term (`stage_of_localization`).
-/

namespace WeakBezout

open MvPolynomial RingTheory.Sequence

section Bridges

variable {R : Type*} [CommRing R]

/-- `I • ⊤ = I` for an ideal acting on the ring itself. -/
lemma ideal_smul_top (I : Ideal R) : (I • ⊤ : Submodule R R) = I := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

/-- Being regular on `R ⧸ I` (as a quotient module) is the ideal-theoretic statement
`r * f ∈ I → f ∈ I`. -/
lemma isSMulRegular_quotient_iff (I : Ideal R) (r : R) :
    IsSMulRegular (R ⧸ (I • ⊤ : Submodule R R)) r ↔ ∀ f : R, r * f ∈ I → f ∈ I := by
  constructor
  · intro hreg f hf
    have h0 : r • (Submodule.Quotient.mk f : R ⧸ (I • ⊤ : Submodule R R)) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ideal_smul_top,
        smul_eq_mul]
      exact hf
    have hf0 : (Submodule.Quotient.mk f : R ⧸ (I • ⊤ : Submodule R R)) = 0 := by
      apply hreg
      change r • (Submodule.Quotient.mk f : R ⧸ (I • ⊤ : Submodule R R)) = r • 0
      rw [h0, smul_zero]
    rwa [Submodule.Quotient.mk_eq_zero, ideal_smul_top] at hf0
  · intro h x y hxy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hxy' : r • (Submodule.Quotient.mk f : R ⧸ (I • ⊤ : Submodule R R)) =
        r • Submodule.Quotient.mk g := hxy
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq, ideal_smul_top, smul_eq_mul, smul_eq_mul, ← mul_sub] at hxy'
    rw [Submodule.Quotient.eq, ideal_smul_top]
    exact h _ hxy'

/-- The ideal of a list built from a tuple is the span of the range. -/
lemma ofList_ofFn {n : ℕ} (g : Fin n → R) :
    Ideal.ofList (List.ofFn g) = Ideal.span (Set.range g) :=
  congrArg Ideal.span (Set.ext fun a => List.mem_ofFn' g a)

/-- The ideal of the first `j` entries of a tuple is the span of the corresponding image. -/
lemma ofList_take_ofFn {n : ℕ} (g : Fin n → R) (j : ℕ) :
    Ideal.ofList ((List.ofFn g).take j) =
      Ideal.span (g '' {t : Fin n | (t : ℕ) < j}) := by
  refine congrArg Ideal.span (Set.ext fun a => ?_)
  constructor
  · intro ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hlen := hi
    rw [List.length_take, List.length_ofFn] at hlen
    have hin : i < n := lt_of_lt_of_le hlen (min_le_right _ _)
    have hij : i < j := lt_of_lt_of_le hlen (min_le_left _ _)
    refine ⟨⟨i, hin⟩, hij, ?_⟩
    simp
  · rintro ⟨t, htj, rfl⟩
    refine List.mem_iff_getElem.mpr ⟨(t : ℕ), ?_, ?_⟩
    · rw [List.length_take, List.length_ofFn]
      exact lt_min htj t.isLt
    · simp

/-- Stagewise criterion for weak regularity of a tuple on the ring: at each stage `j`,
multiplication by `g j` must be injective modulo the ideal of the previous entries. -/
lemma isWeaklyRegular_ofFn_of_stage {n : ℕ} (g : Fin n → R)
    (h : ∀ (j : Fin n) (f : R),
      g j * f ∈ Ideal.span (g '' {t : Fin n | (t : ℕ) < (j : ℕ)}) →
      f ∈ Ideal.span (g '' {t : Fin n | (t : ℕ) < (j : ℕ)})) :
    IsWeaklyRegular R (List.ofFn g) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < n := by simpa using hi
  rw [ofList_take_ofFn g i, isSMulRegular_quotient_iff]
  intro f hf
  refine h ⟨i, hi'⟩ f ?_
  rw [List.getElem_ofFn] at hf
  exact hf

/-- Conversely, a weakly regular tuple satisfies the stagewise ideal-theoretic property. -/
lemma stage_of_isWeaklyRegular_ofFn {n : ℕ} (g : Fin n → R)
    (hreg : IsWeaklyRegular R (List.ofFn g)) (j : Fin n) (f : R)
    (hf : g j * f ∈ Ideal.span (g '' {t : Fin n | (t : ℕ) < (j : ℕ)})) :
    f ∈ Ideal.span (g '' {t : Fin n | (t : ℕ) < (j : ℕ)}) := by
  have h := hreg.regular_mod_prev (j : ℕ) (by simp)
  rw [ofList_take_ofFn g (j : ℕ), isSMulRegular_quotient_iff] at h
  refine h f ?_
  rw [List.getElem_ofFn]
  exact hf

end Bridges

variable {n : ℕ} {k : Type*} [Field k]

/-- **Step 1**: the variables form a weakly regular sequence on `k[X₁, …, Xₙ]`. -/
lemma isWeaklyRegular_ofFn_X :
    IsWeaklyRegular (MvPolynomial (Fin n) k)
      (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)) := by
  refine isWeaklyRegular_ofFn_of_stage _ (fun j f hf => ?_)
  rw [mem_ideal_span_X_image] at hf ⊢
  intro μ hμ
  have hmem : Finsupp.single j 1 + μ ∈ (X j * f).support := by
    rw [support_X_mul]
    exact Finset.mem_map.mpr ⟨μ, hμ, addLeftEmbedding_apply _ _⟩
  obtain ⟨t, htS, ht⟩ := hf _ hmem
  have htj : j ≠ t := by
    rintro rfl
    simp only [Set.mem_setOf_eq] at htS
    exact absurd htS (lt_irrefl _)
  refine ⟨t, htS, ?_⟩
  intro h0
  apply ht
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne htj.symm, zero_add, h0]

/-- **Steps 2–4**: the localized family is weakly regular on the localization of
`k[X₁, …, Xₙ]` at the irrelevant ideal. -/
lemma isWeaklyRegular_localization_ofFn [IsAlgClosed k]
    [hmp : (idealOfVars (Fin n) k).IsPrime]
    (L : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hhom : ∀ i, (L i).IsHomogeneous (d i)) (hd : ∀ i, 1 ≤ d i)
    (hL : ∀ x : Fin n → k, (∀ i, MvPolynomial.eval x (L i) = 0) → x = 0) :
    IsWeaklyRegular (Localization.AtPrime (idealOfVars (Fin n) k))
      ((List.ofFn L).map (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (idealOfVars (Fin n) k)))) := by
  -- the localized variables: a weakly regular sequence inside the maximal ideal
  have hws : ∀ w ∈ (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime (idealOfVars (Fin n) k))),
      w ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (idealOfVars (Fin n) k)) := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ((List.mem_ofFn' _ _).mp hx)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime (idealOfVars (Fin n) k)) (idealOfVars (Fin n) k) _).mpr
      (Ideal.subset_span ⟨i, rfl⟩)
  have hwreg := (isWeaklyRegular_ofFn_X (n := n) (k := k)).of_isLocalization
    (Localization.AtPrime (idealOfVars (Fin n) k)) (idealOfVars (Fin n) k).primeCompl
  -- the localized family lies in the maximal ideal
  have hrs : ∀ r ∈ (List.ofFn L).map (algebraMap (MvPolynomial (Fin n) k)
      (Localization.AtPrime (idealOfVars (Fin n) k))),
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (idealOfVars (Fin n) k)) := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ((List.mem_ofFn' _ _).mp hx)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime (idealOfVars (Fin n) k)) (idealOfVars (Fin n) k) _).mpr
      (mem_idealOfVars_of_isHomogeneous (hhom i) (hd i))
  -- every prime of the localization over the localized ideal is the maximal ideal
  have hkey : ∀ q : Ideal (Localization.AtPrime (idealOfVars (Fin n) k)), q.IsPrime →
      Ideal.ofList ((List.ofFn L).map (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (idealOfVars (Fin n) k)))) ≤ q →
      q = IsLocalRing.maximalIdeal (Localization.AtPrime (idealOfVars (Fin n) k)) := by
    intro q hq hle
    refine le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top) ?_
    have hrad := IsLocalization.map_radical (M := (idealOfVars (Fin n) k).primeCompl)
      (S := Localization.AtPrime (idealOfVars (Fin n) k)) (Ideal.span (Set.range L))
    rw [radical_span_eq L d hhom hd hL] at hrad
    have h2 : Ideal.map (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (idealOfVars (Fin n) k))) (idealOfVars (Fin n) k) ≤ q := by
      rw [hrad]
      refine hq.isRadical.radical_le_iff.mpr ?_
      rw [← ofList_ofFn L, Ideal.map_ofList]
      exact hle
    calc IsLocalRing.maximalIdeal (Localization.AtPrime (idealOfVars (Fin n) k))
        = Ideal.map (algebraMap (MvPolynomial (Fin n) k)
            (Localization.AtPrime (idealOfVars (Fin n) k))) (idealOfVars (Fin n) k) :=
          (Localization.AtPrime.map_eq_maximalIdeal (I := idealOfVars (Fin n) k)).symm
      _ ≤ q := h2
  -- hence the quotient has Krull dimension at most `0`
  have hdim : ringKrullDim ((Localization.AtPrime (idealOfVars (Fin n) k)) ⧸
      Ideal.ofList ((List.ofFn L).map (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (idealOfVars (Fin n) k))))) ≤ 0 := by
    have key : ∀ P : PrimeSpectrum ((Localization.AtPrime (idealOfVars (Fin n) k)) ⧸
        Ideal.ofList ((List.ofFn L).map (algebraMap (MvPolynomial (Fin n) k)
          (Localization.AtPrime (idealOfVars (Fin n) k))))),
        Ideal.comap (Ideal.Quotient.mk (Ideal.ofList ((List.ofFn L).map
          (algebraMap (MvPolynomial (Fin n) k)
            (Localization.AtPrime (idealOfVars (Fin n) k)))))) P.asIdeal =
        IsLocalRing.maximalIdeal (Localization.AtPrime (idealOfVars (Fin n) k)) := by
      intro P
      refine hkey _ inferInstance ?_
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact P.asIdeal.zero_mem
    haveI : Subsingleton (PrimeSpectrum ((Localization.AtPrime (idealOfVars (Fin n) k)) ⧸
        Ideal.ofList ((List.ofFn L).map (algebraMap (MvPolynomial (Fin n) k)
          (Localization.AtPrime (idealOfVars (Fin n) k)))))) := by
      constructor
      intro P Q
      apply PrimeSpectrum.ext
      have h := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.ofList ((List.ofFn L).map
        (algebraMap (MvPolynomial (Fin n) k)
          (Localization.AtPrime (idealOfVars (Fin n) k))))))) ((key P).trans (key Q).symm)
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact Order.krullDim_nonpos_of_subsingleton
  exact isWeaklyRegular_of_dim_quotient_le _ _ hws hwreg hrs (by simp) hdim

/-- **Step 5** (graded faithfulness): if multiplication by the homogeneous polynomial `p` is
injective modulo the localized span of a homogeneously generated ideal, then it is injective
modulo the span itself. -/
lemma stage_of_localization [hmp : (idealOfVars (Fin n) k).IsPrime]
    {S : Set (MvPolynomial (Fin n) k)} (hS : ∀ g ∈ S, ∃ e, g.IsHomogeneous e)
    {p : MvPolynomial (Fin n) k} {e : ℕ} (hp : p.IsHomogeneous e)
    (hdown : ∀ b : MvPolynomial (Fin n) k,
      algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime (idealOfVars (Fin n) k)) p *
          algebraMap (MvPolynomial (Fin n) k)
            (Localization.AtPrime (idealOfVars (Fin n) k)) b ∈
          Ideal.map (algebraMap (MvPolynomial (Fin n) k)
            (Localization.AtPrime (idealOfVars (Fin n) k))) (Ideal.span S) →
        algebraMap (MvPolynomial (Fin n) k)
            (Localization.AtPrime (idealOfVars (Fin n) k)) b ∈
          Ideal.map (algebraMap (MvPolynomial (Fin n) k)
            (Localization.AtPrime (idealOfVars (Fin n) k))) (Ideal.span S))
    {f : MvPolynomial (Fin n) k} (hf : p * f ∈ Ideal.span S) : f ∈ Ideal.span S := by
  by_contra hfJ
  -- some homogeneous component of `f` lies outside the ideal
  have hex : ∃ t, homogeneousComponent t f ∉ Ideal.span S := by
    by_contra hall
    push Not at hall
    apply hfJ
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => hall i
  obtain ⟨t, hgJ⟩ := hex
  have hghom : (homogeneousComponent t f).IsHomogeneous t :=
    homogeneousComponent_isHomogeneous t f
  -- `p` multiplies this component into the ideal
  have hpg : p * homogeneousComponent t f ∈ Ideal.span S := by
    have h1 : homogeneousComponent (t + e) (f * p) ∈ Ideal.span S :=
      homogeneousComponent_mem_ideal_span hS (by rwa [mul_comm]) _
    rwa [homogeneousComponent_mul_isHomogeneous_right hp f t, mul_comm] at h1
  -- pass through the localization
  have hdown' := hdown (homogeneousComponent t f) (by
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ hpg)
  obtain ⟨s, hs, hsg⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((idealOfVars (Fin n) k).primeCompl) (Localization.AtPrime (idealOfVars (Fin n) k))
    (Ideal.span S) (homogeneousComponent t f)).mp hdown'
  have hsm : s ∉ idealOfVars (Fin n) k := hs
  -- `s` is not in the irrelevant ideal, so its constant term is nonzero
  have hs0 : MvPolynomial.coeff 0 s ≠ 0 := by
    intro h0
    apply hsm
    rw [← pow_one (idealOfVars (Fin n) k), mem_pow_idealOfVars_iff']
    intro x hx
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
    rwa [hx0]
  -- the constant term of `s` also multiplies the component into the ideal
  have hC : MvPolynomial.C (MvPolynomial.coeff 0 s) * homogeneousComponent t f ∈
      Ideal.span S := by
    have h1 : homogeneousComponent (0 + t) (s * homogeneousComponent t f) ∈ Ideal.span S :=
      homogeneousComponent_mem_ideal_span hS hsg _
    rwa [homogeneousComponent_mul_isHomogeneous_right hghom s 0,
      homogeneousComponent_zero] at h1
  -- but that constant is a unit: contradiction
  exact hgJ ((Ideal.unit_mul_mem_iff_mem _
    (hs0.isUnit.map (MvPolynomial.C : k →+* MvPolynomial (Fin n) k))).mp hC)

/-- **Main theorem.** A family `L : Fin n → k[X₁, …, Xₙ]` of homogeneous polynomials of
positive degrees whose only common zero is the origin (`k` algebraically closed) is a weakly
regular sequence on the polynomial ring. -/
theorem isWeaklyRegular_ofFn [IsAlgClosed k]
    (L : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hhom : ∀ i, (L i).IsHomogeneous (d i)) (hd : ∀ i, 1 ≤ d i)
    (hL : ∀ x : Fin n → k, (∀ i, MvPolynomial.eval x (L i) = 0) → x = 0) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) k) (List.ofFn L) := by
  haveI hmmax : (idealOfVars (Fin n) k).IsMaximal := by
    rw [idealOfVars_eq_vanishingIdeal]
    infer_instance
  haveI hmp : (idealOfVars (Fin n) k).IsPrime := hmmax.isPrime
  have hAreg' : IsWeaklyRegular (Localization.AtPrime (idealOfVars (Fin n) k))
      (List.ofFn (fun t => algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (idealOfVars (Fin n) k)) (L t))) := by
    rw [List.ofFn_comp' L (algebraMap (MvPolynomial (Fin n) k)
      (Localization.AtPrime (idealOfVars (Fin n) k)))]
    exact isWeaklyRegular_localization_ofFn L d hhom hd hL
  have hspan_eq : ∀ j : Fin n,
      Ideal.span ((fun t => algebraMap (MvPolynomial (Fin n) k)
          (Localization.AtPrime (idealOfVars (Fin n) k)) (L t)) ''
        {t : Fin n | (t : ℕ) < (j : ℕ)}) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) k)
          (Localization.AtPrime (idealOfVars (Fin n) k)))
        (Ideal.span (L '' {t : Fin n | (t : ℕ) < (j : ℕ)})) := by
    intro j
    rw [Ideal.map_span, ← Set.image_comp]
    rfl
  refine isWeaklyRegular_ofFn_of_stage L (fun j f hf => ?_)
  refine stage_of_localization (S := L '' {t : Fin n | (t : ℕ) < (j : ℕ)})
    ?_ (hhom j) ?_ hf
  · rintro g ⟨t, -, rfl⟩
    exact ⟨d t, hhom t⟩
  · intro b hb
    have h := stage_of_isWeaklyRegular_ofFn
      (fun t => algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (idealOfVars (Fin n) k)) (L t)) hAreg' j
      (algebraMap (MvPolynomial (Fin n) k)
        (Localization.AtPrime (idealOfVars (Fin n) k)) b)
    rw [hspan_eq j] at h
    exact h hb

end WeakBezout
