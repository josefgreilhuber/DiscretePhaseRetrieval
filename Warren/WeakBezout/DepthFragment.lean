/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib

/-! # Weak Bezout: DepthFragment

An elementary (Ext-free, depth-free) Rees/Kaplansky-style theory of maximal weakly
regular sequences over a commutative Noetherian local ring, culminating in the
criterion `WeakBezout.isWeaklyRegular_of_dim_quotient_le`: if some weakly regular
sequence `ws` of length `n` exists (entries in the maximal ideal), then any list
`rs` of `n` elements of the maximal ideal whose quotient ring `A ⧸ (rs)` has Krull
dimension `≤ 0` is itself weakly regular.

Main ingredients:
* `WeakBezout.IsMaximalSeq`: a weakly regular sequence that cannot be extended by
  any element of the maximal ideal.
* `WeakBezout.exists_associated_ge_of_isSMulRegular` (the "u-trick"): pushing an
  associated prime through a regular element.
* `WeakBezout.cast_length_le_ringKrullDim_quotient`: a weakly regular sequence on
  `M` forces long chains of primes above any associated prime of `M`.
* `WeakBezout.exists_isMaximalSeq_extension`: maximal sequences exist.
* `WeakBezout.length_le_of_isMaximalSeq`: any weakly regular sequence is at most
  as long as any maximal one (the exchange/equal-length theorem).
-/

universe v

namespace WeakBezout

open RingTheory.Sequence Submodule IsLocalRing

open scoped Pointwise

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- A list `rs` is a *maximal (weakly regular) sequence* on `M` if it is weakly
regular and no element of the maximal ideal is regular on `M ⧸ (rs)M`. -/
def IsMaximalSeq (M : Type*) [AddCommGroup M] [Module A M] (rs : List A) : Prop :=
  IsWeaklyRegular M rs ∧
    ∀ r ∈ maximalIdeal A,
      ¬ IsSMulRegular (M ⧸ (Ideal.ofList rs • ⊤ : Submodule A M)) r

section AssociatedPrimes

variable {M : Type v} [AddCommGroup M] [Module A M]

/-- L1: a regular element avoids every associated prime. -/
lemma notMem_of_isSMulRegular {θ : A} (hθ : IsSMulRegular M θ)
    {p : Ideal A} (hp : p ∈ associatedPrimes A M) : θ ∉ p := by
  intro hθp
  have hmem : θ ∈ ⋃ p ∈ associatedPrimes A M, (p : Set A) := Set.mem_biUnion hp hθp
  rw [biUnion_associatedPrimes_eq_compl_regular] at hmem
  exact hmem hθ

/-- L2 (the u-trick): if `θ ∈ 𝔪` is regular on the finite module `M` and
`p` is an associated prime of `M`, then some associated prime of `M ⧸ θM`
contains both `p` and `θ`. -/
lemma exists_associated_ge_of_isSMulRegular [Module.Finite A M]
    {θ : A} (hθm : θ ∈ maximalIdeal A) (hθ : IsSMulRegular M θ)
    {p : Ideal A} (hp : p ∈ associatedPrimes A M) :
    ∃ q ∈ associatedPrimes A (QuotSMulTop θ M), p ≤ q ∧ θ ∈ q := by
  have hprime : p.IsPrime := hp.isPrime
  obtain ⟨-, x, hx⟩ := isAssociatedPrime_iff.mp hp
  -- take a maximal cyclic submodule among those with annihilator `p`
  set S : Set (Submodule A M) :=
    {N | ∃ u : M, N = span A {u} ∧ p = (⊥ : Submodule A M).colon {u}} with hS
  obtain ⟨N, hNS, hmax⟩ :=
    (set_has_maximal_iff_noetherian.mpr inferInstance) S ⟨span A {x}, x, rfl, hx⟩
  obtain ⟨u, rfl, hu⟩ := hNS
  have hu0 : u ≠ 0 := by
    rintro rfl
    refine hprime.ne_top ?_
    rw [hu]
    ext r
    simp [mem_colon_singleton]
  -- the image of `u` in `M ⧸ θM` is nonzero
  have hbar : (Submodule.Quotient.mk u : QuotSMulTop θ M) ≠ 0 := by
    intro h0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨v, -, hv⟩ := (mem_smul_pointwise_iff_exists u θ ⊤).mp h0
    -- `v` has the same annihilator
    have hpv : p = (⊥ : Submodule A M).colon {v} := by
      ext r
      rw [mem_colon_singleton, mem_bot]
      constructor
      · intro hr
        have hru : r • u = 0 := by
          have := hu ▸ hr
          rwa [mem_colon_singleton, mem_bot] at this
        apply hθ
        show θ • (r • v) = θ • 0
        rw [smul_zero, smul_comm, hv, hru]
      · intro hr
        rw [hu, mem_colon_singleton, mem_bot, ← hv, smul_comm, hr, smul_zero]
    -- `span {u} ≤ span {v}` and by maximality they are equal
    have hle : span A {u} ≤ span A {v} := by
      rw [span_le, Set.singleton_subset_iff]
      exact mem_span_singleton.mpr ⟨θ, hv⟩
    have heq : span A {u} = span A {v} := by
      rcases hle.lt_or_eq with hlt | heq
      · exact absurd hlt (hmax _ ⟨v, rfl, hpv⟩)
      · exact heq
    obtain ⟨c, hc⟩ := mem_span_singleton.mp (heq ▸ mem_span_singleton_self v)
    have hv0 : (1 - c * θ) • v = 0 := by
      rw [sub_smul, one_smul, mul_smul, hv, hc, sub_self]
    have hunit : IsUnit (1 - c * θ) :=
      isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_left _ c hθm)
    have : v = 0 := hunit.smul_eq_zero.mp hv0
    exact hu0 (by rw [← hv, this, smul_zero])
  obtain ⟨q, hq, hle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing A
      (Submodule.Quotient.mk u : QuotSMulTop θ M) hbar
  refine ⟨q, hq, ?_, ?_⟩
  · intro r hr
    apply hle
    rw [mem_colon_singleton, mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    have hru : r • u = 0 := by
      have := hu ▸ hr
      rwa [mem_colon_singleton, mem_bot] at this
    rw [hru]
    exact zero_mem _
  · apply hle
    rw [mem_colon_singleton, mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact smul_mem_pointwise_smul u θ ⊤ mem_top

end AssociatedPrimes

section Chains

/-- L3: a weakly regular sequence on `M` of length `n` produces a strictly
increasing chain of primes of length `n` starting at any associated prime of
`M`. -/
lemma exists_ltSeries_of_associated :
    ∀ (rs : List A) {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M],
      (∀ r ∈ rs, r ∈ maximalIdeal A) → IsWeaklyRegular M rs →
      ∀ {p : Ideal A}, p ∈ associatedPrimes A M →
      ∃ c : LTSeries (PrimeSpectrum A), c.length = rs.length ∧ c.head.asIdeal = p := by
  intro rs
  induction rs with
  | nil =>
    intro M _ _ _ _ _ p hp
    exact ⟨RelSeries.singleton _ ⟨p, hp.isPrime⟩, rfl, rfl⟩
  | cons θ rs ih =>
    intro M _ _ _ hmem hreg p hp
    obtain ⟨hθreg, hreg'⟩ := (isWeaklyRegular_cons_iff M θ rs).mp hreg
    have hθm : θ ∈ maximalIdeal A := hmem θ List.mem_cons_self
    have hθp : θ ∉ p := notMem_of_isSMulRegular hθreg hp
    obtain ⟨q, hq, hpq, hθq⟩ := exists_associated_ge_of_isSMulRegular hθm hθreg hp
    obtain ⟨c, hclen, hchead⟩ :=
      ih (fun r hr => hmem r (List.mem_cons_of_mem θ hr)) hreg' hq
    have hlt : (⟨p, hp.isPrime⟩ : PrimeSpectrum A) < c.head := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal, hchead]
      refine lt_of_le_of_ne hpq fun h => hθp ?_
      have h' : p = q := h
      rw [h']
      exact hθq
    exact ⟨c.cons ⟨p, hp.isPrime⟩ hlt, by simpa using hclen, by simp⟩

/-- L3a: a weakly regular sequence of length `n` on `M` forces
`n ≤ dim (A ⧸ p)` for every associated prime `p` of `M`. -/
lemma cast_length_le_ringKrullDim_quotient {M : Type v} [AddCommGroup M]
    [Module A M] [Module.Finite A M] {rs : List A}
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal A) (hreg : IsWeaklyRegular M rs)
    {p : Ideal A} (hp : p ∈ associatedPrimes A M) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p) := by
  obtain ⟨c, hclen, hchead⟩ := exists_ltSeries_of_associated rs hmem hreg hp
  rw [ringKrullDim_quotient, Order.le_krullDim_iff]
  have hmemZL : ∀ i, c i ∈ PrimeSpectrum.zeroLocus (p : Set A) := by
    intro i
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact le_trans (le_of_eq hchead.symm)
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (c.head_le i))
  exact ⟨LTSeries.mk c.length (fun i => ⟨c i, hmemZL i⟩)
    (fun i j hij => Subtype.mk_lt_mk.mpr (c.strictMono hij)), hclen⟩

/-- Any weakly regular sequence on a nontrivial finite module, with entries in
the maximal ideal, has length at most `spanFinrank 𝔪`. -/
lemma length_le_spanFinrank {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] {rs : List A}
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal A) (hreg : IsWeaklyRegular M rs) :
    rs.length ≤ (maximalIdeal A).spanFinrank := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty A M
  have h1 := cast_length_le_ringKrullDim_quotient hmem hreg hp
  have h2 : ringKrullDim (A ⧸ p) ≤ ringKrullDim A := ringKrullDim_quotient_le p
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal A
  have := h1.trans (h2.trans h3)
  exact_mod_cast this

end Chains

section MaximalSeq

/-- L4: every weakly regular sequence (entries in `𝔪`) on a nontrivial finite
module extends to a maximal one. -/
lemma exists_isMaximalSeq_extension {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] {rs : List A}
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal A) (hreg : IsWeaklyRegular M rs) :
    ∃ ext : List A, (∀ r ∈ ext, r ∈ maximalIdeal A) ∧ IsMaximalSeq M (rs ++ ext) := by
  suffices H : ∀ (k : ℕ) (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) →
      IsWeaklyRegular M rs → (maximalIdeal A).spanFinrank + 1 - rs.length ≤ k →
      ∃ ext, (∀ r ∈ ext, r ∈ maximalIdeal A) ∧ IsMaximalSeq M (rs ++ ext) by
    exact H _ rs hmem hreg le_rfl
  intro k
  induction k with
  | zero =>
    intro rs hmem hreg hk
    have := length_le_spanFinrank hmem hreg
    omega
  | succ k ih =>
    intro rs hmem hreg hk
    by_cases hext : ∃ r ∈ maximalIdeal A,
        IsSMulRegular (M ⧸ (Ideal.ofList rs • ⊤ : Submodule A M)) r
    · obtain ⟨r, hrm, hrreg⟩ := hext
      have hreg' : IsWeaklyRegular M (rs ++ [r]) := by
        rw [isWeaklyRegular_append_iff]
        exact ⟨hreg, (isWeaklyRegular_singleton_iff _ _).mpr hrreg⟩
      have hmem' : ∀ x ∈ rs ++ [r], x ∈ maximalIdeal A := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hmem x hx
        · rw [List.mem_singleton] at hx
          exact hx ▸ hrm
      obtain ⟨ext, hextm, hmax⟩ := ih (rs ++ [r]) hmem' hreg' (by simp; omega)
      refine ⟨r :: ext, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hrm
        · exact hextm x hx
      · rwa [← List.singleton_append, ← List.append_assoc]
    · push_neg at hext
      refine ⟨[], by simp, ?_⟩
      rw [List.append_nil]
      exact ⟨hreg, hext⟩

end MaximalSeq

section Swap

lemma ofList_append_singleton (rs : List A) (θ : A) :
    Ideal.ofList (rs ++ [θ]) = Ideal.ofList (θ :: rs) := by
  rw [Ideal.ofList_append, Ideal.ofList_singleton, Ideal.ofList_cons, sup_comm]

/-- The equivalence `M ⧸ (r₁, …, rₙ, θ)M ≃ (M ⧸ (r₁, …, rₙ)M) ⧸ θ(⋯)`. -/
def quotConcatEquiv (M : Type v) [AddCommGroup M] [Module A M] (rs : List A) (θ : A) :
    (M ⧸ (Ideal.ofList (rs ++ [θ]) • ⊤ : Submodule A M)) ≃ₗ[A]
      QuotSMulTop θ (M ⧸ (Ideal.ofList rs • ⊤ : Submodule A M)) :=
  Submodule.quotEquivOfEq _ _ (by rw [ofList_append_singleton]) ≪≫ₗ
    Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter M θ rs

/-- The swap lemma: if `θ, c ∈ 𝔪` are both regular on `N` and no element of `𝔪`
is regular on `N ⧸ θN`, then no element of `𝔪` is regular on `N ⧸ cN`. -/
lemma swap_last {N : Type v} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Nontrivial N] {θ c : A} (hθm : θ ∈ maximalIdeal A) (hcm : c ∈ maximalIdeal A)
    (hθ : IsSMulRegular N θ) (hc : IsSMulRegular N c)
    (hmax : ∀ r ∈ maximalIdeal A, ¬ IsSMulRegular (QuotSMulTop θ N) r) :
    ∀ r ∈ maximalIdeal A, ¬ IsSMulRegular (QuotSMulTop c N) r := by
  -- `𝔪` is an associated prime of `N ⧸ θN`
  haveI := nontrivial_quotSMulTop_of_mem_maximalIdeal N hθm
  have hsub : (maximalIdeal A : Set A) ⊆
      ⋃ p ∈ associatedPrimes A (QuotSMulTop θ N), (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact fun r hr => hmax r hr
  obtain ⟨q, hq, hle⟩ :=
    (Ideal.subset_union_prime_finite (associatedPrimes.finite A _) (f := id) ⊥ ⊥
      (fun i hi _ _ => hi.isPrime)).mp hsub
  have hqm : maximalIdeal A = q :=
    (maximalIdeal.isMaximal A).eq_of_le hq.isPrime.ne_top hle
  obtain ⟨-, ubar, hubar⟩ := isAssociatedPrime_iff.mp hq
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ ubar
  have hu0 : (Submodule.Quotient.mk u : QuotSMulTop θ N) ≠ 0 := by
    intro h
    apply hq.isPrime.ne_top
    rw [hubar, h]
    ext r
    simp [mem_colon_singleton]
  have huN : u ∉ (θ • ⊤ : Submodule A N) :=
    fun h => hu0 ((Submodule.Quotient.mk_eq_zero _).mpr h)
  have hann : ∀ x ∈ maximalIdeal A, x • u ∈ (θ • ⊤ : Submodule A N) := by
    intro x hx
    have hx' : x ∈ (⊥ : Submodule A (QuotSMulTop θ N)).colon {Submodule.Quotient.mk u} := by
      rw [← hubar]
      exact hqm ▸ hx
    rw [mem_colon_singleton, mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hx'
    exact hx'
  obtain ⟨v, -, hv⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp (hann c hcm)
  -- `v ∉ cN`
  have hvN : v ∉ (c • ⊤ : Submodule A N) := by
    intro hvc
    obtain ⟨z, -, hz⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hvc
    apply huN
    have h1 : c • (θ • z) = c • u := by rw [smul_comm, hz, hv]
    rw [← hc h1]
    exact smul_mem_pointwise_smul _ _ _ mem_top
  -- `𝔪 • v ⊆ cN`
  have hvm : ∀ x ∈ maximalIdeal A, x • v ∈ (c • ⊤ : Submodule A N) := by
    intro x hx
    obtain ⟨w, -, hw⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp (hann x hx)
    have h1 : θ • (x • v) = θ • (c • w) := by
      calc θ • (x • v) = x • (θ • v) := smul_comm θ x v
        _ = x • (c • u) := by rw [hv]
        _ = c • (x • u) := smul_comm x c u
        _ = c • (θ • w) := by rw [hw]
        _ = θ • (c • w) := smul_comm c θ w
    rw [hθ h1]
    exact smul_mem_pointwise_smul _ _ _ mem_top
  -- conclusion
  intro r hr hreg
  have h1 : r • (Submodule.Quotient.mk v : QuotSMulTop c N) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hvm r hr
  have h2 : (Submodule.Quotient.mk v : QuotSMulTop c N) = 0 := by
    apply hreg
    show r • _ = r • 0
    rw [h1, smul_zero]
  exact hvN ((Submodule.Quotient.mk_eq_zero _).mp h2)

end Swap

section Exchange

/-- L5 (equal length / exchange theorem): any weakly regular sequence `ψ` on `M`
with entries in `𝔪` is at most as long as any maximal sequence `rs` on `M`. -/
theorem length_le_of_isMaximalSeq :
    ∀ (n : ℕ) {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [Nontrivial M] {rs ψ : List A}, rs.length = n →
      (∀ r ∈ rs, r ∈ maximalIdeal A) → (∀ r ∈ ψ, r ∈ maximalIdeal A) →
      IsMaximalSeq M rs → IsWeaklyRegular M ψ → ψ.length ≤ rs.length := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ _ rs ψ hlen hrsm hψm hmax hψ
    rcases ψ with _ | ⟨a, ψ⟩
    · simp
    exfalso
    rcases rs with _ | ⟨b, rs⟩
    · have hareg : IsSMulRegular M a := ((isWeaklyRegular_cons_iff M a ψ).mp hψ).1
      have ham : a ∈ maximalIdeal A := hψm a List.mem_cons_self
      apply hmax.2 a ham
      have e : (M ⧸ (Ideal.ofList ([] : List A) • ⊤ : Submodule A M)) ≃ₗ[A] M :=
        Submodule.quotEquivOfEqBot _ (by simp)
      exact (e.isSMulRegular_congr a).mpr hareg
    · simp at hlen
  | succ n ih =>
    intro M _ _ _ _ rs ψ hlen hrsm hψm hmax hψ
    rcases eq_or_ne ψ [] with rfl | hψne
    · simp
    have hrsne : rs ≠ [] := by rintro rfl; simp at hlen
    -- decompositions
    have hrssplit : rs.dropLast ++ [rs.getLast hrsne] = rs :=
      List.dropLast_append_getLast hrsne
    have hψsplit : ψ.dropLast ++ [ψ.getLast hψne] = ψ :=
      List.dropLast_append_getLast hψne
    have hrs'len : rs.dropLast.length = n := by
      rw [List.length_dropLast, hlen, Nat.add_sub_cancel]
    have hψpos : 0 < ψ.length := List.length_pos_of_ne_nil hψne
    have hrs'm : ∀ r ∈ rs.dropLast, r ∈ maximalIdeal A :=
      fun r hr => hrsm r (List.dropLast_subset _ hr)
    have hψ'm : ∀ r ∈ ψ.dropLast, r ∈ maximalIdeal A :=
      fun r hr => hψm r (List.dropLast_subset _ hr)
    have hθm : rs.getLast hrsne ∈ maximalIdeal A := hrsm _ (List.getLast_mem hrsne)
    haveI : IsNoetherian A M := isNoetherian_of_isNoetherianRing_of_finite A M
    -- the finite family of obstructing primes
    have hnotsub : ¬ ((maximalIdeal A : Set A) ⊆
        ⋃ p ∈ ((⋃ i ∈ Set.Iio (n+1), associatedPrimes A
            (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule A M))) ∪
          (⋃ i ∈ Set.Iio ψ.length, associatedPrimes A
            (M ⧸ (Ideal.ofList (ψ.take i) • ⊤ : Submodule A M)))), (p : Set A)) := by
      intro hsub
      have hUfin : ((⋃ i ∈ Set.Iio (n+1), associatedPrimes A
          (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule A M))) ∪
        (⋃ i ∈ Set.Iio ψ.length, associatedPrimes A
          (M ⧸ (Ideal.ofList (ψ.take i) • ⊤ : Submodule A M)))).Finite :=
        Set.Finite.union
          (Set.Finite.biUnion (Set.finite_Iio _) fun i _ => associatedPrimes.finite A _)
          (Set.Finite.biUnion (Set.finite_Iio _) fun i _ => associatedPrimes.finite A _)
      have hprime : ∀ p ∈ ((⋃ i ∈ Set.Iio (n+1), associatedPrimes A
          (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule A M))) ∪
        (⋃ i ∈ Set.Iio ψ.length, associatedPrimes A
          (M ⧸ (Ideal.ofList (ψ.take i) • ⊤ : Submodule A M)))), p.IsPrime := by
        rintro p (hp | hp) <;>
          · obtain ⟨i, -, hpi⟩ := Set.mem_iUnion₂.mp hp
            exact hpi.isPrime
      obtain ⟨p, hpU, hle⟩ :=
        (Ideal.subset_union_prime_finite hUfin (f := id) ⊥ ⊥
          (fun i hi _ _ => hprime i hi)).mp hsub
      rcases hpU with hp | hp
      · obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp hp
        have hilen : i < rs.length := by rw [hlen]; exact hi
        exact notMem_of_isSMulRegular (hmax.1.regular_mod_prev i hilen) hpi
          (hle (hrsm _ (List.getElem_mem hilen)))
      · obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp hp
        exact notMem_of_isSMulRegular (hψ.regular_mod_prev i hi) hpi
          (hle (hψm _ (List.getElem_mem hi)))
    obtain ⟨c, hcm', hcU⟩ := Set.not_subset.mp hnotsub
    have hcm : c ∈ maximalIdeal A := hcm'
    -- `c` is regular on all the intermediate quotients
    have hcreg : ∀ i < n + 1,
        IsSMulRegular (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule A M)) c := by
      intro i hi
      have hnot : c ∉ ⋃ p ∈ associatedPrimes A
          (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule A M)), (p : Set A) := by
        intro hcmem
        apply hcU
        obtain ⟨p, hp, hcp⟩ := Set.mem_iUnion₂.mp hcmem
        exact Set.mem_biUnion (Set.mem_union_left _ (Set.mem_biUnion hi hp)) hcp
      rw [biUnion_associatedPrimes_eq_compl_regular] at hnot
      simpa using hnot
    have hcregψ : ∀ i < ψ.length,
        IsSMulRegular (M ⧸ (Ideal.ofList (ψ.take i) • ⊤ : Submodule A M)) c := by
      intro i hi
      have hnot : c ∉ ⋃ p ∈ associatedPrimes A
          (M ⧸ (Ideal.ofList (ψ.take i) • ⊤ : Submodule A M)), (p : Set A) := by
        intro hcmem
        apply hcU
        obtain ⟨p, hp, hcp⟩ := Set.mem_iUnion₂.mp hcmem
        exact Set.mem_biUnion (Set.mem_union_right _ (Set.mem_biUnion hi hp)) hcp
      rw [biUnion_associatedPrimes_eq_compl_regular] at hnot
      simpa using hnot
    -- `rs.dropLast` is weakly regular on `M`, its last entry regular on `N`
    have hsplit_reg := (isWeaklyRegular_append_iff M rs.dropLast [rs.getLast hrsne]).mp
      (by rw [hrssplit]; exact hmax.1)
    have hrs'reg : IsWeaklyRegular M rs.dropLast := hsplit_reg.1
    have hθreg : IsSMulRegular
        (M ⧸ (Ideal.ofList rs.dropLast • ⊤ : Submodule A M)) (rs.getLast hrsne) :=
      (isWeaklyRegular_singleton_iff _ _).mp hsplit_reg.2
    have htake_rs : rs.take n = rs.dropLast := by
      rw [List.dropLast_eq_take, hlen, Nat.add_sub_cancel]
    have hcregN : IsSMulRegular (M ⧸ (Ideal.ofList rs.dropLast • ⊤ : Submodule A M)) c := by
      have := hcreg n (by omega)
      rwa [htake_rs] at this
    -- `N` is nontrivial
    haveI hNnt : Nontrivial (M ⧸ (Ideal.ofList rs.dropLast • ⊤ : Submodule A M)) :=
      Submodule.Quotient.nontrivial_iff.mpr (Ne.symm
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (le_trans (Ideal.span_le.mpr fun r hr => hrs'm r hr)
            (maximalIdeal_le_jacobson _))))
    -- transport maximality of `rs` to `QuotSMulTop θ N`
    have hmaxθN : ∀ r ∈ maximalIdeal A, ¬ IsSMulRegular
        (QuotSMulTop (rs.getLast hrsne)
          (M ⧸ (Ideal.ofList rs.dropLast • ⊤ : Submodule A M))) r := by
      intro r hr hreg
      apply hmax.2 r hr
      have e := quotConcatEquiv M rs.dropLast (rs.getLast hrsne)
      rw [hrssplit] at e
      exact (e.isSMulRegular_congr r).mpr hreg
    -- swap the last entry for `c`
    have hswap := swap_last hθm hcm hθreg hcregN hmaxθN
    -- `rs.dropLast ++ [c]` is weakly regular on `M`; permute to `c :: rs.dropLast`
    have hconcatreg : IsWeaklyRegular M (rs.dropLast ++ [c]) :=
      (isWeaklyRegular_append_iff M rs.dropLast [c]).mpr
        ⟨hrs'reg, (isWeaklyRegular_singleton_iff _ _).mpr hcregN⟩
    have hconsreg : IsWeaklyRegular M (c :: rs.dropLast) :=
      IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hconcatreg
        (List.perm_append_singleton c rs.dropLast)
        (fun r hr => by
          rcases List.mem_append.mp hr with h | h
          · exact hrs'm r h
          · exact (List.mem_singleton.mp h) ▸ hcm)
    obtain ⟨hcregM, hrs'regQ⟩ := (isWeaklyRegular_cons_iff M c rs.dropLast).mp hconsreg
    -- maximality of `rs.dropLast` on `QuotSMulTop c M`
    have hquotmax : ∀ r ∈ maximalIdeal A, ¬ IsSMulRegular
        ((QuotSMulTop c M) ⧸
          (Ideal.ofList rs.dropLast • ⊤ : Submodule A (QuotSMulTop c M))) r := by
      intro r hr hreg
      apply hswap r hr
      have e1 := (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M c rs.dropLast).symm
      have e2 : (M ⧸ (Ideal.ofList (c :: rs.dropLast) • ⊤ : Submodule A M)) ≃ₗ[A]
          QuotSMulTop c (M ⧸ (Ideal.ofList rs.dropLast • ⊤ : Submodule A M)) :=
        Submodule.quotEquivOfEq _ _ (by rw [ofList_append_singleton]) ≪≫ₗ
          quotConcatEquiv M rs.dropLast c
      exact ((e1 ≪≫ₗ e2).isSMulRegular_congr r).mp hreg
    haveI : Nontrivial (QuotSMulTop c M) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal M hcm
    have hmax' : IsMaximalSeq (QuotSMulTop c M) rs.dropLast := ⟨hrs'regQ, hquotmax⟩
    -- the `ψ` side
    have hψ'reg : IsWeaklyRegular M ψ.dropLast :=
      ((isWeaklyRegular_append_iff M ψ.dropLast [ψ.getLast hψne]).mp
        (by rw [hψsplit]; exact hψ)).1
    have htake_ψ : ψ.take (ψ.length - 1) = ψ.dropLast := List.dropLast_eq_take.symm
    have hcregψN : IsSMulRegular (M ⧸ (Ideal.ofList ψ.dropLast • ⊤ : Submodule A M)) c := by
      have := hcregψ (ψ.length - 1) (by omega)
      rwa [htake_ψ] at this
    have hψconcat : IsWeaklyRegular M (ψ.dropLast ++ [c]) :=
      (isWeaklyRegular_append_iff M ψ.dropLast [c]).mpr
        ⟨hψ'reg, (isWeaklyRegular_singleton_iff _ _).mpr hcregψN⟩
    have hψcons : IsWeaklyRegular M (c :: ψ.dropLast) :=
      IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hψconcat
        (List.perm_append_singleton c ψ.dropLast)
        (fun r hr => by
          rcases List.mem_append.mp hr with h | h
          · exact hψ'm r h
          · exact (List.mem_singleton.mp h) ▸ hcm)
    have hψ'regQ : IsWeaklyRegular (QuotSMulTop c M) ψ.dropLast :=
      ((isWeaklyRegular_cons_iff M c ψ.dropLast).mp hψcons).2
    -- induction hypothesis
    have hIH := ih hrs'len hrs'm hψ'm hmax' hψ'regQ
    rw [List.length_dropLast, List.length_dropLast] at hIH
    omega

end Exchange

section Main

/-- The stagewise regularity claim inside L6: assuming `rs.take k` is already
weakly regular, the next entry `rs[k]` is regular on `A ⧸ (rs.take k)`. -/
private lemma stage_regular {ws rs : List A}
    (hws : ∀ w ∈ ws, w ∈ maximalIdeal A) (hwreg : IsWeaklyRegular A ws)
    (hrs : ∀ r ∈ rs, r ∈ maximalIdeal A) (hlen : ws.length = rs.length)
    (hdim : ringKrullDim (A ⧸ Ideal.ofList rs) ≤ 0)
    {k : ℕ} (hk : k < rs.length) (hprev : IsWeaklyRegular A (rs.take k)) :
    IsSMulRegular (A ⧸ (Ideal.ofList (rs.take k) • ⊤ : Submodule A A)) rs[k] := by
  classical
  by_contra hreg
  have htakem : ∀ r ∈ rs.take k, r ∈ maximalIdeal A :=
    fun r hr => hrs r (List.take_subset k rs hr)
  -- an associated prime `q` of `A ⧸ (rs.take k)` containing `rs[k]`
  have hmem2 : rs[k] ∈ ⋃ p ∈ associatedPrimes A
      (A ⧸ (Ideal.ofList (rs.take k) • ⊤ : Submodule A A)), (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hreg
  obtain ⟨q, hq, hrq⟩ := Set.mem_iUnion₂.mp hmem2
  have hIann : Ideal.ofList (rs.take k) ≤
      (⊤ : Submodule A (A ⧸ (Ideal.ofList (rs.take k) • ⊤ : Submodule A A))).annihilator := by
    intro x hx
    rw [Submodule.mem_annihilator]
    intro m _
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hx mem_top
  have hqI : Ideal.ofList (rs.take k) ≤ q :=
    le_trans hIann (IsAssociatedPrime.annihilator_le hq)
  have htake : rs.take (k+1) = rs.take k ++ [rs[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    rfl
  have hq1 : Ideal.ofList (rs.take (k+1)) ≤ q := by
    rw [htake, Ideal.ofList_append]
    refine sup_le hqI ?_
    rw [Ideal.ofList_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hrq
  -- (α) lower bound: `rs.length - k ≤ dim (A ⧸ q)`
  obtain ⟨e, hem, hemax⟩ := exists_isMaximalSeq_extension (M := A) hws hwreg
  obtain ⟨f, hfm, hfmax⟩ := exists_isMaximalSeq_extension (M := A) htakem hprev
  have h51 := length_le_of_isMaximalSeq (rs.take k ++ f).length rfl
    (fun r hr => (List.mem_append.mp hr).elim (htakem r) (hfm r))
    (fun r hr => (List.mem_append.mp hr).elim (hws r) (hem r))
    hfmax hemax.1
  have hktake : (rs.take k).length = k := by
    rw [List.length_take]
    omega
  have hflen : rs.length - k ≤ f.length := by
    rw [List.length_append, List.length_append, hktake] at h51
    omega
  have hfreg : IsWeaklyRegular (A ⧸ (Ideal.ofList (rs.take k) • ⊤ : Submodule A A)) f :=
    ((isWeaklyRegular_append_iff A (rs.take k) f).mp hfmax.1).2
  have hα : (f.length : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) :=
    cast_length_le_ringKrullDim_quotient hfm hfreg hq
  -- (β) upper bound: `dim (A ⧸ q) ≤ rs.length - (k+1)`
  have hβ1 : ringKrullDim (A ⧸ q) ≤ ringKrullDim (A ⧸ Ideal.ofList (rs.take (k+1))) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hq1)
      (Ideal.Quotient.factor_surjective hq1)
  haveI hBnt : Nontrivial (A ⧸ Ideal.ofList (rs.take (k+1))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top (maximalIdeal.isMaximal A))
        (Ideal.span_le.mpr fun r hr => hrs r (List.take_subset _ _ hr)))
  haveI hBloc : IsLocalRing (A ⧸ Ideal.ofList (rs.take (k+1))) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI hBhom : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList (rs.take (k+1)))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hsjac : ((((rs.drop (k+1)).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take (k+1))))).toFinset : Finset _) : Set _) ⊆
      (↑(Ring.jacobson (A ⧸ Ideal.ofList (rs.take (k+1)))) :
        Set (A ⧸ Ideal.ofList (rs.take (k+1)))) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    intro b hb
    rw [Finset.mem_coe, List.mem_toFinset] at hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact mem_nonunits_iff.mp
      ((IsLocalRing.mem_maximalIdeal _).mp (hrs x (List.drop_subset _ _ hx)))
      (IsUnit.of_map _ x hu)
  have hβ2 := ringKrullDim_le_ringKrullDim_quotient_add_card
    ((rs.drop (k+1)).map (Ideal.Quotient.mk (Ideal.ofList (rs.take (k+1))))).toFinset hsjac
  have hspan : Ideal.span ((((rs.drop (k+1)).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take (k+1))))).toFinset : Finset _) :
        Set (A ⧸ Ideal.ofList (rs.take (k+1)))) =
      (Ideal.ofList (rs.drop (k+1))).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take (k+1)))) := by
    rw [List.coe_toFinset, Ideal.map_ofList]
  have hsup : Ideal.ofList (rs.take (k+1)) ⊔ Ideal.ofList (rs.drop (k+1)) =
      Ideal.ofList rs := by
    rw [← Ideal.ofList_append, List.take_append_drop]
  have hdim2 : ringKrullDim ((A ⧸ Ideal.ofList (rs.take (k+1))) ⧸ Ideal.span
      ((((rs.drop (k+1)).map (Ideal.Quotient.mk (Ideal.ofList (rs.take (k+1))))).toFinset :
        Finset _) : Set (A ⧸ Ideal.ofList (rs.take (k+1))))) =
      ringKrullDim (A ⧸ Ideal.ofList rs) := by
    rw [hspan, ringKrullDim_eq_of_ringEquiv
      (DoubleQuot.quotQuotEquivQuotSup (Ideal.ofList (rs.take (k+1)))
        (Ideal.ofList (rs.drop (k+1)))), hsup]
  have hcard : (((rs.drop (k+1)).map
      (Ideal.Quotient.mk (Ideal.ofList (rs.take (k+1))))).toFinset).card ≤
      rs.length - (k+1) := by
    refine le_trans (List.toFinset_card_le _) ?_
    simp [List.length_drop]
  have hβ : ringKrullDim (A ⧸ q) ≤ ((rs.length - (k+1) : ℕ) : WithBot ℕ∞) := by
    refine hβ1.trans (hβ2.trans ?_)
    rw [hdim2]
    have h0 : ((((rs.drop (k+1)).map
        (Ideal.Quotient.mk (Ideal.ofList (rs.take (k+1))))).toFinset.card : ℕ) :
          WithBot ℕ∞) ≤ ((rs.length - (k+1) : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast hcard
    have hstep := add_le_add hdim h0
    rwa [zero_add] at hstep
  -- (γ) contradiction
  have hγ : ((rs.length - k : ℕ) : WithBot ℕ∞) ≤ ((rs.length - (k+1) : ℕ) : WithBot ℕ∞) :=
    le_trans (le_trans (by exact_mod_cast hflen) hα) hβ
  have hfin : (rs.length - k : ℕ) ≤ rs.length - (k+1) := by exact_mod_cast hγ
  omega

/-- **L6, main theorem**: over a Noetherian local ring `A`, if some weakly
regular sequence `ws` of length `n` (entries in `𝔪`) exists, then any list `rs`
of `n` elements of `𝔪` with `dim (A ⧸ (rs)) ≤ 0` is itself weakly regular. -/
theorem isWeaklyRegular_of_dim_quotient_le (ws rs : List A)
    (hws : ∀ w ∈ ws, w ∈ IsLocalRing.maximalIdeal A) (hwreg : IsWeaklyRegular A ws)
    (hrs : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal A) (hlen : ws.length = rs.length)
    (hdim : ringKrullDim (A ⧸ Ideal.ofList rs) ≤ 0) :
    IsWeaklyRegular A rs := by
  have key : ∀ k, k ≤ rs.length → IsWeaklyRegular A (rs.take k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using IsWeaklyRegular.nil A A
    | succ k ihk =>
      intro hk1
      have hk : k < rs.length := hk1
      have hprev := ihk hk.le
      have htake : rs.take (k+1) = rs.take k ++ [rs[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]
        rfl
      rw [htake, isWeaklyRegular_append_iff]
      exact ⟨hprev, (isWeaklyRegular_singleton_iff _ _).mpr
        (stage_regular hws hwreg hrs hlen hdim hk hprev)⟩
  have h := key rs.length le_rfl
  rwa [List.take_length] at h

end Main

end WeakBezout
