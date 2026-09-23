/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.WeakBezout.GradedDim

/-! # Weak Bezout: degeneration to leading forms

Let `p₁, …, pₙ ∈ k[X₁, …, Xₙ]` with `totalDegree pᵢ ≤ dᵢ` and let `Lᵢ` be the degree-`dᵢ`
homogeneous component of `pᵢ` (its "leading form"). Assume that every homogeneous polynomial of
degree `≥ T` lies in the ideal `J = (L₁, …, Lₙ)`. The main result `finrank_quotient_le` states
that `R ⧸ (p₁, …, pₙ)` is then a finite-dimensional `k`-vector space of dimension at most
`dim_k (R ⧸ J)`.

The proof filters `R ⧸ I` (where `I = (p₁, …, pₙ)`) by the images `lowDegreeImage I t` of the
subspaces of polynomials of total degree `≤ t`, and compares the successive steps of this
filtration with the graded pieces of `R ⧸ J`.  The key point
(`exists_good_representative`) is a "leading-term cancellation": if `f` has total degree `≤ t`
and its degree-`t` component lies in `J`, say `homogeneousComponent t f = ∑ bᵢ * Lᵢ` with `bᵢ`
homogeneous of degree `t - dᵢ`, then `g = f - ∑ bᵢ * pᵢ` is congruent to `f` modulo `I` and has
total degree `< t`.  Consequently each filtration step has dimension at most `hdim J t`, the
filtration stabilizes at `⊤` once the degree passes `T`, and summing over `t` gives the bound
by `dim_k (R ⧸ J) = ∑ t, hdim J t` (the additivity result from `GradedDim`).
-/

namespace WeakBezout

open MvPolynomial

/-! ## Total-degree helpers -/

section DegreeHelpers

variable {σ : Type*} {R : Type*}

/-- If `f` has total degree at most `t` and its degree-`t` homogeneous component vanishes,
then `f` has total degree at most `t - 1`. -/
theorem totalDegree_le_pred [CommSemiring R] {f : MvPolynomial σ R} {t : ℕ}
    (hf : f.totalDegree ≤ t) (h0 : homogeneousComponent t f = 0) :
    f.totalDegree ≤ t - 1 := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro m hm
  have h1 : (m.sum fun _ e => e) ≤ t := le_trans (le_totalDegree hm) hf
  have h2 : m.degree = m.sum fun _ e => e := by
    simp [Finsupp.degree_apply, Finsupp.sum]
  by_contra hcon
  have h4 : m.degree = t := by omega
  have h5 : coeff m f = 0 := by
    have h6 := coeff_homogeneousComponent t f m
    rw [if_pos h4, h0, coeff_zero] at h6
    exact h6.symm
  exact mem_support_iff.mp hm h5

/-- A polynomial of total degree `0` with vanishing degree-`0` component is zero. -/
theorem eq_zero_of_totalDegree_le_zero [CommSemiring R] {f : MvPolynomial σ R}
    (hf : f.totalDegree ≤ 0) (h0 : homogeneousComponent 0 f = 0) : f = 0 := by
  have ht : f.totalDegree = 0 := Nat.le_zero.mp hf
  have hs := sum_homogeneousComponent f
  rw [ht] at hs
  have hs' : homogeneousComponent 0 f = f := by simpa using hs
  exact hs'.symm.trans h0

/-- Subtracting the top homogeneous component drops the total degree. -/
theorem totalDegree_sub_homogeneousComponent [CommRing R] {f : MvPolynomial σ R} {e : ℕ}
    (hf : f.totalDegree ≤ e) :
    (f - homogeneousComponent e f).totalDegree ≤ e - 1 := by
  apply totalDegree_le_pred
  · exact le_trans (totalDegree_sub _ _)
      (max_le hf (homogeneousComponent_isHomogeneous e f).totalDegree_le)
  · rw [map_sub, homogeneousComponent_of_mem (homogeneousComponent_mem e f), if_pos rfl,
      sub_self]

end DegreeHelpers

/-! ## The degree filtration of `R ⧸ I` -/

section Degeneration

variable {n : ℕ} {k : Type*} [Field k]

/-- The `k`-linear map sending a polynomial of total degree `≤ t` to its class in `R ⧸ I`. -/
private noncomputable def repMap (I : Ideal (MvPolynomial (Fin n) k)) (t : ℕ) :
    restrictTotalDegree (Fin n) k t →ₗ[k] MvPolynomial (Fin n) k ⧸ I :=
  (Ideal.Quotient.mkₐ k I).toLinearMap ∘ₗ (restrictTotalDegree (Fin n) k t).subtype

private theorem repMap_apply (I : Ideal (MvPolynomial (Fin n) k)) (t : ℕ)
    (x : restrictTotalDegree (Fin n) k t) :
    repMap I t x = Ideal.Quotient.mk I (x : MvPolynomial (Fin n) k) := rfl

/-- The image in `R ⧸ I` of the space of polynomials of total degree at most `t`,
as a `k`-subspace.  These spaces filter `R ⧸ I`. -/
noncomputable def lowDegreeImage (I : Ideal (MvPolynomial (Fin n) k)) (t : ℕ) :
    Submodule k (MvPolynomial (Fin n) k ⧸ I) :=
  LinearMap.range (repMap I t)

instance (I : Ideal (MvPolynomial (Fin n) k)) (t : ℕ) :
    FiniteDimensional k ↥(lowDegreeImage I t) :=
  inferInstanceAs (FiniteDimensional k ↥(LinearMap.range (repMap I t)))

theorem mem_lowDegreeImage {I : Ideal (MvPolynomial (Fin n) k)} {t : ℕ}
    {x : MvPolynomial (Fin n) k ⧸ I} :
    x ∈ lowDegreeImage I t ↔
      ∃ f : MvPolynomial (Fin n) k, f.totalDegree ≤ t ∧ Ideal.Quotient.mk I f = x := by
  constructor
  · intro hx
    rw [lowDegreeImage, LinearMap.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(y : MvPolynomial (Fin n) k), ?_, (repMap_apply I t y).symm⟩
    have h := y.2
    rwa [mem_restrictTotalDegree] at h
  · rintro ⟨f, hf, rfl⟩
    rw [lowDegreeImage, LinearMap.mem_range]
    exact ⟨⟨f, by rw [mem_restrictTotalDegree]; exact hf⟩, repMap_apply I t _⟩

/-- The subspace preceding `lowDegreeImage I t` in the filtration: `⊥` for `t = 0`,
and `lowDegreeImage I t` for `t + 1`. -/
noncomputable def prevSpace (I : Ideal (MvPolynomial (Fin n) k)) :
    ℕ → Submodule k (MvPolynomial (Fin n) k ⧸ I)
  | 0 => ⊥
  | t + 1 => lowDegreeImage I t

@[simp] theorem prevSpace_succ (I : Ideal (MvPolynomial (Fin n) k)) (t : ℕ) :
    prevSpace I (t + 1) = lowDegreeImage I t := rfl

instance (I : Ideal (MvPolynomial (Fin n) k)) (t : ℕ) :
    FiniteDimensional k ↥(prevSpace I t) :=
  match t with
  | 0 => inferInstanceAs
      (FiniteDimensional k ↥(⊥ : Submodule k (MvPolynomial (Fin n) k ⧸ I)))
  | s + 1 => inferInstanceAs (FiniteDimensional k ↥(lowDegreeImage I s))

/-- The `k`-linear map sending a polynomial of total degree `≤ t` to the class of its
degree-`t` component in the degree-`t` graded piece of `R ⧸ J`. -/
private noncomputable def pieceMap (J : Ideal (MvPolynomial (Fin n) k)) (t : ℕ) :
    restrictTotalDegree (Fin n) k t →ₗ[k]
      (homogeneousSubmodule (Fin n) k t ⧸ idealPiece J t) :=
  (idealPiece J t).mkQ ∘ₗ LinearMap.codRestrict (homogeneousSubmodule (Fin n) k t)
    ((homogeneousComponent t) ∘ₗ (restrictTotalDegree (Fin n) k t).subtype)
    (fun x => homogeneousComponent_mem t (x : MvPolynomial (Fin n) k))

/-! ## The leading-term cancellation argument -/

/-- **Leading-term cancellation.**  If `f` has total degree `≤ t` and its degree-`t`
component lies in the leading-form ideal `J = (L₁, …, Lₙ)`, then subtracting a suitable
combination `∑ bᵢ * pᵢ` of the original polynomials kills the degree-`t` part of `f`
without leaving `f`'s class modulo `I = (p₁, …, pₙ)`. -/
theorem exists_good_representative
    (p : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) {t : ℕ} {f : MvPolynomial (Fin n) k}
    (hf : f.totalDegree ≤ t)
    (hcomp : homogeneousComponent t f ∈
      Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) :
    ∃ g : MvPolynomial (Fin n) k, g.totalDegree ≤ t ∧ homogeneousComponent t g = 0 ∧
      f - g ∈ Ideal.span (Set.range p) := by
  classical
  obtain ⟨c, hcsum⟩ := Ideal.mem_span_range_iff_exists_fun.mp hcomp
  have hcsum' : ∑ i, c i * homogeneousComponent (d i) (p i) = homogeneousComponent t f :=
    hcsum
  -- the homogeneous coefficients of degree `t - dᵢ`
  set b : Fin n → MvPolynomial (Fin n) k :=
    fun i => if d i ≤ t then homogeneousComponent (t - d i) (c i) else 0 with hbdef
  have hbhom : ∀ i, (b i).IsHomogeneous (t - d i) := by
    intro i
    simp only [hbdef]
    split_ifs with hle
    · exact homogeneousComponent_isHomogeneous _ _
    · exact isHomogeneous_zero _ _ _
  -- the degree-`t` component of `f` is `∑ bᵢ * Lᵢ`
  have hsum : ∑ i, b i * homogeneousComponent (d i) (p i) = homogeneousComponent t f := by
    have h1 : homogeneousComponent t (homogeneousComponent t f) = homogeneousComponent t f := by
      rw [homogeneousComponent_of_mem (homogeneousComponent_mem t f), if_pos rfl]
    calc
      ∑ i, b i * homogeneousComponent (d i) (p i)
          = ∑ i, homogeneousComponent t (c i * homogeneousComponent (d i) (p i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : d i ≤ t
        · have h2 := homogeneousComponent_mul_isHomogeneous_right
            (homogeneousComponent_isHomogeneous (d i) (p i)) (c i) (t - d i)
          rw [Nat.sub_add_cancel h] at h2
          rw [h2]
          simp only [hbdef]
          rw [if_pos h]
        · rw [homogeneousComponent_mul_of_lt
            (homogeneousComponent_isHomogeneous (d i) (p i)) (c i) (by omega)]
          simp only [hbdef]
          rw [if_neg h, zero_mul]
      _ = homogeneousComponent t (∑ i, c i * homogeneousComponent (d i) (p i)) :=
        (map_sum _ _ _).symm
      _ = homogeneousComponent t f := by rw [hcsum', h1]
  -- the degree-`t` component of `bᵢ * pᵢ` is exactly `bᵢ * Lᵢ`
  have hcompi : ∀ i, homogeneousComponent t (b i * p i)
      = b i * homogeneousComponent (d i) (p i) := by
    intro i
    by_cases h : d i ≤ t
    · have hsplit : b i * p i
          = b i * homogeneousComponent (d i) (p i)
            + b i * (p i - homogeneousComponent (d i) (p i)) := by ring
      rw [hsplit, map_add]
      have hbLhom : (b i * homogeneousComponent (d i) (p i)).IsHomogeneous t := by
        have h3 := (hbhom i).mul (homogeneousComponent_isHomogeneous (d i) (p i))
        rwa [Nat.sub_add_cancel h] at h3
      have h1 : homogeneousComponent t (b i * homogeneousComponent (d i) (p i))
          = b i * homogeneousComponent (d i) (p i) := by
        rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hbLhom),
          if_pos rfl]
      have h2 : homogeneousComponent t (b i * (p i - homogeneousComponent (d i) (p i)))
          = 0 := by
        rcases Nat.eq_zero_or_pos (d i) with hd0 | hd0
        · have hp0 : (p i).totalDegree = 0 := Nat.le_zero.mp (hd0 ▸ hdeg i)
          have hself : homogeneousComponent 0 (p i) = p i := by
            have hs := sum_homogeneousComponent (p i)
            rw [hp0] at hs
            simpa using hs
          have hpc : p i - homogeneousComponent (d i) (p i) = 0 := by
            rw [hd0, hself, sub_self]
          rw [hpc, mul_zero, map_zero]
        · apply homogeneousComponent_eq_zero
          have hb1 : (b i).totalDegree ≤ t - d i := (hbhom i).totalDegree_le
          have hp1 : (p i - homogeneousComponent (d i) (p i)).totalDegree ≤ d i - 1 :=
            totalDegree_sub_homogeneousComponent (hdeg i)
          have h4 := totalDegree_mul (b i) (p i - homogeneousComponent (d i) (p i))
          omega
      rw [h1, h2, add_zero]
    · have hb0 : b i = 0 := by
        simp only [hbdef]
        rw [if_neg h]
      rw [hb0, zero_mul, zero_mul, map_zero]
  refine ⟨f - ∑ i, b i * p i, ?_, ?_, ?_⟩
  · -- total degree stays `≤ t`
    refine le_trans (totalDegree_sub _ _) (max_le hf ?_)
    refine totalDegree_finsetSum_le fun i _ => ?_
    by_cases h : d i ≤ t
    · refine le_trans (totalDegree_mul _ _) ?_
      have hb1 : (b i).totalDegree ≤ t - d i := (hbhom i).totalDegree_le
      have hp1 := hdeg i
      omega
    · have hb0 : b i = 0 := by
        simp only [hbdef]
        rw [if_neg h]
      simp [hb0]
  · -- the degree-`t` component vanishes
    rw [map_sub, map_sum, Finset.sum_congr rfl fun i _ => hcompi i, hsum, sub_self]
  · -- the difference lies in `I`
    have h5 : f - (f - ∑ i, b i * p i) = ∑ i, b i * p i := by ring
    rw [h5]
    exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- If `f` has total degree `≤ t` and its degree-`t` component lies in the leading-form
ideal, then the class of `f` in `R ⧸ I` already lies in the previous filtration step. -/
theorem mk_mem_prevSpace
    (p : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) {t : ℕ} {f : MvPolynomial (Fin n) k}
    (hf : f.totalDegree ≤ t)
    (hcomp : homogeneousComponent t f ∈
      Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) :
    Ideal.Quotient.mk (Ideal.span (Set.range p)) f
      ∈ prevSpace (Ideal.span (Set.range p)) t := by
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_good_representative p d hdeg hf hcomp
  have hmk : Ideal.Quotient.mk (Ideal.span (Set.range p)) f
      = Ideal.Quotient.mk (Ideal.span (Set.range p)) g := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hg3
  cases t with
  | zero =>
    have hg0 : g = 0 := eq_zero_of_totalDegree_le_zero hg1 hg2
    rw [hmk, hg0, map_zero]
    exact Submodule.zero_mem _
  | succ s =>
    rw [hmk, prevSpace_succ, mem_lowDegreeImage]
    refine ⟨g, ?_, rfl⟩
    have h1 := totalDegree_le_pred hg1 hg2
    omega

/-! ## Dimension count along the filtration -/

/-- **Filtration step bound.**  If every polynomial of degree `≤ t` whose top component lies
in `J` is congruent modulo `I` to a polynomial of lower degree, then the `t`-th filtration
step of `R ⧸ I` grows by at most the dimension `hdim J t` of the degree-`t` graded piece of
`R ⧸ J`. -/
theorem finrank_lowDegreeImage_le (I J : Ideal (MvPolynomial (Fin n) k)) (t : ℕ)
    (hIJ : ∀ f : MvPolynomial (Fin n) k, f.totalDegree ≤ t →
      homogeneousComponent t f ∈ J → Ideal.Quotient.mk I f ∈ prevSpace I t) :
    Module.finrank k ↥(lowDegreeImage I t) ≤
      Module.finrank k ↥(prevSpace I t) + hdim J t := by
  classical
  set ψ : restrictTotalDegree (Fin n) k t →ₗ[k]
      (MvPolynomial (Fin n) k ⧸ I) ⧸ prevSpace I t :=
    (prevSpace I t).mkQ ∘ₗ repMap I t with hψdef
  -- the kernel of the piece map is contained in the kernel of the quotient map
  have hker : LinearMap.ker (pieceMap J t) ≤ LinearMap.ker ψ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hx' : homogeneousComponent t (x : MvPolynomial (Fin n) k) ∈ J := by
      have h1 : pieceMap J t x = Submodule.Quotient.mk
          (⟨homogeneousComponent t (x : MvPolynomial (Fin n) k),
            homogeneousComponent_mem t (x : MvPolynomial (Fin n) k)⟩ :
            homogeneousSubmodule (Fin n) k t) := rfl
      rw [h1, Submodule.Quotient.mk_eq_zero] at hx
      exact hx
    have hxdeg : (x : MvPolynomial (Fin n) k).totalDegree ≤ t := by
      have h2 := x.2
      rwa [mem_restrictTotalDegree] at h2
    have hmem := hIJ _ hxdeg hx'
    rw [hψdef, LinearMap.comp_apply, repMap_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hmem
  -- rank-nullity on the common domain
  have hd1 := LinearMap.finrank_range_add_finrank_ker ψ
  have hd2 := LinearMap.finrank_range_add_finrank_ker (pieceMap J t)
  have hd3 : Module.finrank k ↥(LinearMap.ker (pieceMap J t)) ≤
      Module.finrank k ↥(LinearMap.ker ψ) :=
    Submodule.finrank_mono hker
  have hd5 : Module.finrank k ↥(LinearMap.range (pieceMap J t)) ≤ hdim J t :=
    Submodule.finrank_le _
  -- decompose `lowDegreeImage I t` through the quotient by `prevSpace I t`
  have hq1 := LinearMap.finrank_range_add_finrank_ker
    ((prevSpace I t).mkQ ∘ₗ (lowDegreeImage I t).subtype)
  have hrq : LinearMap.range ((prevSpace I t).mkQ ∘ₗ (lowDegreeImage I t).subtype)
      = LinearMap.range ψ := by
    rw [hψdef, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hrq' : Module.finrank k ↥(LinearMap.range ((prevSpace I t).mkQ ∘ₗ
      (lowDegreeImage I t).subtype)) = Module.finrank k ↥(LinearMap.range ψ) := by
    rw [hrq]
  have hkq : Module.finrank k ↥(LinearMap.ker ((prevSpace I t).mkQ ∘ₗ
      (lowDegreeImage I t).subtype)) ≤ Module.finrank k ↥(prevSpace I t) := by
    have hkeq : LinearMap.ker ((prevSpace I t).mkQ ∘ₗ (lowDegreeImage I t).subtype)
        = Submodule.comap (lowDegreeImage I t).subtype
            (lowDegreeImage I t ⊓ prevSpace I t) := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      ext x
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [hkeq, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)]
    exact Submodule.finrank_mono inf_le_right
  omega

/-- Summing the filtration step bounds: the `t`-th filtration step of `R ⧸ I` has dimension
at most `∑_{s ≤ t} hdim J s`. -/
theorem finrank_lowDegreeImage_le_sum
    (p : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) (t : ℕ) :
    Module.finrank k ↥(lowDegreeImage (Ideal.span (Set.range p)) t) ≤
      ∑ s ∈ Finset.range (t + 1),
        hdim (Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) s := by
  induction t with
  | zero =>
    have h := finrank_lowDegreeImage_le (Ideal.span (Set.range p))
      (Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) 0
      (fun f hf hcomp => mk_mem_prevSpace p d hdeg hf hcomp)
    have h0 : Module.finrank k ↥(prevSpace (Ideal.span (Set.range p)) 0) = 0 := by
      have e : Module.finrank k ↥(prevSpace (Ideal.span (Set.range p)) 0)
          = Module.finrank k ↥(⊥ : Submodule k
              (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p))) := rfl
      rw [e, finrank_bot]
    rw [h0] at h
    simpa using h
  | succ s ih =>
    have h := finrank_lowDegreeImage_le (Ideal.span (Set.range p))
      (Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) (s + 1)
      (fun f hf hcomp => mk_mem_prevSpace p d hdeg hf hcomp)
    have h0 : Module.finrank k ↥(prevSpace (Ideal.span (Set.range p)) (s + 1))
        = Module.finrank k ↥(lowDegreeImage (Ideal.span (Set.range p)) s) := rfl
    rw [Finset.sum_range_succ]
    omega

/-! ## Stabilization of the filtration -/

/-- Once every homogeneous polynomial of the current degree lies in the leading-form ideal,
the filtration stops growing. -/
theorem lowDegreeImage_le_pred
    (p : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) {T t : ℕ}
    (hT : ∀ s, T ≤ s → homogeneousSubmodule (Fin n) k s ≤
      Submodule.restrictScalars k
        (Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))))
    (htT : T ≤ t) (ht1 : 1 ≤ t) :
    lowDegreeImage (Ideal.span (Set.range p)) t ≤
      lowDegreeImage (Ideal.span (Set.range p)) (t - 1) := by
  intro x hx
  rw [mem_lowDegreeImage] at hx
  obtain ⟨f, hf, rfl⟩ := hx
  have hcomp : homogeneousComponent t f ∈
      Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i)) := by
    have h := hT t htT (homogeneousComponent_mem t f)
    simpa using h
  have hmem := mk_mem_prevSpace p d hdeg hf hcomp
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [prevSpace_succ] at hmem
  simpa using hmem

/-- The filtration reaches `⊤` at degree `max T 1 - 1`. -/
theorem lowDegreeImage_eq_top
    (p : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) (T : ℕ)
    (hT : ∀ s, T ≤ s → homogeneousSubmodule (Fin n) k s ≤
      Submodule.restrictScalars k
        (Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i)))) :
    lowDegreeImage (Ideal.span (Set.range p)) (max T 1 - 1) = ⊤ := by
  have hT1 : 1 ≤ max T 1 := le_max_right _ _
  have hTT : T ≤ max T 1 := le_max_left _ _
  have key : ∀ m, lowDegreeImage (Ideal.span (Set.range p)) (max T 1 - 1 + m) ≤
      lowDegreeImage (Ideal.span (Set.range p)) (max T 1 - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ s ih =>
      refine le_trans ?_ ih
      have h := lowDegreeImage_le_pred p d hdeg hT
        (t := max T 1 - 1 + s + 1) (by omega) (by omega)
      have e1 : max T 1 - 1 + (s + 1) = max T 1 - 1 + s + 1 := by omega
      rw [e1]
      simpa using h
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : Ideal.Quotient.mk (Ideal.span (Set.range p)) f ∈
      lowDegreeImage (Ideal.span (Set.range p))
        (max T 1 - 1 + (f.totalDegree - (max T 1 - 1))) := by
    rw [mem_lowDegreeImage]
    exact ⟨f, by omega, rfl⟩
  exact key _ h1

/-! ## The main theorem -/

/-- **Degeneration to leading forms.**  Let `p₁, …, pₙ ∈ k[X₁, …, Xₙ]` with
`totalDegree pᵢ ≤ dᵢ`, let `Lᵢ` be the degree-`dᵢ` homogeneous component of `pᵢ`, and assume
that every homogeneous polynomial of degree `≥ T` lies in `J = (L₁, …, Lₙ)`.  Then
`R ⧸ (p₁, …, pₙ)` is finite-dimensional over `k`, of dimension at most `dim_k (R ⧸ J)`. -/
theorem finrank_quotient_le (p : Fin n → MvPolynomial (Fin n) k) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) (T : ℕ)
    (hT : ∀ t, T ≤ t → homogeneousSubmodule (Fin n) k t ≤
      Submodule.restrictScalars k
        (Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i)))) :
    FiniteDimensional k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p)) ∧
      Module.finrank k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p)) ≤
        Module.finrank k (MvPolynomial (Fin n) k ⧸
          Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) := by
  classical
  have htop := lowDegreeImage_eq_top p d hdeg T hT
  have hfin : FiniteDimensional k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p)) := by
    haveI h1 : FiniteDimensional k
        ↥(⊤ : Submodule k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p))) := by
      rw [← htop]
      infer_instance
    exact Module.Finite.equiv Submodule.topEquiv
  refine ⟨hfin, ?_⟩
  have hfr : Module.finrank k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range p))
      = Module.finrank k ↥(lowDegreeImage (Ideal.span (Set.range p)) (max T 1 - 1)) := by
    rw [htop, finrank_top]
  have hsum := finrank_lowDegreeImage_le_sum p d hdeg (max T 1 - 1)
  haveI hJfin : FiniteDimensional k (MvPolynomial (Fin n) k ⧸
      Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i))) :=
    finiteDimensional_quotient _ T hT
  have hJeq := finrank_quotient_eq_sum_hdim
    (Ideal.span (Set.range fun i => homogeneousComponent (d i) (p i)))
    (Set.range fun i => homogeneousComponent (d i) (p i))
    (fun f hf => by
      obtain ⟨i, rfl⟩ := hf
      exact ⟨d i, homogeneousComponent_isHomogeneous _ _⟩)
    rfl (max T 1)
    (fun t ht => hT t (le_trans (le_max_left _ _) ht))
  have hT1 : 1 ≤ max T 1 := le_max_right _ _
  have hrange : max T 1 - 1 + 1 = max T 1 := by omega
  rw [hrange] at hsum
  rw [hfr, hJeq]
  exact hsum

end Degeneration

end WeakBezout
