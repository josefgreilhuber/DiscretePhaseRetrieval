/-
Copyright (c) 2026 Josef Greilhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josef Greilhuber
-/
import Mathlib
import Warren.Transversality
import Warren.SignPatterns.Orthant

/-!
# Sign patterns: charging a realised sign pattern to a bounded component

Let `q 1, ..., q m` be polynomials in `n` real variables which are in general position (every
subfamily has linearly independent gradients at every common zero).  Let `σ` be a nowhere-zero
sign pattern which is realised at some point `x₁`, and assume that for *at least one* index `j`
with `σ j = -1` the set `{q j ≤ 0}` is bounded.  (No boundedness is required of the other
polynomials.)

The main result `SignPatterns.exists_charge` produces a nonempty subfamily `J` with `|J| ≤ n` and
a point `x₀` which is a common zero of `(q j)_{j ∈ J}`, such that the connected component of `x₀`
in the joint zero set of `(q j)_{j ∈ J}` is bounded and the signs of the remaining `q k` are
constantly `σ k` on that component.  This is exactly the `charge` hypothesis of
`SignPatterns.card_le_of_charge`.

## Proof outline

Let `G` be the (open) set where no `q j` vanishes, `U := connectedComponentIn G x₁`.

* the sign pattern is constant equal to `σ` on `U` (`sign_eq_on_component`);
* `U` is bounded: for the distinguished index `j` we have `σ j = -1`, so `U ⊆ {q j ≤ 0}`, which
  is bounded by hypothesis;
* hence `F := closure U \ U` is nonempty (otherwise `U` would be clopen in the connected,
  unbounded space `ℝⁿ`), closed and bounded, and `F ∩ G = ∅`;
* choose `x₀ ∈ F` maximising the number of polynomials vanishing at it and let `J` be that set of
  indices; then `1 ≤ |J| ≤ n`;
* the key claim is that the whole connected component `C` of `x₀` in the zero set of
  `(q j)_{j ∈ J}` stays inside `F` and has the same vanishing set `J`.  This is a connectedness
  argument: the local orthant structure `SignPatterns.exists_orthant_nhd` shows that the set of
  such points is open in `C`, while it is closed in `C` because `F` is closed.
-/

open MvPolynomial Set Topology
open AlgebraicTransversality

namespace SignPatterns

variable {n m : ℕ}

/-! ## Preliminaries -/

/-- A nonzero sign is `1` or `-1`. -/
theorem sign_ne_zero_cases {s : SignType} (h : s ≠ 0) : s = 1 ∨ s = -1 := by
  revert h; cases s <;> decide

/-- The set of points at which none of the polynomials `q j` vanishes. -/
def nonvanishing (q : Fin m → MvPolynomial (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ j, eval x (q j) ≠ 0}

theorem isOpen_nonvanishing (q : Fin m → MvPolynomial (Fin n) ℝ) : IsOpen (nonvanishing q) := by
  have h : nonvanishing q = ⋂ j, {x : Fin n → ℝ | eval x (q j) ≠ 0} := by
    ext x; simp [nonvanishing]
  rw [h]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_ne_fun (differentiable_evalPoly (q j)).continuous continuous_const

/-- A point realising a nowhere-zero sign pattern lies in `nonvanishing q`. -/
theorem mem_nonvanishing_of_sign {q : Fin m → MvPolynomial (Fin n) ℝ} {σ : Fin m → SignType}
    (hσ : ∀ j, σ j ≠ 0) {x : Fin n → ℝ} (hx : ∀ j, SignType.sign (eval x (q j)) = σ j) :
    x ∈ nonvanishing q := by
  intro k hk
  refine hσ k ?_
  rw [← hx k, hk, sign_zero]

open scoped Classical in
/-- The set of indices `j` such that `q j` vanishes at `y`. -/
noncomputable def zeroIdx (q : Fin m → MvPolynomial (Fin n) ℝ) (y : Fin n → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun j => eval y (q j) = 0

theorem mem_zeroIdx {q : Fin m → MvPolynomial (Fin n) ℝ} {y : Fin n → ℝ} {j : Fin m} :
    j ∈ zeroIdx q y ↔ eval y (q j) = 0 := by
  unfold zeroIdx
  simp

/-- Under general position, at most `n` of the polynomials can vanish at a given point. -/
theorem card_zeroIdx_le (q : Fin m → MvPolynomial (Fin n) ℝ)
    (hgp : ∀ (x : Fin n → ℝ) (S : Finset (Fin m)), (∀ j ∈ S, eval x (q j) = 0) →
      LinearIndependent ℝ (fun j : S => gradient (q j) x))
    (y : Fin n → ℝ) : (zeroIdx q y).card ≤ n := by
  have hind := hgp y (zeroIdx q y) fun j hj => mem_zeroIdx.1 hj
  have h := hind.fintype_card_le_finrank
  rwa [Fintype.card_coe, Module.finrank_fin_fun] at h

/-! ## The component of a point realising the sign pattern -/

/-- The sign pattern is constant on the connected component of `x₁` in `nonvanishing q`. -/
theorem sign_eq_on_component {q : Fin m → MvPolynomial (Fin n) ℝ} {σ : Fin m → SignType}
    (hσ : ∀ j, σ j ≠ 0) {x₁ : Fin n → ℝ} (hx₁ : ∀ j, SignType.sign (eval x₁ (q j)) = σ j)
    {y : Fin n → ℝ} (hy : y ∈ connectedComponentIn (nonvanishing q) x₁) (j : Fin m) :
    SignType.sign (eval y (q j)) = σ j := by
  have hx₁G : x₁ ∈ nonvanishing q := mem_nonvanishing_of_sign hσ hx₁
  have hUsub : connectedComponentIn (nonvanishing q) x₁ ⊆ nonvanishing q :=
    connectedComponentIn_subset _ _
  have hx₁U : x₁ ∈ connectedComponentIn (nonvanishing q) x₁ := mem_connectedComponentIn hx₁G
  have hconn : IsPreconnected (connectedComponentIn (nonvanishing q) x₁) :=
    isPreconnected_connectedComponentIn
  have hu : IsOpen {w : Fin n → ℝ | 0 < eval w (q j)} :=
    isOpen_lt continuous_const (differentiable_evalPoly (q j)).continuous
  have hv : IsOpen {w : Fin n → ℝ | eval w (q j) < 0} :=
    isOpen_lt (differentiable_evalPoly (q j)).continuous continuous_const
  have hduv : Disjoint {w : Fin n → ℝ | 0 < eval w (q j)} {w : Fin n → ℝ | eval w (q j) < 0} := by
    rw [Set.disjoint_left]
    intro w hw hw'
    exact absurd (lt_trans hw hw') (lt_irrefl (0 : ℝ))
  have hsub : connectedComponentIn (nonvanishing q) x₁ ⊆
      {w : Fin n → ℝ | 0 < eval w (q j)} ∪ {w : Fin n → ℝ | eval w (q j) < 0} := by
    intro w hw
    rcases lt_or_gt_of_ne (hUsub hw j) with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases sign_ne_zero_cases (hσ j) with h1 | h1
  · have hx : x₁ ∈ {w : Fin n → ℝ | 0 < eval w (q j)} := by
      have h2 := hx₁ j
      rw [h1] at h2
      exact sign_eq_one_iff.1 h2
    have hUu := hconn.subset_left_of_subset_union hu hv hduv hsub ⟨x₁, hx₁U, hx⟩
    rw [h1]
    exact sign_pos (hUu hy)
  · have hx : x₁ ∈ {w : Fin n → ℝ | eval w (q j) < 0} := by
      have h2 := hx₁ j
      rw [h1] at h2
      exact sign_eq_neg_one_iff.1 h2
    have hUv := hconn.subset_right_of_subset_union hu hv hduv hsub ⟨x₁, hx₁U, hx⟩
    rw [h1]
    exact sign_neg (hUv hy)

/-! ## The main theorem -/

/-- **Charging a sign pattern.**

If the family `q` is in general position, the nowhere-zero sign pattern `σ` is realised at `x₁`,
and some index `j` has `σ j = -1` with `{q j ≤ 0}` bounded, then `σ` is *charged* to a
bounded component of the zero set of a nonempty subfamily of size at most `n`: there are a
nonempty `J` with `|J| ≤ n` and a common zero `x₀` of `(q j)_{j ∈ J}` whose connected component
`C` in that zero set is bounded, and on which every `q k` with `k ∉ J` has constant sign `σ k`.

Note that boundedness is only required for a *single* polynomial, namely one whose sign in the
pattern `σ` is negative; the remaining sublevel sets `{q k ≤ 0}` may be unbounded. -/
theorem exists_charge {n m : ℕ} (hn : 1 ≤ n) (q : Fin m → MvPolynomial (Fin n) ℝ)
    (hgp : ∀ (x : Fin n → ℝ) (S : Finset (Fin m)), (∀ j ∈ S, MvPolynomial.eval x (q j) = 0) →
        LinearIndependent ℝ (fun j : S => AlgebraicTransversality.gradient (q j) x))
    (σ : Fin m → SignType) (hσ : ∀ j, σ j ≠ 0)
    (x₁ : Fin n → ℝ) (hx₁ : ∀ j, SignType.sign (MvPolynomial.eval x₁ (q j)) = σ j)
    (hbdd : ∃ j, σ j = -1 ∧ Bornology.IsBounded {x | MvPolynomial.eval x (q j) ≤ 0}) :
    ∃ (J : Finset (Fin m)) (x₀ : Fin n → ℝ),
      J.Nonempty ∧ J.card ≤ n ∧ (∀ j ∈ J, MvPolynomial.eval x₀ (q j) = 0) ∧
      Bornology.IsBounded (connectedComponentIn {y | ∀ j ∈ J, MvPolynomial.eval y (q j) = 0} x₀) ∧
      ∀ c ∈ connectedComponentIn {y | ∀ j ∈ J, MvPolynomial.eval y (q j) = 0} x₀,
        ∀ k ∉ J, SignType.sign (MvPolynomial.eval c (q k)) = σ k := by
  classical
  have hGopen : IsOpen (nonvanishing q) := isOpen_nonvanishing q
  have hx₁G : x₁ ∈ nonvanishing q := mem_nonvanishing_of_sign hσ hx₁
  -- Step 1: the component `U` of `x₁`.
  set U : Set (Fin n → ℝ) := connectedComponentIn (nonvanishing q) x₁ with hUdef
  have hUopen : IsOpen U := by rw [hUdef]; exact hGopen.connectedComponentIn
  have hx₁U : x₁ ∈ U := by rw [hUdef]; exact mem_connectedComponentIn hx₁G
  have hUG : U ⊆ nonvanishing q := by rw [hUdef]; exact connectedComponentIn_subset _ _
  -- Step 2: the signs are constant on `U`.
  have hUsign : ∀ y ∈ U, ∀ j, SignType.sign (eval y (q j)) = σ j := by
    intro y hy j
    rw [hUdef] at hy
    exact sign_eq_on_component hσ hx₁ hy j
  -- Step 3: `U` is bounded, using the single index with negative sign and bounded sublevel set.
  obtain ⟨jneg, hjneg, hjbdd⟩ := hbdd
  have hUbdd : Bornology.IsBounded U := by
    refine hjbdd.subset ?_
    intro y hy
    have h := hUsign y hy jneg
    rw [hjneg] at h
    exact le_of_lt (sign_eq_neg_one_iff.1 h)
  -- Step 4: the "boundary" `F`.
  set F : Set (Fin n → ℝ) := closure U \ U with hFdef
  have hFclosed : IsClosed F := by rw [hFdef]; exact isClosed_closure.sdiff hUopen
  have hFsubcl : F ⊆ closure U := fun y hy => hy.1
  have hFbdd : Bornology.IsBounded F := hUbdd.closure.subset hFsubcl
  have hFne : F.Nonempty := by
    by_contra hFe
    rw [Set.not_nonempty_iff_eq_empty] at hFe
    have hcl : closure U ⊆ U := by
      intro y hy
      by_contra hyU
      have hmem : y ∈ F := ⟨hy, hyU⟩
      rw [hFe] at hmem
      exact hmem
    have hUclosed : IsClosed U := isClosed_of_closure_subset hcl
    have hclopen : IsClopen U := ⟨hUclosed, hUopen⟩
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have huniv := hclopen.eq_univ ⟨x₁, hx₁U⟩
    rw [huniv] at hUbdd
    exact NormedSpace.unbounded_univ ℝ (Fin n → ℝ) hUbdd
  -- Step 5: points of `F` are zeros of some `q j`.
  have hFnotG : ∀ y ∈ F, y ∉ nonvanishing q := by
    intro y hy hyG
    have hVopen : IsOpen (connectedComponentIn (nonvanishing q) y) := hGopen.connectedComponentIn
    have hyV : y ∈ connectedComponentIn (nonvanishing q) y := mem_connectedComponentIn hyG
    obtain ⟨w, hwV, hwU⟩ := mem_closure_iff.1 hy.1 _ hVopen hyV
    have h1 : connectedComponentIn (nonvanishing q) y = connectedComponentIn (nonvanishing q) w :=
      connectedComponentIn_eq hwV
    have h2 : U = connectedComponentIn (nonvanishing q) w := by
      rw [hUdef]
      exact connectedComponentIn_eq (by rw [← hUdef]; exact hwU)
    exact hy.2 (by rw [h2, ← h1]; exact hyV)
  have hFzero : ∀ y ∈ F, (zeroIdx q y).Nonempty := by
    intro y hy
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine hFnotG y hy fun j hj => ?_
    have : j ∈ zeroIdx q y := mem_zeroIdx.2 hj
    rw [hne] at this
    exact absurd this (Finset.notMem_empty j)
  -- Step 6/7: choose a point of `F` with a maximal vanishing set.
  set K : Finset ℕ := (Finset.range (m + 1)).filter (fun k => ∃ y ∈ F, (zeroIdx q y).card = k)
    with hKdef
  have hcard_le_m : ∀ y : Fin n → ℝ, (zeroIdx q y).card ≤ m := by
    intro y
    have := Finset.card_le_univ (zeroIdx q y)
    simpa using this
  obtain ⟨y₀, hy₀⟩ := hFne
  have hKne : K.Nonempty := by
    refine ⟨(zeroIdx q y₀).card, ?_⟩
    rw [hKdef, Finset.mem_filter]
    exact ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hcard_le_m y₀)), y₀, hy₀, rfl⟩
  obtain ⟨k₀, hk₀K, hk₀max⟩ := Finset.exists_max_image K id hKne
  obtain ⟨-, x₀, hx₀F, hx₀card⟩ := Finset.mem_filter.1 (by rw [← hKdef]; exact hk₀K)
  have hmax : ∀ y ∈ F, (zeroIdx q y).card ≤ (zeroIdx q x₀).card := by
    intro y hy
    rw [hx₀card]
    refine hk₀max (zeroIdx q y).card ?_
    rw [hKdef, Finset.mem_filter]
    exact ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hcard_le_m y)), y, hy, rfl⟩
  set J : Finset (Fin m) := zeroIdx q x₀ with hJdef
  have hJne : J.Nonempty := hFzero x₀ hx₀F
  have hJcard : J.card ≤ n := card_zeroIdx_le q hgp x₀
  have hJmem : ∀ j, j ∈ J ↔ eval x₀ (q j) = 0 := fun j => by rw [hJdef]; exact mem_zeroIdx
  set Z : Set (Fin n → ℝ) := {y | ∀ j ∈ J, eval y (q j) = 0} with hZdef
  have hx₀Z : x₀ ∈ Z := fun j hj => (hJmem j).1 hj
  set C : Set (Fin n → ℝ) := connectedComponentIn Z x₀ with hCdef
  have hCZ : C ⊆ Z := by rw [hCdef]; exact connectedComponentIn_subset _ _
  have hx₀C : x₀ ∈ C := by rw [hCdef]; exact mem_connectedComponentIn hx₀Z
  have hCconn : IsPreconnected C := by rw [hCdef]; exact isPreconnected_connectedComponentIn
  -- Step 8(a): points of `C ∩ F` have vanishing set exactly `J`.
  have hstepa : ∀ z ∈ C, z ∈ F → zeroIdx q z = J := by
    intro z hzC hzF
    have hsub : J ⊆ zeroIdx q z := fun j hj => mem_zeroIdx.2 (hCZ hzC j hj)
    exact (Finset.eq_of_subset_of_card_le hsub (hmax z hzF)).symm
  -- Step 8(b): the good set is locally open along `C`.
  have hloc : ∀ z : Fin n → ℝ, ∃ W : Set (Fin n → ℝ),
      (z ∈ C ∧ z ∈ F ∧ zeroIdx q z = J) →
        IsOpen W ∧ z ∈ W ∧ ∀ z' ∈ C, z' ∈ W → (z' ∈ C ∧ z' ∈ F ∧ zeroIdx q z' = J) := by
    intro z
    by_cases hz : z ∈ C ∧ z ∈ F ∧ zeroIdx q z = J
    · obtain ⟨hzC, hzF, hzJ⟩ := hz
      have hJz : ∀ j, j ∈ J ↔ eval z (q j) = 0 := by
        intro j
        rw [← hzJ]
        exact mem_zeroIdx
      have hind : LinearIndependent ℝ (fun j : J => gradient (q j) z) :=
        hgp z J fun j hj => (hJz j).1 hj
      obtain ⟨W, hWopen, hzW, hWk, hWτ⟩ := exists_orthant_nhd q z J hJz hind
      obtain ⟨hOconn, hOcl⟩ := hWτ σ fun j _ => hσ j
      refine ⟨W, fun _ => ⟨hWopen, hzW, ?_⟩⟩
      -- the orthant of `σ` inside `W`
      have hOG : {y ∈ W | ∀ j ∈ J, SignType.sign (eval y (q j)) = σ j} ⊆ nonvanishing q := by
        rintro y ⟨hyW, hy⟩ j
        by_cases hj : j ∈ J
        · intro h0
          refine hσ j ?_
          rw [← hy j hj, h0, sign_zero]
        · exact hWk j hj y hyW
      obtain ⟨u, huW, huU⟩ := mem_closure_iff.1 hzF.1 W hWopen hzW
      have huO : u ∈ {y ∈ W | ∀ j ∈ J, SignType.sign (eval y (q j)) = σ j} :=
        ⟨huW, fun j _ => hUsign u huU j⟩
      have hOU : {y ∈ W | ∀ j ∈ J, SignType.sign (eval y (q j)) = σ j} ⊆ U := by
        have h1 := hOconn.subset_connectedComponentIn huO hOG
        have h2 : U = connectedComponentIn (nonvanishing q) u := by
          rw [hUdef]
          exact connectedComponentIn_eq (by rw [← hUdef]; exact huU)
        rw [h2]
        exact h1
      intro z' hz'C hz'W
      have hz'Z : ∀ j ∈ J, eval z' (q j) = 0 := fun j hj => hCZ hz'C j hj
      have hz'cl : z' ∈ closure {y ∈ W | ∀ j ∈ J, SignType.sign (eval y (q j)) = σ j} :=
        hOcl z' hz'W hz'Z
      have hz'F : z' ∈ F := by
        refine ⟨closure_mono hOU hz'cl, ?_⟩
        intro hz'U
        obtain ⟨j, hj⟩ := hJne
        exact hUG hz'U j (hz'Z j hj)
      exact ⟨hz'C, hz'F, hstepa z' hz'C hz'F⟩
    · exact ⟨Set.univ, fun h => absurd h hz⟩
  choose Wf hWf using hloc
  -- Step 8(c): connectedness of `C` finishes the key claim.
  set A : Set (Fin n → ℝ) := {z | z ∈ C ∧ z ∈ F ∧ zeroIdx q z = J} with hAdef
  have hx₀A : x₀ ∈ A := ⟨hx₀C, hx₀F, rfl⟩
  have hAF : A ⊆ F := fun z hz => hz.2.1
  have hCAopen : IsOpen (⋃ z ∈ A, Wf z) :=
    isOpen_biUnion fun z hz => (hWf z hz).1
  have hCcover : C ⊆ (⋃ z ∈ A, Wf z) ∪ Fᶜ := by
    intro z hzC
    by_cases hzF : z ∈ F
    · have hzA : z ∈ A := ⟨hzC, hzF, hstepa z hzC hzF⟩
      exact Or.inl (Set.mem_biUnion hzA (hWf z hzA).2.1)
    · exact Or.inr hzF
  have hCAsub : ∀ y ∈ C, y ∈ (⋃ z ∈ A, Wf z) → y ∈ A := by
    intro y hyC hyU
    obtain ⟨z, hzA, hyW⟩ := Set.mem_iUnion₂.1 hyU
    exact (hWf z hzA).2.2 y hyC hyW
  have hCA : C ⊆ A := by
    have hdisj : C ∩ ((⋃ z ∈ A, Wf z) ∩ Fᶜ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyC, hyU, hyF⟩
      exact hyF (hAF (hCAsub y hyC hyU))
    rcases isPreconnected_iff_subset_of_disjoint.1 hCconn _ _ hCAopen hFclosed.isOpen_compl
      hCcover hdisj with h | h
    · exact fun y hy => hCAsub y hy (h hy)
    · exact absurd (h hx₀C) (by simpa using hx₀F)
  -- Step 9: assemble.
  have hclsign : ∀ y ∈ closure U, ∀ k, eval y (q k) ≠ 0 →
      SignType.sign (eval y (q k)) = σ k := by
    intro y hy k hk
    rcases sign_ne_zero_cases (hσ k) with h1 | h1
    · have hsub : U ⊆ {w : Fin n → ℝ | 0 ≤ eval w (q k)} := by
        intro w hw
        have h2 := hUsign w hw k
        rw [h1] at h2
        exact le_of_lt (sign_eq_one_iff.1 h2)
      have hcl : closure U ⊆ {w : Fin n → ℝ | 0 ≤ eval w (q k)} :=
        closure_minimal hsub
          (isClosed_le continuous_const (differentiable_evalPoly (q k)).continuous)
      rw [h1]
      exact sign_pos (lt_of_le_of_ne (hcl hy) (Ne.symm hk))
    · have hsub : U ⊆ {w : Fin n → ℝ | eval w (q k) ≤ 0} := by
        intro w hw
        have h2 := hUsign w hw k
        rw [h1] at h2
        exact le_of_lt (sign_eq_neg_one_iff.1 h2)
      have hcl : closure U ⊆ {w : Fin n → ℝ | eval w (q k) ≤ 0} :=
        closure_minimal hsub
          (isClosed_le (differentiable_evalPoly (q k)).continuous continuous_const)
      rw [h1]
      exact sign_neg (lt_of_le_of_ne (hcl hy) hk)
  refine ⟨J, x₀, hJne, hJcard, fun j hj => (hJmem j).1 hj, ?_, ?_⟩
  · have : connectedComponentIn {y | ∀ j ∈ J, eval y (q j) = 0} x₀ = C := by
      rw [hCdef, hZdef]
    rw [this]
    exact hFbdd.subset fun z hz => (hCA hz).2.1
  · have hCeq : connectedComponentIn {y | ∀ j ∈ J, eval y (q j) = 0} x₀ = C := by
      rw [hCdef, hZdef]
    rw [hCeq]
    intro c hc k hk
    obtain ⟨-, hcF, hcJ⟩ := hCA hc
    have hck : eval c (q k) ≠ 0 := by
      intro h0
      exact hk (by rw [← hcJ]; exact mem_zeroIdx.2 h0)
    exact hclsign c hcF.1 k hck

end SignPatterns

