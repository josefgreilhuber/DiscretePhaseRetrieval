import VCInequality.Defs
import DiscretePhaseRetrieval.Auxiliary

/-!
# Sauer–Shelah step

A family of VC dimension `≤ V` has growth function at most `(e n / V)^V` on `n ≥ V` points.
The binomial-tail estimate `∑_{k ≤ V} C(n,k) ≤ (e n / V)^V` behind it is
`DiscretePR.sum_choose_le_exp_pow` (`DiscretePhaseRetrieval/Auxiliary.lean`), shared with
Warren's sign-pattern bound.

Mathlib input: `Finset.card_le_card_shatterer`, `Finset.card_shatterer_le_sum_vcDim`,
`Finset.Shatters`, `Finset.vcDim`.
-/

open MeasureTheory Finset

namespace VCInequality

variable {X : Type*} [MeasurableSpace X]

/-- A family of VC dimension `≤ V` has at most `(e n / V)^V` traces on any `n`-point sample,
`1 ≤ V ≤ n`. -/
theorem isGrowthBound_of_vcDimLE {𝒢 : Set (Set X)} {V n : ℕ} (hvc : VCDimLE 𝒢 V)
    (hV : 1 ≤ V) (hVn : V ≤ n) :
    IsGrowthBound 𝒢 n ((Real.exp 1 * n / V) ^ V) := by
  classical
  intro x
  -- The family of traces of `𝒢` on the sample `x`, as a `Finset (Finset (Fin n))`.
  set T : Set (Set (Fin n)) := (fun A ↦ {i | x i ∈ A}) '' 𝒢 with hT
  set 𝒜 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun s : Finset (Fin n) ↦ (↑s : Set (Fin n)) ∈ T) with h𝒜
  have hmem𝒜 : ∀ s : Finset (Fin n), s ∈ 𝒜 ↔ (↑s : Set (Fin n)) ∈ T := by
    intro s; simp [h𝒜]
  -- `𝒜` has the same cardinality as `T`.
  have hTcard : T.ncard = #𝒜 := by
    have himg : T = ↑(𝒜.image (fun s : Finset (Fin n) ↦ (↑s : Set (Fin n)))) := by
      ext A
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · intro hA
        refine ⟨A.toFinset, ?_, ?_⟩
        · rw [hmem𝒜, Set.coe_toFinset]; exact hA
        · rw [Set.coe_toFinset]
      · rintro ⟨s, hs, rfl⟩
        exact (hmem𝒜 s).mp hs
    rw [himg, Set.ncard_coe_finset, Finset.card_image_of_injective _ Finset.coe_injective]
  -- Every member of `𝒜` is the trace of some `A ∈ 𝒢`.
  have htrace : ∀ u : Finset (Fin n), u ∈ 𝒜 → ∃ A ∈ 𝒢, ∀ i, (i ∈ u ↔ x i ∈ A) := by
    intro u hu
    obtain ⟨A, hA𝒢, hAu⟩ := (hmem𝒜 u).mp hu
    have hAu' : ({i | x i ∈ A} : Set (Fin n)) = (↑u : Set (Fin n)) := hAu
    refine ⟨A, hA𝒢, fun i ↦ ?_⟩
    constructor
    · intro hi
      have hi' : i ∈ (↑u : Set (Fin n)) := by exact_mod_cast hi
      rw [← hAu'] at hi'
      exact hi'
    · intro hi
      have hi' : i ∈ ({i | x i ∈ A} : Set (Fin n)) := hi
      rw [hAu'] at hi'
      exact_mod_cast hi'
  -- The trace family has VC dimension at most `V`.
  have hvcdim : 𝒜.vcDim ≤ V := by
    refine Finset.sup_le ?_
    intro s hs
    rw [Finset.mem_shatterer] at hs
    -- `x` is injective on a shattered index set: singletons separate the indices.
    have hinj : Set.InjOn x ↑s := by
      intro i hi j hj hij
      by_contra hne
      obtain ⟨u, hu, hsu⟩ := hs (Finset.singleton_subset_iff.mpr (by simpa using hi))
      obtain ⟨A, hA𝒢, hAu⟩ := htrace u hu
      have hiu : i ∈ u := by
        have : i ∈ s ∩ u := by rw [hsu]; simp
        exact (Finset.mem_inter.mp this).2
      have hju : j ∉ u := by
        intro hju'
        have : j ∈ s ∩ u := Finset.mem_inter.mpr ⟨by simpa using hj, hju'⟩
        rw [hsu, Finset.mem_singleton] at this
        exact hne this.symm
      exact hju ((hAu j).mpr (hij ▸ (hAu i).mp hiu))
    have hcard : #(s.image x) = #s := Finset.card_image_of_injOn hinj
    -- The image point set is shattered by `𝒢`.
    have hle := hvc (s.image x) ?_
    · omega
    · intro t ht
      obtain ⟨u, hu, hsu⟩ := hs (Finset.filter_subset (fun i ↦ x i ∈ t) s)
      obtain ⟨A, hA𝒢, hAu⟩ := htrace u hu
      refine ⟨A, hA𝒢, ?_⟩
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      constructor
      · intro hxiA
        have : i ∈ s ∩ u := Finset.mem_inter.mpr ⟨hi, (hAu i).mpr hxiA⟩
        rw [hsu, Finset.mem_filter] at this
        exact this.2
      · intro hxit
        have : i ∈ s.filter (fun i ↦ x i ∈ t) := Finset.mem_filter.mpr ⟨hi, hxit⟩
        rw [← hsu] at this
        exact (hAu i).mp (Finset.mem_inter.mp this).2
  -- Sauer–Shelah plus the binomial estimate.
  have hnat : #𝒜 ≤ ∑ k ∈ Iic V, n.choose k := by
    calc #𝒜 ≤ #𝒜.shatterer := Finset.card_le_card_shatterer 𝒜
      _ ≤ ∑ k ∈ Iic 𝒜.vcDim, (Fintype.card (Fin n)).choose k :=
          Finset.card_shatterer_le_sum_vcDim
      _ = ∑ k ∈ Iic 𝒜.vcDim, n.choose k := by simp
      _ ≤ ∑ k ∈ Iic V, n.choose k :=
          Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hvcdim)
  calc (T.ncard : ℝ) = (#𝒜 : ℝ) := by rw [hTcard]
    _ ≤ ((∑ k ∈ Iic V, n.choose k : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ∑ k ∈ Iic V, (n.choose k : ℝ) := by push_cast; ring
    _ ≤ (Real.exp 1 * n / V) ^ V := DiscretePR.sum_choose_le_exp_pow n V hV hVn

end VCInequality
