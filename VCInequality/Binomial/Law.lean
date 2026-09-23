import VCInequality.Defs

/-!
# Law of the count

Under `sampleMeasure μ m = μ^{⊗m}`, the number of sample points in a measurable set `B` is
binomial `Bin(m, μ B)`: `μ^{⊗m} {y | t ≤ count y B} = binTail m ⌈t⌉₊ (μ B)`.

Route: `{y | count y B = j}` is the disjoint union over `j`-subsets `J` of `Fin m` of the boxes
`{y | ∀ i, y i ∈ B ↔ i ∈ J} = Set.pi univ (fun i ↦ if i ∈ J then B else Bᶜ)`, each of measure
`p^j (1−p)^{m−j}` by `Measure.pi_pi`; there are `m.choose j` of them (`Finset.card_powersetCard`).
Alternatively use `ProbabilityTheory.setBernoulli` / `binomial` and `measurePreserving_pi`.
Note `t ≤ (count y B : ℝ) ↔ ⌈t⌉₊ ≤ count y B` (`Nat.ceil_le`).
-/

open MeasureTheory ProbabilityTheory Finset

namespace VCInequality

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- At most all `m` sample points can lie in `B`. -/
theorem count_le {m : ℕ} (y : Fin m → X) (B : Set X) : count y B ≤ m := by
  classical
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- The set of samples whose membership pattern in `B` is exactly the index set `J`. -/
def box (B : Set X) {m : ℕ} (J : Finset (Fin m)) : Set (Fin m → X) :=
  Set.pi Set.univ fun i ↦ if i ∈ J then B else Bᶜ

omit [MeasurableSpace X] in
theorem mem_box_iff (B : Set X) {m : ℕ} (J : Finset (Fin m)) (y : Fin m → X) :
    y ∈ box B J ↔ ∀ i, (y i ∈ B ↔ i ∈ J) := by
  classical
  simp only [box, Set.mem_univ_pi]
  refine forall_congr' fun i ↦ ?_
  by_cases h : i ∈ J <;> simp [h]

theorem measurableSet_box {B : Set X} (hB : MeasurableSet B) {m : ℕ} (J : Finset (Fin m)) :
    MeasurableSet (box B J) := by
  classical
  refine MeasurableSet.univ_pi fun i ↦ ?_
  by_cases h : i ∈ J <;> simp [h, hB, hB.compl]

omit [MeasurableSpace X] in
/-- `{y | count y B = j}` is the union of the boxes indexed by the `j`-element subsets. -/
theorem count_eq_iUnion {m : ℕ} (B : Set X) (j : ℕ) :
    {y : Fin m → X | count y B = j} = ⋃ J ∈ powersetCard j (univ : Finset (Fin m)), box B J := by
  classical
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_powersetCard, mem_box_iff]
  constructor
  · intro h
    exact ⟨univ.filter fun i ↦ y i ∈ B, ⟨Finset.subset_univ _, by
      rw [← h]; rfl⟩, fun i ↦ by simp⟩
  · rintro ⟨J, ⟨-, hJ⟩, hy⟩
    rw [show count y B = #(univ.filter fun i ↦ y i ∈ B) from rfl, ← hJ]
    congr 1
    ext i
    simp [hy i]

omit [MeasurableSpace X] in
/-- Distinct index sets give disjoint boxes. -/
theorem pairwiseDisjoint_box {B : Set X} {m : ℕ} (s : Finset (Finset (Fin m))) :
    (s : Set (Finset (Fin m))).PairwiseDisjoint (box B) := by
  intro J _ K _ hJK
  simp only [Function.onFun, Set.disjoint_left]
  intro y hyJ hyK
  exact hJK (Finset.ext fun i ↦
    ((mem_box_iff B J y).mp hyJ i).symm.trans ((mem_box_iff B K y).mp hyK i))

theorem measurableSet_count_eq {B : Set X} (hB : MeasurableSet B) {m : ℕ} (j : ℕ) :
    MeasurableSet {y : Fin m → X | count y B = j} := by
  classical
  rw [count_eq_iUnion]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun J _ ↦ measurableSet_box hB J

/-- Each box has measure `p ^ #J * (1 - p) ^ (m - #J)`. -/
theorem measureReal_box (μ : Measure X) [IsProbabilityMeasure μ] {m : ℕ} {B : Set X}
    (hB : MeasurableSet B) (J : Finset (Fin m)) :
    (sampleMeasure μ m).real (box B J) = (μ.real B) ^ #J * (1 - μ.real B) ^ (m - #J) := by
  classical
  have hcompl : μ.real Bᶜ = 1 - μ.real B := by
    rw [measureReal_compl hB, probReal_univ]
  have h1 : (univ.filter fun i : Fin m ↦ i ∈ J) = J := by ext i; simp
  have h2 : (univ.filter fun i : Fin m ↦ i ∉ J) = Jᶜ := by ext i; simp
  rw [measureReal_def, box, MeasureTheory.Measure.pi_pi, ENNReal.toReal_prod]
  have key : ∀ i : Fin m, (μ (if i ∈ J then B else Bᶜ)).toReal
      = if i ∈ J then μ.real B else (1 - μ.real B) := by
    intro i
    by_cases h : i ∈ J
    · simp [h, measureReal_def]
    · simpa [h, measureReal_def] using hcompl
  rw [Finset.prod_congr rfl fun i _ ↦ key i, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const, h1, h2, Finset.card_compl, Fintype.card_fin]

theorem sampleMeasure_real_count_eq (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ)
    {B : Set X} (hB : MeasurableSet B) (j : ℕ) :
    (sampleMeasure μ m).real {y | count y B = j}
      = (m.choose j : ℝ) * (μ.real B) ^ j * (1 - μ.real B) ^ (m - j) := by
  classical
  have hterm : ∀ J ∈ powersetCard j (univ : Finset (Fin m)),
      (sampleMeasure μ m).real (box B J) = (μ.real B) ^ j * (1 - μ.real B) ^ (m - j) := by
    intro J hJ
    rw [measureReal_box μ hB J, (mem_powersetCard.mp hJ).2]
  rw [count_eq_iUnion,
    measureReal_biUnion_finset (pairwiseDisjoint_box _) (fun J _ ↦ measurableSet_box hB J),
    Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sampleMeasure_real_count_ge (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ)
    {B : Set X} (hB : MeasurableSet B) (t : ℝ) :
    (sampleMeasure μ m).real {y | t ≤ count y B} = binTail m ⌈t⌉₊ (μ.real B) := by
  classical
  have hset : {y : Fin m → X | t ≤ (count y B : ℝ)}
      = ⋃ k ∈ Icc ⌈t⌉₊ m, {y : Fin m → X | count y B = k} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_Icc]
    constructor
    · intro h
      exact ⟨count y B, ⟨Nat.ceil_le.mpr h, count_le y B⟩, rfl⟩
    · rintro ⟨k, ⟨hk1, -⟩, rfl⟩
      exact Nat.ceil_le.mp hk1
  have hdisj : (Icc ⌈t⌉₊ m : Set ℕ).PairwiseDisjoint
      (fun k ↦ {y : Fin m → X | count y B = k}) := by
    intro a _ b _ hab
    simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
    rintro y rfl hb
    exact hab hb
  rw [hset, measureReal_biUnion_finset hdisj (fun k _ ↦ measurableSet_count_eq hB k), binTail]
  exact Finset.sum_congr rfl fun k _ ↦ sampleMeasure_real_count_eq μ m hB k

end VCInequality
