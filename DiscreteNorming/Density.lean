import DiscreteNorming.Defs
import DiscreteNorming.ComplexPoly

/-!
# Claim C12: from the countable subfamily to all of `𝒱`

Let `S` be a finite set which meets every set of the rational subfamily of measure `≥ t|Ω|`.
Let `P = diff F G` with `F = comb φ a`, `G = comb φ b` (arbitrary complex coefficients), `K ≥ 0`,
`0 < c ≤ 1`, and suppose the superlevel set `{z ∈ Ω : |P(z)| ≥ c K}` has measure `≥ t|Ω|`.
Then `|P(y)| ≥ c K` for some `y ∈ S`.

Proof. If not, `max_S |P| < cK`; pick `η > 0` with `max_S |P| < (c − 3η)K`, a Gaussian-rational
approximant `P'` with `sup_Ω |P − P'| ≤ ηK` (`exists_rat_approx`) and a rational threshold
`τ ∈ [(c − 2η)K, (c − η)K]`. Then `{z ∈ Ω : |P'| ≥ τ} ⊇ {z ∈ Ω : |P| ≥ cK}` has measure
`≥ t|Ω|`, so it contains some `y ∈ S`, and `|P(y)| ≥ τ − ηK ≥ (c − 3η)K`, a contradiction.
No constant is lost because `S` is fixed and `η` is arbitrary.
-/

open MeasureTheory Metric

namespace DiscreteNorming

/-- **Norming from hitting the countable subfamily.** -/
theorem norming_of_hits {d N : ℕ} {Ω : Set (Pt d)} (hb : Bornology.IsBounded Ω)
    (φ : Fin N → PolyFock.Fock.P d) {t : ℝ} {S : Finset (Pt d)}
    (hhit : ∀ i : RatIndex N, t * vol Ω ≤ vol (ratFamily Ω φ i) → ∃ p ∈ S, p ∈ ratFamily Ω φ i)
    (a b : Fin N → ℂ) {K c : ℝ} (hK : 0 ≤ K) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hsup : t * vol Ω ≤ vol {x ∈ Ω | c * K ≤ |diff (comb φ a) (comb φ b) x|})
    (hS : S.Nonempty) :
    ∃ y ∈ S, c * K ≤ |diff (comb φ a) (comb φ b) y| := by
  classical
  obtain ⟨y₀, hy₀⟩ := hS
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · -- `K = 0`: the conclusion is `0 ≤ |P y|`.
    refine ⟨y₀, hy₀, ?_⟩
    rw [← hK0, mul_zero]
    exact abs_nonneg _
  by_contra hcon
  push Not at hcon
  -- `m` is the maximum of `|P|` over `S`; by assumption `m < cK`.
  obtain ⟨m, hmdef⟩ :
      ∃ m : ℝ, m = S.sup' ⟨y₀, hy₀⟩ (fun y ↦ |diff (comb φ a) (comb φ b) y|) := ⟨_, rfl⟩
  have hmlt : m < c * K := by
    rw [hmdef]; exact (Finset.sup'_lt_iff ⟨y₀, hy₀⟩).2 hcon
  have hm0 : 0 ≤ m := by
    rw [hmdef]
    exact le_trans (abs_nonneg (diff (comb φ a) (comb φ b) y₀))
      (Finset.le_sup' (fun y ↦ |diff (comb φ a) (comb φ b) y|) hy₀)
  have hKne : K ≠ 0 := ne_of_gt hKpos
  -- the approximation parameter `η`
  obtain ⟨η, hηpos, hηK⟩ : ∃ η : ℝ, 0 < η ∧ η * K = (c * K - m) / 4 := by
    refine ⟨(c * K - m) / (4 * K), div_pos (by linarith) (by linarith), ?_⟩
    field_simp
  have hηKpos : 0 < η * K := mul_pos hηpos hKpos
  have hlt : (c - 2 * η) * K < (c - η) * K := by nlinarith [hηK, hmlt]
  have hpos2 : 0 < (c - 2 * η) * K := by nlinarith [hηK, hmlt, hm0]
  have hgt : m < (c - 3 * η) * K := by nlinarith [hηK, hmlt]
  -- the Gaussian-rational approximant `P'`
  obtain ⟨a', b', happ⟩ := exists_rat_approx φ hb a b hηKpos
  -- the rational threshold `τ`
  obtain ⟨τ, hτ1, hτ2⟩ := exists_rat_btwn hlt
  have hτpos : 0 < τ := by
    have h : (0 : ℝ) < (τ : ℝ) := lt_trans hpos2 hτ1
    exact_mod_cast h
  set i : RatIndex N := (a', b', ⟨τ, hτpos⟩) with hidef
  -- Claim 1: the `cK`-superlevel set of `P` sits inside the `τ`-superlevel set of `P'`.
  have hsub : {x ∈ Ω | c * K ≤ |diff (comb φ a) (comb φ b) x|} ⊆ ratFamily Ω φ i := by
    rintro x ⟨hxΩ, hx⟩
    have h1 := happ x hxΩ
    have h2 := abs_sub_abs_le_abs_sub (diff (comb φ a) (comb φ b) x)
      (diff (ratComb φ a') (ratComb φ b') x)
    refine ⟨hxΩ, ?_⟩
    change ((τ : ℚ) : ℝ) ≤ |diff (ratComb φ a') (ratComb φ b') x|
    linarith
  -- the superlevel set of `P'` is contained in `Ω`, hence of finite measure
  have hsubΩ : ratFamily Ω φ i ⊆ Ω := fun x hx ↦ hx.1
  have hfin : volume (ratFamily Ω φ i) ≠ ⊤ :=
    ((measure_mono hsubΩ).trans_lt hb.measure_lt_top).ne
  have hmono : vol {x ∈ Ω | c * K ≤ |diff (comb φ a) (comb φ b) x|} ≤ vol (ratFamily Ω φ i) :=
    ENNReal.toReal_mono hfin (measure_mono hsub)
  -- so `S` hits it
  obtain ⟨y, hyS, hy⟩ := hhit i (le_trans hsup hmono)
  have hyΩ : y ∈ Ω := hy.1
  have hyτ : ((τ : ℚ) : ℝ) ≤ |diff (ratComb φ a') (ratComb φ b') y| := hy.2
  have h1 := happ y hyΩ
  have h2 := abs_sub_abs_le_abs_sub (diff (ratComb φ a') (ratComb φ b') y)
    (diff (comb φ a) (comb φ b) y)
  have h3 : |diff (ratComb φ a') (ratComb φ b') y - diff (comb φ a) (comb φ b) y|
      = |diff (comb φ a) (comb φ b) y - diff (ratComb φ a') (ratComb φ b') y| := abs_sub_comm _ _
  have h4 : |diff (comb φ a) (comb φ b) y| ≤ m := by
    rw [hmdef]; exact Finset.le_sup' (fun y ↦ |diff (comb φ a) (comb φ b) y|) hyS
  -- `m < (c − 3η)K < τ − ηK ≤ |P y| ≤ m`
  nlinarith [hτ1, hyτ, h1, h2, h3, h4, hgt]

end DiscreteNorming
