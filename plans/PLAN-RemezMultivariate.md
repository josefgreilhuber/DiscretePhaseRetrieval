# Attack plan: the Brudnyi–Ganzburg multivariate Remez inequality

Target: inequality (4.1) of Ganzburg's survey (`Remez/Ganzburg_Survey.pdf`, p. 288).
For a convex body `V ⊂ ℝᵐ`, a set `E ⊆ V` of positive measure and a polynomial `P` of total
degree `≤ n`,

    ‖P‖_{C(V)} ≤ Tₙ( (1 + βₘ(|E|/|V|)) / (1 − βₘ(|E|/|V|)) ) ‖P‖_{C(E)},   βₘ(t) = (1 − t)^{1/m}.

Only the inequality; the extremal bodies/sets/polynomials of [16] are out of scope.

## Target statement (`Remez/Multivariate/BrudnyiGanzburgRemez.lean`, namespace `Remez`)

```lean
/-- `βₘ(t) = (1 - t)^{1/m}`. -/
noncomputable def beta (m : ℕ) (t : ℝ) : ℝ := (1 - t) ^ (1 / (m : ℝ))

/-- **Brudnyi–Ganzburg multivariate Remez inequality.** -/
theorem brudnyi_ganzburg {m : ℕ} (hm : 0 < m)
    {V : Set (Fin m → ℝ)} (hVconv : Convex ℝ V) (hVcpt : IsCompact V)
    {E : Set (Fin m → ℝ)} (hE : E ⊆ V) (hvol : 0 < volume E)
    {P : MvPolynomial (Fin m) ℝ} {n : ℕ} (hP : P.totalDegree ≤ n)
    {K : ℝ} (hPE : ∀ y ∈ E, |MvPolynomial.eval y P| ≤ K) {x : Fin m → ℝ} (hx : x ∈ V) :
    let β := beta m ((volume E).toReal / (volume V).toReal)
    |MvPolynomial.eval x P| ≤ (Polynomial.Chebyshev.T ℝ n).eval ((1 + β) / (1 - β)) * K
```

plus a `sSup` form as in the 1-D file.  Remarks on the hypotheses:

* `V` compact convex is the survey's "convex body"; nonempty interior is not needed because
  `|E| > 0` forces `|V| > 0`.  (Relaxing to bounded convex is possible later via
  `Convex.nullMeasurableSet`, but adds nothing for our use.)
* `E` needs **no measurability**: we run the argument on the closed set
  `M = V ∩ {|P| ≤ K} ⊇ E` and finish with the monotonicity of `Tₙ` on `[1, ∞)`.
* `m ≥ 1` is needed: for `m = 0` Lean's `1/m = 0` makes `β = 1` and the constant meaningless.
  For `m = 1` the constant reduces to `Tₙ(2|V|/|E| − 1)`, i.e. the 1-D theorem.
* All points `x ∈ V` are treated at once, boundary points included (rays with `ρ(θ) = 0`
  are simply allowed, see step C); no reduction to interior points, no density argument.

## Proof (the ray-scanning argument)

Fix `x ∈ V` and the closed set `M := V ∩ {y | |P y| ≤ K}`, `E ⊆ M`, so `|M| ≥ |E| > 0`.
Write `‖·‖` for the sup norm on `Fin m → ℝ` (any norm works; the sup norm keeps us in the
plain `volume` on `Fin m → ℝ`, no `EuclideanSpace` wrapper).  For a direction `θ` on the
unit sphere `S = sphere 0 1` define the *ray fibers*

    V_θ = {r > 0 | x + rθ ∈ V},   M_θ = {r > 0 | x + rθ ∈ M},   ρ(θ) = |V_θ|₁,   a(θ) = |M_θ|₁.

1. **Polar coordinates around `x`.**  For every measurable `S ⊆ ℝᵐ`,
   `|S| = ∫_{θ ∈ S} ( ∫_{S_θ} r^{m-1} dr ) dσ(θ)` with `σ = volume.toSphere`.
2. **Star-shapedness.**  `V` convex, `x ∈ V` ⇒ `Ioo 0 ρ(θ) ⊆ V_θ ⊆ Ioc 0 ρ(θ)`, and
   `∫_{V_θ} r^{m-1} dr = ρ^m/m`.
3. **A good ray exists.**  Let `β = (1 − |M|/|V|)^{1/m}`.  There is `θ` with `ρ(θ) > 0` and
   `a(θ) ≥ (1 − β) ρ(θ)`.  Proof by contradiction: otherwise, for every `θ` with `ρ > 0`,
   pushing `M_θ` to the right end of `(0, ρ]` (the weight `r^{m-1}` is increasing) gives
   `∫_{M_θ} r^{m-1} ≤ ∫_{ρ−a}^{ρ} r^{m-1} < ∫_{βρ}^{ρ} r^{m-1} = (1 − β^m) ρ^m/m = (|M|/|V|) ∫_{V_θ} r^{m-1}`;
   for `ρ = 0` both sides vanish.  The set `{ρ > 0}` has positive `σ`-measure (else `|V| = 0`),
   so integrating over `θ` gives the strict inequality `|M| < (|M|/|V|)|V| = |M|`.
4. **1-D Remez on the good ray.**  `q(r) := P(x + rθ)` is a univariate polynomial of degree
   `≤ n`, `|q| ≤ K` on `M_θ ⊆ [0, ρ]`, and `|M_θ| ≥ m₀ := (1 − β)ρ > 0`.  The 1-D theorem at
   the left endpoint `r = 0` gives `|P(x)| = |q(0)| ≤ Tₙ(2ρ/m₀ − 1) K = Tₙ((1+β)/(1−β)) K`.
   (As in the 1-D file the constant is exact: we feed the lower bound `m₀`, not `|M_θ|`,
   into Remez, so no monotonicity of `Tₙ` is needed here.)
5. **Back to `E`.**  `|M| ≥ |E|` ⇒ `β_M ≤ β_E` ⇒ `(1+β_M)/(1−β_M) ≤ (1+β_E)/(1−β_E)`, and
   `Tₙ` is monotone on `[1, ∞)` (immediate from `Remez.eval_T_eq_sum`: every term
   `∏ |y − ηⱼ|/|ηᵢ − ηⱼ|` is increasing in `y ≥ 1`).

## Files and lemmas

Reused as is: `Remez.remez_of_abs_le_one` (gives the left endpoint by taking `x = a`),
`Remez.eval_T_eq_sum`, Mathlib's `measurePreserving_homeomorphUnitSphereProd`,
`Measure.toSphere`, `volumeIoiPow`, `lintegral_strict_mono_of_ae_le_of_ae_lt_on`.

### A. Additions to the 1-D files (~40 lines)
* `remez_of_abs_le`: the `K`-normalised form of `remez_of_abs_le_one` with hypothesis
  `ofReal m ≤ volume E` (same scaling trick as `remez_inequality`).
* `Interpolation.lean`: `monotoneOn_eval_T : MonotoneOn (fun y => (T ℝ n).eval y) (Ici 1)`.

### B. `Remez/Multivariate/Line.lean` — restriction of `P` to a line (~60 lines)
* `lineRestrict P x θ : ℝ[X] := MvPolynomial.aeval (fun i => C (x i) + C (θ i) * X) P`.
* `eval_lineRestrict : (lineRestrict P x θ).eval r = MvPolynomial.eval (x + r • θ) P`
  (ring-hom extensionality: `Polynomial.evalRingHom r ∘ aeval f = eval (fun i => (f i).eval r)`).
* `natDegree_lineRestrict_le : (lineRestrict P x θ).natDegree ≤ P.totalDegree`
  (expand `P` as a sum of monomials; `natDegree_sum_le`, `natDegree_prod_le`,
  `natDegree_pow_le`, `natDegree_linear_le`).  Mathlib has no such lemma.

### C. `Remez/Multivariate/Polar.lean` — polar coordinates about a point (~150 lines, main risk)
* `rayFiber S x θ := {r : ℝ | 0 < r ∧ x + r • θ ∈ S}`,
  `rayWeight m S x θ := ∫⁻ r in rayFiber S x θ, ENNReal.ofReal (r ^ (m - 1))`.
* `volume_eq_lintegral_rayWeight (hS : MeasurableSet S) :
     volume S = ∫⁻ θ, rayWeight m S x θ ∂(volume.toSphere)`.
  Proof: translate by `x` (`measure_preimage_add`), drop the null point `{0}`
  (`comap_subtype_coe_apply`, `measure_singleton`), apply
  `MeasurePreserving.measure_preimage` to the set `{(θ, r) | x + r • θ ∈ S}` whose preimage
  under `y ↦ (y/‖y‖, ‖y‖)` is `{y ≠ 0 | x + y ∈ S}`, then `Measure.prod_apply`, and unfold
  `volumeIoiPow` (`withDensity_apply`, `setLIntegral_subtype`) to a Lebesgue integral on `ℝ`.
* `measurable_rayWeight : Measurable (rayWeight m S x)` (from `Measurable.lintegral_prod_right'`).
* Everything is over the sup-norm sphere; `finrank ℝ (Fin m → ℝ) = m` gives the weight `r^{m-1}`.

### D. `Remez/Multivariate/Rearrangement.lean` — 1-D weighted estimates (~120 lines)
* `rayFiber_convex`: for `V` convex bounded, `x ∈ V`: `Ioo 0 ρ ⊆ V_θ ⊆ Ioc 0 ρ` where
  `ρ = (volume V_θ).toReal` (the fiber is an interval starting at `0`; its sup equals its measure).
* `lintegral_pow_Ioo : ∫⁻ r in Ioo 0 ρ, ofReal (r^(m-1)) = ofReal (ρ^m / m)` and the same for
  `Ioc (βρ) ρ` giving `ofReal ((1 − β^m) ρ^m / m)` (via `integral_pow`, as in Mathlib's
  `volumeIoiPow_apply_Iio`).
* `lintegral_pow_le_of_subset_Ioc` (the pushing lemma): `A ⊆ Ioc 0 ρ` measurable,
  `a = |A|` ⇒ `∫⁻ r in A, ofReal (r^(m-1)) ≤ ∫⁻ r in Ioc (ρ − a) ρ, ofReal (r^(m-1))`.
  Split `A` at `ρ − a`; the lower part has the same measure as `Ioc (ρ−a) ρ \ A`, and the
  weight is `≤ (ρ−a)^{m-1}` on the former and `≥ (ρ−a)^{m-1}` on the latter.

### E. `Remez/Multivariate/BrudnyiGanzburgRemez.lean` (~150 lines)
* `exists_good_ray`: `V` compact convex, `M ⊆ V` measurable, `0 < |M|`, `x ∈ V`,
  `β = beta m (|M|/|V|)` ⇒ `∃ θ ∈ sphere 0 1, 0 < ρ θ ∧ ofReal ((1 − β) ρ θ) ≤ volume (M_θ)`.
  (Step 3; uses `lintegral_strict_mono_of_ae_le_of_ae_lt_on` with `s = {ρ > 0}`,
  `f = rayWeight M`, `g = (|M|/|V|) • rayWeight V`; `β^m = 1 − |M|/|V|` by
  `Real.rpow_inv_natCast_pow`.)
* `brudnyi_ganzburg_of_closed`: the theorem for the closed sublevel set `M`
  (steps 4: `lineRestrict`, `remez_of_abs_le` on `[0, ρ]` at `0`, algebra
  `2ρ/((1−β)ρ) − 1 = (1+β)/(1−β)`).
* `brudnyi_ganzburg`, `brudnyi_ganzburg_sSup` (step 5).

## Risks and fallbacks
* Step C is the only genuinely fiddly part (subtype measures on `{0}ᶜ` and `Ioi 0`, the
  `comap`/`withDensity` unfolding).  Mathlib's own proof of `volumeIoiPow_apply_Iio` shows the
  needed rewrites, so this is bookkeeping rather than mathematics.
* Strictness in step 3 is handled by `lintegral_strict_mono_of_ae_le_of_ae_lt_on`; the only
  side condition is `σ{ρ > 0} ≠ 0`, which follows from `|V| = ∫ rayWeight V > 0`.
* Expected total: 500–600 new lines, four new files; sorry-free with standard axioms, checked
  by `#print axioms` as for the 1-D theorem.
