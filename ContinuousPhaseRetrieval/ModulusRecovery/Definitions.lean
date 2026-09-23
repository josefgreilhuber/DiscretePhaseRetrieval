import Mathlib

set_option linter.unusedVariables false

open scoped BigOperators

noncomputable section

namespace ModulusRecovery

abbrev Cd (d : Nat) := Fin d -> ℂ
abbrev MultiIndex (d : Nat) := Fin d -> Nat
abbrev Idx (d : Nat) := MultiIndex d

abbrev Pfin (d : Nat) := Finsupp (Idx d) ℂ

structure Coeffs (d : Nat) where
  coeff : Idx d -> ℂ
  summable_norm_sq : Summable (fun alpha : Idx d => ‖coeff alpha‖ ^ 2)

def gaussianDensity (d : Nat) (z : Cd d) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-Finset.sum Finset.univ (fun q : Fin d => ‖z q‖ ^ 2))

def gamma_d (d : Nat) : MeasureTheory.Measure (Cd d) :=
  MeasureTheory.volume.withDensity fun z => ENNReal.ofReal (gaussianDensity d z)

abbrev L2Tensor (d : Nat) := MeasureTheory.Lp ℂ 2 (gamma_d d)

def complexHermite (m n : Nat) (z : ℂ) : ℂ :=
  Finset.sum (Finset.range (min m n + 1)) fun j =>
    ((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
      (Nat.choose m j : ℂ) * (Nat.choose n j : ℂ) *
      z ^ (m - j) * (star z) ^ (n - j)

def phi1D (k n : Nat) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    complexHermite n k z

def Phi {d : Nat} (kappa : MultiIndex d) (alpha : Idx d) (z : Cd d) : ℂ :=
  Finset.prod Finset.univ fun q : Fin d => phi1D (kappa q) (alpha q) (z q)

def box {d : Nat} (J : MultiIndex d) : Finset (Idx d) :=
  Fintype.piFinset fun q : Fin d => Finset.range (J q + 1)

noncomputable instance instNormPfin {d : Nat} : Norm (Pfin d) :=
  ⟨fun F => Real.sqrt (Finset.sum F.support fun alpha => ‖F alpha‖ ^ 2)⟩

instance {d : Nat} : Zero (Coeffs d) :=
  ⟨{ coeff := fun _ => 0
     summable_norm_sq := by simp }⟩

instance {d : Nat} : SMul ℂ (Coeffs d) where
  smul c u :=
    { coeff := fun alpha => c * u.coeff alpha
      summable_norm_sq := by
        have hEq :
            (fun alpha : Idx d => ‖c * u.coeff alpha‖ ^ 2) =
              fun alpha => (‖c‖ ^ 2) * (‖u.coeff alpha‖ ^ 2) := by
          funext alpha
          rw [norm_mul, mul_pow]
        rw [hEq]
        exact u.summable_norm_sq.mul_left (‖c‖ ^ 2) }

def coeffPfin {d : Nat} (F : Pfin d) (alpha : Idx d) : ℂ := F alpha

def coeffAt {d : Nat} (F : Coeffs d) (alpha : Idx d) : ℂ :=
  F.coeff alpha

def evalPfin {d : Nat} (kappa : MultiIndex d) (F : Pfin d) : Cd d -> ℂ :=
  fun z => F.sum fun alpha c => c * Phi kappa alpha z

def toFun {d : Nat} (kappa : MultiIndex d) (F : Coeffs d) : Cd d -> ℂ :=
  fun z => ∑' alpha : Idx d, coeffAt F alpha * Phi kappa alpha z

noncomputable def toL2 {d : Nat} (kappa : MultiIndex d) (F : Coeffs d) : L2Tensor d := by
  classical
  exact if h : MeasureTheory.MemLp (toFun kappa F) 2 (gamma_d d) then h.toLp (toFun kappa F) else 0

def ofPfin {d : Nat} (F : Pfin d) : Coeffs d :=
  { coeff := fun alpha => F alpha
    summable_norm_sq := by
      classical
      refine summable_of_hasFiniteSupport ?_
      refine Set.Finite.subset F.support.finite_toSet ?_
      intro alpha halpha
      have hnorm : ‖F alpha‖ ≠ 0 := by simpa using halpha
      exact F.mem_support_iff.mpr (by simpa using hnorm) }


def truncateFinset {d : Nat} (E : Finset (Idx d)) (F : Coeffs d) :
    Pfin d :=
  Finset.sum E fun alpha => Finsupp.single alpha (coeffAt F alpha)


























end ModulusRecovery
