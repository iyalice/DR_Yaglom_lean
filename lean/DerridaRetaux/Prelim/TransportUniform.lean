import DerridaRetaux.Model.TransportLimit
import DerridaRetaux.Prelim.AtomTail
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-!
# Uniform lower bound for the zero tilted atom

This file completes the last elementary estimate in unnumbered obligation `U09`.
The exact recurrence from `lem:atomtail` shows that `x_n` dominates the initial
zero atom transported by the finite product `C_n`.  Positivity of the limiting
product therefore gives one constant bounding every inverse `x_n⁻¹`.
-/

/-- The transported initial zero atom is a lower bound for every orbit zero atom. -/
theorem transportProduct_mul_zeroTilt_le_orbitZeroTilt
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    transportProduct m p₀ n * zeroTilt m p₀ ≤
      zeroTilt m (orbit m p₀ n) := by
  induction n with
  | zero => simp [transportProduct_zero]
  | succ n ih =>
      have hcritn := orbit_critical m p₀ (by omega) hcrit n
      have hcoeffNonneg :
          0 ≤ transportCoeff m (orbit m p₀ n) :=
        transportCoeff_nonneg m (orbit m p₀ n) (by omega) hcritn
      have hfirstNonneg : 0 ≤ firstTiltedAtom m p₀ n :=
        normalizedTilt_nonneg m (orbit m p₀ n) (by omega) hcritn 1
      rw [transportProduct_succ,
        orbitZeroTilt_succ_eq_transportCoeff_mul m p₀ (by omega) hcrit n]
      calc
        transportProduct m p₀ n * transportCoeff m (orbit m p₀ n) *
              zeroTilt m p₀ =
            transportCoeff m (orbit m p₀ n) *
              (transportProduct m p₀ n * zeroTilt m p₀) := by ring
        _ ≤ transportCoeff m (orbit m p₀ n) *
              zeroTilt m (orbit m p₀ n) :=
          mul_le_mul_of_nonneg_left ih hcoeffNonneg
        _ ≤ transportCoeff m (orbit m p₀ n) *
              (zeroTilt m (orbit m p₀ n) + firstTiltedAtom m p₀ n) := by
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right hfirstNonneg) hcoeffNonneg

/-- One positive constant uniformly bounds all inverses `x_n⁻¹` from the source. -/
theorem orbitZeroTilt_inverse_uniform
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hdefect : Summable
      (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n))) :
    ∃ B : ℝ, 0 < B ∧
      ∀ n : ℕ, (zeroTilt m (orbit m p₀ n))⁻¹ ≤ B := by
  have hlimitPos := transportProductLimit_pos_of_defect_summable
    m p₀ hm hcrit hnotBinaryFixedPoint hdefect
  have hx₀ := orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint 0
  rw [orbit_zero] at hx₀
  have hlowerPos :
      0 < transportProductLimit m p₀ * zeroTilt m p₀ :=
    mul_pos hlimitPos hx₀
  refine ⟨(transportProductLimit m p₀ * zeroTilt m p₀)⁻¹,
    inv_pos.mpr hlowerPos, ?_⟩
  intro n
  have hproductNonneg := transportProduct_nonneg m p₀ (by omega) hcrit n
  have hx₀Nonneg : 0 ≤ zeroTilt m p₀ := hx₀.le
  have hlower :
      transportProductLimit m p₀ * zeroTilt m p₀ ≤
        zeroTilt m (orbit m p₀ n) := by
    calc
      transportProductLimit m p₀ * zeroTilt m p₀ ≤
          transportProduct m p₀ n * zeroTilt m p₀ :=
        mul_le_mul_of_nonneg_right
          (transportProductLimit_le m p₀ (by omega) hcrit hdefect n)
          hx₀Nonneg
      _ ≤ zeroTilt m (orbit m p₀ n) :=
        transportProduct_mul_zeroTilt_le_orbitZeroTilt
          m p₀ hm hcrit n
  have hxn := orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint n
  exact (inv_le_inv₀ hxn hlowerPos).2 hlower

end

end DerridaRetaux
