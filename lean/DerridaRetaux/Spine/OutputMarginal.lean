import DerridaRetaux.Spine.Allocation
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-!
# Output coefficients of the cubic-spine allocation

The carrier identity leaves the coefficient below after averaging the
distinguished coordinate.  This file proves that coefficient is exactly the
next normalized cubic size-biased marginal, including all zero-carrier rows.

The separate theorem that a concrete tuple-valued `PMF.bind` pushes forward to
this coefficient is not asserted here.
-/

/-- The output coefficient obtained from the averaged allocation identity. -/
def cubicSpineOutputMass
    (m : ℕ) (p : ProbabilityMass) (k : ℕ) : ℝ :=
  cubicCarrier m k * convPow m (normalizedTilt m p) (k + 1) /
    ((m : ℝ) * normalizedCubicMoment m p)

theorem cubicSpineOutputMass_nonneg
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (hJ : 0 < normalizedCubicMoment m p) (k : ℕ) :
    0 ≤ cubicSpineOutputMass m p k := by
  apply div_nonneg
  · exact mul_nonneg (cubicCarrier_nonneg m k hm)
      (convPow_nonneg m (normalizedTilt m p)
        (normalizedTilt_nonneg m p (by omega) hcrit) (k + 1))
  · exact mul_nonneg (Nat.cast_nonneg m) hJ.le

/-- The allocation output coefficient is the next cubic size-biased marginal. -/
theorem cubicSpineOutputMass_eq_nextSizeBiased
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (k : ℕ) :
    cubicSpineOutputMass m p k =
      cubicSizeBiasedLaw m (drStep m p) hm
        (critical_drStep m p (by omega) hcrit)
        (tiltSummable_three_drStep m p (by omega) hcrit hthird)
        (normalizedCubicMoment_drStep_pos_of_pos m p hm hcrit hthird hJ) k := by
  cases k with
  | zero =>
      simp [cubicSpineOutputMass, cubicCarrier_zero]
  | succ k =>
      have hD := tiltDenom_pos m p (by omega) hcrit
      have hmReal : (m : ℝ) ≠ 0 := by
        exact_mod_cast (show m ≠ 0 by omega)
      have hnextTilt :
          normalizedTilt m (drStep m p) (k + 1) =
            convPow m (normalizedTilt m p) (k + 2) / tiltDenom m p := by
        rw [drStep_eq_drStepProb]
        exact normalizedTilt_drStepProb_succ m p (by omega) hcrit k
      rw [cubicSpineOutputMass, cubicSizeBiasedLaw_apply, hnextTilt,
        normalizedCubicMoment_drStep m p hm hcrit hthird]
      field_simp [hD.ne', hJ.ne', hmReal]

/-- The output coefficients themselves form a probability mass. -/
def cubicSpineOutputLaw
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) : ProbabilityMass where
  mass := cubicSpineOutputMass m p
  nonneg := cubicSpineOutputMass_nonneg m p hm hcrit hJ
  hasSum_one := by
    have hnext := (cubicSizeBiasedLaw m (drStep m p) hm
      (critical_drStep m p (by omega) hcrit)
      (tiltSummable_three_drStep m p (by omega) hcrit hthird)
      (normalizedCubicMoment_drStep_pos_of_pos m p hm hcrit hthird hJ)).hasSum_coe
    convert hnext using 1
    funext k
    exact cubicSpineOutputMass_eq_nextSizeBiased m p hm hcrit hthird hJ k

@[simp]
theorem cubicSpineOutputLaw_apply
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (k : ℕ) :
    cubicSpineOutputLaw m p hm hcrit hthird hJ k = cubicSpineOutputMass m p k :=
  rfl

theorem cubicSpineOutputLaw_eq_nextSizeBiased
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) :
    cubicSpineOutputLaw m p hm hcrit hthird hJ =
      cubicSizeBiasedLaw m (drStep m p) hm
        (critical_drStep m p (by omega) hcrit)
        (tiltSummable_three_drStep m p (by omega) hcrit hthird)
        (normalizedCubicMoment_drStep_pos_of_pos m p hm hcrit hthird hJ) := by
  apply ProbabilityMass.ext
  exact cubicSpineOutputMass_eq_nextSizeBiased m p hm hcrit hthird hJ

theorem cubicSpineOutputMass_eq_zero_of_carrier_eq_zero
    (m : ℕ) (p : ProbabilityMass) (k : ℕ) (hk : cubicCarrier m k = 0) :
    cubicSpineOutputMass m p k = 0 := by
  simp [cubicSpineOutputMass, hk]

/-- At binary arity, both exceptional output rows have zero weight. -/
theorem cubicSpineOutputMass_two_eq_zero_of_lt_two
    (p : ProbabilityMass) (k : ℕ) (hk : k < 2) :
    cubicSpineOutputMass 2 p k = 0 := by
  have hkCases : k = 0 ∨ k = 1 := by omega
  rcases hkCases with rfl | rfl
  · exact cubicSpineOutputMass_eq_zero_of_carrier_eq_zero 2 p 0 (cubicCarrier_zero 2)
  · exact cubicSpineOutputMass_eq_zero_of_carrier_eq_zero 2 p 1 cubicCarrier_two_one

end

end DerridaRetaux
