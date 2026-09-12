import DerridaRetaux.Model.CoarseRelations
import DerridaRetaux.Model.TiltedRecursion
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Exact readout identities

This file proves the source's exact conversion from the normalized tilted density
back to the original survival probability and atoms, together with the scalar
one-step decrement identity used at the end of the profile proof.  No asymptotic
conclusion is assumed.
-/

noncomputable section

/-- The geometrically weighted density sum appearing in `eq:survivalread`. -/
def survivalReadout (m : ℕ) (p : ProbabilityMass) : ℝ :=
  ∑' j : ℕ, ((m : ℝ) ^ (j + 1))⁻¹ * rho m p j

/-- Summability-safe evaluation of the readout series. -/
theorem survivalReadout_hasSum
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    HasSum (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹ * rho m p j)
      ((((m : ℝ) - 1) / tiltedPartition m p) * survival p) := by
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have h := (survival_hasSum p).mul_left
    (((m : ℝ) - 1) / tiltedPartition m p)
  convert h using 1
  funext j
  simp only [positiveTiltedDensity_apply, normalizedTilt_apply]
  rw [show j + 1 = j + 1 by rfl]
  field_simp only [hG.ne', pow_ne_zero _ hm0]
  ring

/-- Source equation `eq:survivalread`. -/
theorem survival_eq_partition_mul_readout
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    survival p =
      tiltedPartition m p / ((m : ℝ) - 1) * survivalReadout m p := by
  have hmOne : 1 ≤ m := by omega
  have hG := normalizedTilt_denominator_pos m p hmOne hcrit
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  rw [survivalReadout, (survivalReadout_hasSum m p hmOne hcrit).tsum_eq]
  field_simp only [hG.ne', hfactor]
  ring

/-- Exact recovery of each fixed positive original-law atom from `rho`. -/
theorem atom_eq_partition_mul_rho
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (k : ℕ) (hk : 1 ≤ k) :
    p k = tiltedPartition m p / ((m : ℝ) - 1) *
      ((m : ℝ) ^ k)⁻¹ * rho m p (k - 1) := by
  have hmOne : 1 ≤ m := by omega
  have hG := normalizedTilt_denominator_pos m p hmOne hcrit
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  simp only [positiveTiltedDensity_apply, normalizedTilt_apply,
    Nat.sub_add_cancel hk]
  field_simp only [hG.ne', hfactor, pow_ne_zero k hm0]
  ring

/-- Cross-multiplied tilted-partition recursion for the paper-facing step. -/
theorem tiltedPartition_drStep_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hzero : TiltSummable m 0 p) :
    (m : ℝ) * tiltedPartition m (drStep m p) =
      tiltedPartition m p ^ m - p 0 ^ m + (m : ℝ) * p 0 ^ m := by
  rw [drStep_eq_drStepProb]
  exact tiltedPartition_drStepProb_cross m p hm hzero

/-- The exact scalar excess-decrement identity stated after `eq:tv`. -/
theorem excess_step_decrement
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hzero : TiltSummable m 0 p) :
    (m : ℝ) * (excess m p - excess m (drStep m p)) =
      ((m : ℝ) - 1) * (1 - (1 - survival p) ^ m) -
        ((1 + excess m p) ^ m - 1 - (m : ℝ) * excess m p) := by
  have hstep := tiltedPartition_drStep_cross m p hm hzero
  have hpzero : p 0 = 1 - survival p := by
    rw [survival_eq_one_sub_zero]
    ring
  have hpartition : tiltedPartition m p = 1 + excess m p := by
    rw [excess]
    ring
  have hpartitionNext :
      tiltedPartition m (drStep m p) = 1 + excess m (drStep m p) := by
    rw [excess]
    ring
  rw [hpzero, hpartition, hpartitionNext] at hstep
  linear_combination -hstep

/-- Orbit-indexed form of the exact scalar decrement. -/
theorem excess_orbit_decrement
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    (m : ℝ) *
        (excess m (orbit m p₀ n) - excess m (orbit m p₀ (n + 1))) =
      ((m : ℝ) - 1) * (1 - (1 - survival (orbit m p₀ n)) ^ m) -
        ((1 + excess m (orbit m p₀ n)) ^ m - 1 -
          (m : ℝ) * excess m (orbit m p₀ n)) := by
  rw [orbit_succ]
  exact excess_step_decrement m (orbit m p₀ n) hm
    (orbit_tiltSummable_zero m p₀ hm hcrit n)

end

end DerridaRetaux
