import DerridaRetaux.Model.NormalizedTilt
import DerridaRetaux.Model.Observables
import DerridaRetaux.Model.Criticality
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

/-!
# Exact coarse relations among source observables

This file proves the two elementary identities used after source equation `eq:coarse`:
survival is bounded by the tilted excess, and the positive normalized tilted mass is
exactly `(epsilon + survival) / G`.  The estimates are internal consequences of the
mass-function definitions and use no published bound.
-/

noncomputable section

/-- The positive part of the tilted partition is `G - p(0)`. -/
theorem tiltedPositive_hasSum
    (m : ℕ) (p : ProbabilityMass) (hzero : TiltSummable m 0 p) :
    HasSum (fun k : ℕ ↦ (m : ℝ) ^ (k + 1) * p (k + 1))
      (tiltedPartition m p - p 0) := by
  have h := (hasSum_nat_add_iff'
    (f := fun k : ℕ ↦ (m : ℝ) ^ k * p k) 1).2
      (tiltedPartition_hasSum m p hzero)
  simpa using h

/-- Multiplying survival by the arity is bounded by the positive tilted mass. -/
theorem arity_mul_survival_le_tiltedPositive
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hzero : TiltSummable m 0 p) :
    (m : ℝ) * survival p ≤ tiltedPartition m p - p 0 := by
  have hleft :
      HasSum (fun k : ℕ ↦ (m : ℝ) * p (k + 1)) ((m : ℝ) * survival p) :=
    (survival_hasSum p).mul_left (m : ℝ)
  have hright := tiltedPositive_hasSum m p hzero
  calc
    (m : ℝ) * survival p = ∑' k : ℕ, (m : ℝ) * p (k + 1) :=
      hleft.tsum_eq.symm
    _ ≤ ∑' k : ℕ, (m : ℝ) ^ (k + 1) * p (k + 1) := by
      apply Summable.tsum_le_tsum _ hleft.summable hright.summable
      intro k
      have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hpow : (m : ℝ) ≤ (m : ℝ) ^ (k + 1) := by
        calc
          (m : ℝ) = (m : ℝ) * 1 := by ring
          _ ≤ (m : ℝ) * (m : ℝ) ^ k := by
            exact mul_le_mul_of_nonneg_left (one_le_pow₀ hmReal)
              (Nat.cast_nonneg m)
          _ = (m : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      exact mul_le_mul_of_nonneg_right hpow (p.nonneg (k + 1))
    _ = tiltedPartition m p - p 0 := hright.tsum_eq

/-- The source inequality `p <= epsilon / (m - 1)`. -/
theorem survival_le_excess_div
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hzero : TiltSummable m 0 p) :
    survival p ≤ excess m p / ((m : ℝ) - 1) := by
  have hmOne : 1 ≤ m := by omega
  have hmgt : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hfactor : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  apply (le_div_iff₀ hfactor).2
  have hweighted := arity_mul_survival_le_tiltedPositive m p hmOne hzero
  rw [survival_eq_one_sub_zero] at hweighted
  rw [survival_eq_one_sub_zero]
  simp only [excess]
  linarith

/-- Critical-law specialization of the survival/excess inequality. -/
theorem survival_le_excess_div_of_critical
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    survival p ≤ excess m p / ((m : ℝ) - 1) :=
  survival_le_excess_div m p hm hcrit.1

/-- Exact source identity `theta = (epsilon + p) / G`. -/
theorem positiveTiltMass_eq_excess_add_survival_div
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    positiveTiltMass m p =
      (excess m p + survival p) / tiltedPartition m p := by
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  rw [positiveTiltMass, zeroTilt_eq, excess, survival_eq_one_sub_zero]
  field_simp [hG.ne']

/-- Orbit form of the exact positive-tilt identity. -/
theorem positiveTiltMass_orbit_eq
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    positiveTiltMass m (orbit m p₀ n) =
      (excess m (orbit m p₀ n) + survival (orbit m p₀ n)) /
        tiltedPartition m (orbit m p₀ n) :=
  positiveTiltMass_eq_excess_add_survival_div m (orbit m p₀ n) hm
    (orbit_critical m p₀ hm hcrit n)

end

end DerridaRetaux
