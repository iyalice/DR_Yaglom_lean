import DerridaRetaux.Model.TiltedProperties
import Mathlib.Tactic

/-!
# Normalized tilted laws

This file defines the normalized critical tilt
`q(k) = m ^ k * p(k) / G`, where `G` is the tilted partition.  The definitions are
total, but every theorem using the quotient first establishes that `G` is positive.
It also records the zero atom, positive tilted mass, and the shifted density
`rho(j) = (m - 1) * q(j + 1)` used by the profile theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- The normalized tilted coefficient sequence `q(k) = m^k p(k) / G`. -/
def normalizedTilt (m : ℕ) (p : ProbabilityMass) : Seq :=
  fun k ↦ (m : ℝ) ^ k * p k / tiltedPartition m p

/-- The zero atom of the normalized tilted sequence. -/
def zeroTilt (m : ℕ) (p : ProbabilityMass) : ℝ :=
  normalizedTilt m p 0

/-- The normalized tilted mass on the positive integers, written as `1 - q(0)`. -/
def positiveTiltMass (m : ℕ) (p : ProbabilityMass) : ℝ :=
  1 - zeroTilt m p

/-- The shifted positive tilted density `rho(j) = (m - 1) q(j + 1)`. -/
def positiveTiltedDensity (m : ℕ) (p : ProbabilityMass) : Seq :=
  fun j ↦ ((m : ℝ) - 1) * normalizedTilt m p (j + 1)

/-- Source-notation alias for `positiveTiltedDensity`. -/
abbrev rho (m : ℕ) (p : ProbabilityMass) : Seq :=
  positiveTiltedDensity m p

@[simp]
theorem normalizedTilt_apply (m : ℕ) (p : ProbabilityMass) (k : ℕ) :
    normalizedTilt m p k = (m : ℝ) ^ k * p k / tiltedPartition m p :=
  rfl

@[simp]
theorem zeroTilt_eq (m : ℕ) (p : ProbabilityMass) :
    zeroTilt m p = p 0 / tiltedPartition m p := by
  simp [zeroTilt]

@[simp]
theorem positiveTiltedDensity_apply (m : ℕ) (p : ProbabilityMass) (j : ℕ) :
    positiveTiltedDensity m p j =
      ((m : ℝ) - 1) * normalizedTilt m p (j + 1) :=
  rfl

/-- A critical law at an arity at least one in fact has arity at least two.

At `m = 1`, criticality would force the tilted partition to be zero, whereas it is
the total mass one.  This explicitly resolves the denominator boundary in the mean
identity below.
-/
theorem two_le_of_one_le_of_critical (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : 2 ≤ m := by
  by_contra htwo
  have hmone : m = 1 := by omega
  subst m
  have heq := hcrit.2.2
  norm_num at heq
  have hpart : tiltedPartition 1 p = 0 := by
    simpa [tiltedPartition] using heq.symm
  rw [tiltedPartition_one] at hpart
  norm_num at hpart

/-- The factor `m - 1` is strictly positive under the admissible critical hypotheses. -/
theorem critical_tiltFactor_pos (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : 0 < (m : ℝ) - 1 := by
  have htwo := two_le_of_one_le_of_critical m p hm hcrit
  have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast htwo
  linarith

/-- The normalizing denominator is positive before the quotient is used. -/
theorem normalizedTilt_denominator_pos (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : 0 < tiltedPartition m p :=
  tiltedPartition_pos_of_critical m p hm hcrit

/-- Every normalized tilted coefficient is nonnegative. -/
theorem normalizedTilt_nonneg (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) (k : ℕ) : 0 ≤ normalizedTilt m p k := by
  exact div_nonneg
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg m) k) (p.nonneg k))
    (normalizedTilt_denominator_pos m p hm hcrit).le

/-- The normalized tilted coefficients sum to one. -/
theorem normalizedTilt_hasSum (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : HasSum (normalizedTilt m p) 1 := by
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  simpa [normalizedTilt, hG.ne'] using
    (tiltedPartition_hasSum m p hcrit.1).div_const (tiltedPartition m p)

/-- The normalized tilted sequence is summable. -/
theorem normalizedTilt_summable (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : Summable (normalizedTilt m p) :=
  (normalizedTilt_hasSum m p hm hcrit).summable

/-- The `tsum` form of normalization. -/
@[simp]
theorem normalizedTilt_tsum_eq_one (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : ∑' k : ℕ, normalizedTilt m p k = 1 :=
  (normalizedTilt_hasSum m p hm hcrit).tsum_eq

/-- Bundle the normalized tilt as a real-valued probability mass. -/
def normalizedTiltLaw (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : ProbabilityMass where
  mass := normalizedTilt m p
  nonneg := normalizedTilt_nonneg m p hm hcrit
  hasSum_one := normalizedTilt_hasSum m p hm hcrit

@[simp]
theorem normalizedTiltLaw_apply (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) (k : ℕ) :
    normalizedTiltLaw m p hm hcrit k = normalizedTilt m p k :=
  rfl

/-- The positive tilted mass is the tail sum over strictly positive indices. -/
theorem positiveTiltMass_eq_tsum_succ (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    positiveTiltMass m p = ∑' j : ℕ, normalizedTilt m p (j + 1) := by
  have hsummable := normalizedTilt_summable m p hm hcrit
  have hsplit := hsummable.tsum_eq_zero_add
  rw [normalizedTilt_tsum_eq_one m p hm hcrit] at hsplit
  change 1 - normalizedTilt m p 0 = ∑' j : ℕ, normalizedTilt m p (j + 1)
  linarith

/-- The positive tilted mass is nonnegative. -/
theorem positiveTiltMass_nonneg (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : 0 ≤ positiveTiltMass m p := by
  rw [positiveTiltMass_eq_tsum_succ m p hm hcrit]
  exact tsum_nonneg fun j ↦ normalizedTilt_nonneg m p hm hcrit (j + 1)

/-- The shifted positive tilted density is pointwise nonnegative. -/
theorem positiveTiltedDensity_nonneg (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) (j : ℕ) : 0 ≤ positiveTiltedDensity m p j := by
  exact mul_nonneg (critical_tiltFactor_pos m p hm hcrit).le
    (normalizedTilt_nonneg m p hm hcrit (j + 1))

/-- The total density mass is `(m - 1)` times the positive tilted mass. -/
theorem positiveTiltedDensity_hasSum (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    HasSum (positiveTiltedDensity m p)
      (((m : ℝ) - 1) * positiveTiltMass m p) := by
  have htail :
      HasSum (fun j : ℕ ↦ normalizedTilt m p (j + 1)) (positiveTiltMass m p) := by
    simpa [positiveTiltMass, zeroTilt] using
      (hasSum_nat_add_iff' (f := normalizedTilt m p) 1).2
        (normalizedTilt_hasSum m p hm hcrit)
  simpa [positiveTiltedDensity] using htail.mul_left ((m : ℝ) - 1)

/-- Criticality gives the normalized tilted law mean `1 / (m - 1)`. -/
theorem normalizedTilt_mean_hasSum (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    HasSum (fun k : ℕ ↦ (k : ℝ) * normalizedTilt m p k)
      (1 / ((m : ℝ) - 1)) := by
  have hfactor := critical_tiltFactor_pos m p hm hcrit
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  have hmoment :
      HasSum (fun k : ℕ ↦ (k : ℝ) * (m : ℝ) ^ k * p k) (tiltedMoment m 1 p) := by
    simpa [TiltSummable, tiltedMoment] using hcrit.2.1.hasSum
  have hquot := hmoment.div_const (tiltedPartition m p)
  have hvalue : tiltedMoment m 1 p / tiltedPartition m p = 1 / ((m : ℝ) - 1) := by
    apply (div_eq_div_iff hG.ne' hfactor.ne').2
    simpa [tiltedPartition, mul_comm] using hcrit.2.2
  rw [hvalue] at hquot
  convert hquot using 1
  funext k
  simp only [normalizedTilt]
  ring

/-- The `tsum` form of the normalized tilted mean identity. -/
theorem normalizedTilt_mean (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    ∑' k : ℕ, (k : ℝ) * normalizedTilt m p k = 1 / ((m : ℝ) - 1) :=
  (normalizedTilt_mean_hasSum m p hm hcrit).tsum_eq

/-- At binary arity, the normalized tilted mean is exactly one. -/
theorem normalizedTilt_mean_two (p : ProbabilityMass) (hcrit : Critical 2 p) :
    ∑' k : ℕ, (k : ℝ) * normalizedTilt 2 p k = 1 := by
  have hmean := normalizedTilt_mean 2 p (by norm_num) hcrit
  norm_num at hmean
  exact hmean

/-- Equivalently, the shifted density has first shifted moment one. -/
theorem positiveTiltedDensity_shiftedMean_hasSum (m : ℕ) (p : ProbabilityMass)
    (hm : 1 ≤ m) (hcrit : Critical m p) :
    HasSum (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * positiveTiltedDensity m p j) 1 := by
  have hfactor := critical_tiltFactor_pos m p hm hcrit
  have htail :
      HasSum (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * normalizedTilt m p (j + 1))
        (1 / ((m : ℝ) - 1)) := by
    simpa using
      (hasSum_nat_add_iff'
        (f := fun k : ℕ ↦ (k : ℝ) * normalizedTilt m p k) 1).2
        (normalizedTilt_mean_hasSum m p hm hcrit)
  have hscaled := htail.mul_left ((m : ℝ) - 1)
  convert hscaled using 1
  · funext j
    simp only [positiveTiltedDensity]
    ring
  · field_simp

end

end DerridaRetaux
