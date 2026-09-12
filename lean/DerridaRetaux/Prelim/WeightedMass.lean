import DerridaRetaux.Prelim.CubicMoment
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Cubic weighted mass of the shifted tilted density

This file supplies the coefficient-level expansion used in source equation
`eq:weightedmass`.  The orbit-specific `O(1/L)` and cubic-moment bounds remain
explicit parameters, so this algebraic module has no published inputs.
-/

/-- The shifted density has a finite cubic moment whenever the normalized tilt does. -/
theorem positiveTiltedDensity_third_summable
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hthird : TiltSummable m 3 p) :
    Summable (fun j : ℕ ↦ (j : ℝ) ^ 3 * positiveTiltedDensity m p j) := by
  have hcube := normalizedTilt_cube_summable m p hthird
  have htail :
      Summable (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1)) :=
    (summable_nat_add_iff 1).2 hcube
  have hdom :
      Summable (fun j : ℕ ↦ ((m : ℝ) - 1) *
        (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1))) :=
    htail.mul_left ((m : ℝ) - 1)
  apply Summable.of_nonneg_of_le
    (f := fun j : ℕ ↦ ((m : ℝ) - 1) *
      (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1)))
  · intro j
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg j) 3)
      (positiveTiltedDensity_nonneg m p hm hcrit j)
  · intro j
    have hfactor : 0 ≤ (m : ℝ) - 1 := (critical_tiltFactor_pos m p hm hcrit).le
    have hq := normalizedTilt_nonneg m p hm hcrit (j + 1)
    have hj : (j : ℝ) ^ 3 ≤ ((j + 1 : ℕ) : ℝ) ^ 3 := by
      gcongr
      exact_mod_cast (Nat.le_succ j)
    rw [positiveTiltedDensity_apply]
    calc
      (j : ℝ) ^ 3 * (((m : ℝ) - 1) * normalizedTilt m p (j + 1)) =
          ((m : ℝ) - 1) * ((j : ℝ) ^ 3 * normalizedTilt m p (j + 1)) := by ring
      _ ≤ ((m : ℝ) - 1) *
          (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1)) := by
        gcongr
  · exact hdom

/-- Reindexing from `q(k)` to `rho(j)` cannot increase the cubic moment, apart from
the literal normalization factor `m-1`. -/
theorem positiveTiltedDensity_third_tsum_le
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hthird : TiltSummable m 3 p) :
    (∑' j : ℕ, (j : ℝ) ^ 3 * positiveTiltedDensity m p j) ≤
      ((m : ℝ) - 1) *
        ∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m p k := by
  have hleft := positiveTiltedDensity_third_summable m p hm hcrit hthird
  have hcube := normalizedTilt_cube_summable m p hthird
  have htail :
      Summable (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1)) :=
    (summable_nat_add_iff 1).2 hcube
  have hdom :
      Summable (fun j : ℕ ↦ ((m : ℝ) - 1) *
        (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1))) :=
    htail.mul_left ((m : ℝ) - 1)
  have hle :
      (∑' j : ℕ, (j : ℝ) ^ 3 * positiveTiltedDensity m p j) ≤
        ∑' j : ℕ, ((m : ℝ) - 1) *
          (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1)) := by
    apply Summable.tsum_le_tsum _ hleft hdom
    intro j
    have hfactor : 0 ≤ (m : ℝ) - 1 := (critical_tiltFactor_pos m p hm hcrit).le
    have hq := normalizedTilt_nonneg m p hm hcrit (j + 1)
    have hj : (j : ℝ) ^ 3 ≤ ((j + 1 : ℕ) : ℝ) ^ 3 := by
      gcongr
      exact_mod_cast (Nat.le_succ j)
    rw [positiveTiltedDensity_apply]
    calc
      (j : ℝ) ^ 3 * (((m : ℝ) - 1) * normalizedTilt m p (j + 1)) =
          ((m : ℝ) - 1) * ((j : ℝ) ^ 3 * normalizedTilt m p (j + 1)) := by ring
      _ ≤ ((m : ℝ) - 1) *
          (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1)) := by
        gcongr
  calc
    (∑' j : ℕ, (j : ℝ) ^ 3 * positiveTiltedDensity m p j) ≤
        ∑' j : ℕ, ((m : ℝ) - 1) *
          (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1)) := hle
    _ = ((m : ℝ) - 1) *
        ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1) :=
      htail.tsum_mul_left ((m : ℝ) - 1)
    _ ≤ ((m : ℝ) - 1) *
        ∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m p k := by
      have hfactor : 0 ≤ (m : ℝ) - 1 := (critical_tiltFactor_pos m p hm hcrit).le
      apply mul_le_mul_of_nonneg_left _ hfactor
      rw [hcube.tsum_eq_zero_add]
      simp

/-- The elementary cubic weight comparison used to avoid any fourth moment. -/
theorem one_add_cube_le_four (y : ℝ) (hy : 0 ≤ y) :
    (1 + y) ^ 3 ≤ 4 * (1 + y ^ 3) := by
  have hfactor : 0 ≤ 3 * (y + 1) * (y - 1) ^ 2 := by positivity
  nlinarith

/-- Finiteness of the cubic weighted `ℓ¹` quantity. -/
theorem weightedL1Three_positiveTiltedDensity_summable
    (m : ℕ) (p : ProbabilityMass) (L : ℝ) (hm : 1 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) (hL : 0 < L) :
    Summable (fun j : ℕ ↦
      (1 + (j : ℝ) / L) ^ 3 * |positiveTiltedDensity m p j|) := by
  have hzero : Summable (positiveTiltedDensity m p) :=
    (positiveTiltedDensity_hasSum m p hm hcrit).summable
  have hthree := positiveTiltedDensity_third_summable m p hm hcrit hthird
  have hdom :
      Summable (fun j : ℕ ↦
        4 * positiveTiltedDensity m p j +
          (4 / L ^ 3) * ((j : ℝ) ^ 3 * positiveTiltedDensity m p j)) :=
    (hzero.mul_left 4).add (hthree.mul_left (4 / L ^ 3))
  apply Summable.of_nonneg_of_le
    (f := fun j : ℕ ↦
      4 * positiveTiltedDensity m p j +
        (4 / L ^ 3) * ((j : ℝ) ^ 3 * positiveTiltedDensity m p j))
  · intro j
    exact mul_nonneg (pow_nonneg (by positivity) 3) (abs_nonneg _)
  · intro j
    have hrho := positiveTiltedDensity_nonneg m p hm hcrit j
    have hy : 0 ≤ (j : ℝ) / L := div_nonneg (Nat.cast_nonneg j) hL.le
    have hpoly := one_add_cube_le_four ((j : ℝ) / L) hy
    rw [abs_of_nonneg hrho]
    calc
      (1 + (j : ℝ) / L) ^ 3 * positiveTiltedDensity m p j ≤
          (4 * (1 + ((j : ℝ) / L) ^ 3)) * positiveTiltedDensity m p j :=
        mul_le_mul_of_nonneg_right hpoly hrho
      _ = 4 * positiveTiltedDensity m p j +
          (4 / L ^ 3) * ((j : ℝ) ^ 3 * positiveTiltedDensity m p j) := by
        ring_nf
  · exact hdom

/-- Explicit algebraic form of source `eq:weightedmass`: an `A/L` positive-mass
bound and a `B L²` cubic-moment bound imply a cubic weighted `ℓ¹` bound of order
`1/L`, with no moment beyond the third. -/
theorem weightedL1Three_positiveTiltedDensity_le
    (m : ℕ) (p : ProbabilityMass) (L A B : ℝ) (hm : 1 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) (hL : 0 < L)
    (hmass : positiveTiltMass m p ≤ A / L)
    (hmoment :
      (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m p k) ≤ B * L ^ 2) :
    weightedL1Three L (positiveTiltedDensity m p) ≤
      4 * ((m : ℝ) - 1) * (A + B) / L := by
  have hweighted := weightedL1Three_positiveTiltedDensity_summable
    m p L hm hcrit hthird hL
  have hzero : Summable (positiveTiltedDensity m p) :=
    (positiveTiltedDensity_hasSum m p hm hcrit).summable
  have hthree := positiveTiltedDensity_third_summable m p hm hcrit hthird
  have hdom :
      Summable (fun j : ℕ ↦
        4 * positiveTiltedDensity m p j +
          (4 / L ^ 3) * ((j : ℝ) ^ 3 * positiveTiltedDensity m p j)) :=
    (hzero.mul_left 4).add (hthree.mul_left (4 / L ^ 3))
  have hpoint : ∀ j : ℕ,
      (1 + (j : ℝ) / L) ^ 3 * |positiveTiltedDensity m p j| ≤
        4 * positiveTiltedDensity m p j +
          (4 / L ^ 3) * ((j : ℝ) ^ 3 * positiveTiltedDensity m p j) := by
    intro j
    have hrho := positiveTiltedDensity_nonneg m p hm hcrit j
    have hy : 0 ≤ (j : ℝ) / L := div_nonneg (Nat.cast_nonneg j) hL.le
    have hpoly := one_add_cube_le_four ((j : ℝ) / L) hy
    rw [abs_of_nonneg hrho]
    calc
      (1 + (j : ℝ) / L) ^ 3 * positiveTiltedDensity m p j ≤
          (4 * (1 + ((j : ℝ) / L) ^ 3)) * positiveTiltedDensity m p j :=
        mul_le_mul_of_nonneg_right hpoly hrho
      _ = 4 * positiveTiltedDensity m p j +
          (4 / L ^ 3) * ((j : ℝ) ^ 3 * positiveTiltedDensity m p j) := by
        ring_nf
  have hsum := Summable.tsum_le_tsum hpoint hweighted hdom
  have hthirdDensity := positiveTiltedDensity_third_tsum_le
    m p hm hcrit hthird
  have hfactor : 0 ≤ (m : ℝ) - 1 := (critical_tiltFactor_pos m p hm hcrit).le
  have hcoef : 0 ≤ 4 / L ^ 3 := by positivity
  unfold weightedL1Three
  calc
    (∑' j : ℕ,
        (1 + (j : ℝ) / L) ^ 3 * |positiveTiltedDensity m p j|) ≤
        ∑' j : ℕ, (4 * positiveTiltedDensity m p j +
          (4 / L ^ 3) * ((j : ℝ) ^ 3 * positiveTiltedDensity m p j)) := hsum
    _ = 4 * (((m : ℝ) - 1) * positiveTiltMass m p) +
        (4 / L ^ 3) *
          (∑' j : ℕ, (j : ℝ) ^ 3 * positiveTiltedDensity m p j) := by
      rw [(hzero.mul_left 4).tsum_add (hthree.mul_left (4 / L ^ 3))]
      rw [hzero.tsum_mul_left, hthree.tsum_mul_left]
      rw [(positiveTiltedDensity_hasSum m p hm hcrit).tsum_eq]
    _ ≤ 4 * (((m : ℝ) - 1) * (A / L)) +
        (4 / L ^ 3) *
          (((m : ℝ) - 1) * (B * L ^ 2)) := by
      have hmass' := mul_le_mul_of_nonneg_left hmass hfactor
      have hmoment' := hthirdDensity.trans
        (mul_le_mul_of_nonneg_left hmoment hfactor)
      exact add_le_add (mul_le_mul_of_nonneg_left hmass' (by norm_num))
        (mul_le_mul_of_nonneg_left hmoment' hcoef)
    _ = 4 * ((m : ℝ) - 1) * (A + B) / L := by
      field_simp [hL.ne']
      ring

/-- The exact first shifted moment in source equation `eq:weightedmass`. -/
theorem positiveTiltedDensity_firstShifted_tsum
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * positiveTiltedDensity m p j = 1 :=
  (positiveTiltedDensity_shiftedMean_hasSum m p hm hcrit).tsum_eq

end

end DerridaRetaux
