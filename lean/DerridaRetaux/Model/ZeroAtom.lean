import DerridaRetaux.Model.TiltedRecursion
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

/-!
# Positivity of the normalized zero atom

The source treats binary arity separately: at larger arity the fixed normalized mean
forces positive mass at zero, whereas at binary arity zero mass would force the
excluded deterministic fixed point.  Once positive, the exact zero-coefficient
recursion preserves positivity at every generation.
-/

noncomputable section

/-- Positive normalized tilted mass is bounded by the normalized tilted mean. -/
theorem positiveTiltMass_le_normalizedTilt_mean
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    positiveTiltMass m p ≤ 1 / ((m : ℝ) - 1) := by
  have htail :
      HasSum (fun j : ℕ ↦ normalizedTilt m p (j + 1)) (positiveTiltMass m p) := by
    simpa [positiveTiltMass, zeroTilt] using
      (hasSum_nat_add_iff' (f := normalizedTilt m p) 1).2
        (normalizedTilt_hasSum m p hm hcrit)
  have hweighted :
      HasSum (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * normalizedTilt m p (j + 1))
        (1 / ((m : ℝ) - 1)) := by
    simpa using
      (hasSum_nat_add_iff'
        (f := fun k : ℕ ↦ (k : ℝ) * normalizedTilt m p k) 1).2
        (normalizedTilt_mean_hasSum m p hm hcrit)
  calc
    positiveTiltMass m p = ∑' j : ℕ, normalizedTilt m p (j + 1) :=
      htail.tsum_eq.symm
    _ ≤ ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * normalizedTilt m p (j + 1) := by
      apply Summable.tsum_le_tsum _ htail.summable hweighted.summable
      intro j
      calc
        normalizedTilt m p (j + 1) =
            1 * normalizedTilt m p (j + 1) := by ring
        _ ≤ ((j + 1 : ℕ) : ℝ) * normalizedTilt m p (j + 1) := by
          apply mul_le_mul_of_nonneg_right _
            (normalizedTilt_nonneg m p hm hcrit (j + 1))
          norm_num
    _ = 1 / ((m : ℝ) - 1) := hweighted.tsum_eq

/-- At arity at least three the normalized zero atom is strictly positive. -/
theorem zeroTilt_pos_of_three_le
    (m : ℕ) (p : ProbabilityMass) (hm : 3 ≤ m) (hcrit : Critical m p) :
    0 < zeroTilt m p := by
  have hmOne : 1 ≤ m := by omega
  have htail := positiveTiltMass_le_normalizedTilt_mean m p hmOne hcrit
  have hden : (1 : ℝ) < (m : ℝ) - 1 := by
    have hmReal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hinv : 1 / ((m : ℝ) - 1) < 1 := by
    simpa using one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hden
  simp only [positiveTiltMass] at htail
  linarith

/-- Binary criticality gives the exact nonnegative tail representation of the zero
atom used in the source's deterministic boundary case. -/
theorem binary_zero_atom_hasSum (p : ProbabilityMass) (hcrit : Critical 2 p) :
    HasSum
      (fun j : ℕ ↦
        (((j + 2 : ℕ) : ℝ) - 1) * (2 : ℝ) ^ (j + 2) * p (j + 2))
      (p 0) := by
  have hfirst := firstMomentScale_hasSum_tiltedMoment_one 2 p hcrit.2.1
  have hzero : HasSum (powerScale (2 : ℝ) p) (tiltedPartition 2 p) := by
    simpa [tiltedPartition_eq_generatingFunction] using
      generatingFunction_hasSum (2 : ℝ) p
        ((tiltSummable_zero_iff_generatingSummable 2 p).mp hcrit.1)
  have hmom : tiltedMoment 2 1 p = tiltedPartition 2 p := by
    have hmom := hcrit.2.2
    norm_num [tiltedPartition] at hmom
    exact hmom
  have hdiff :
      HasSum
        (fun k : ℕ ↦ ((k : ℝ) - 1) * (2 : ℝ) ^ k * p k) 0 := by
    have h := hfirst.sub hzero
    convert h using 1
    · funext k
      simp only [firstMomentScale_apply, powerScale_apply]
      ring
    · rw [hmom]
      ring
  have htail :=
    (hasSum_nat_add_iff'
      (f := fun k : ℕ ↦ ((k : ℝ) - 1) * (2 : ℝ) ^ k * p k) 2).2 hdiff
  convert htail using 1
  · norm_num [Finset.sum_range_succ]

/-- If a binary critical law has no zero atom, it is the deterministic fixed point. -/
theorem binary_eq_diracMass_one_of_zero
    (p : ProbabilityMass) (hcrit : Critical 2 p) (hzero : p 0 = 0) :
    p = diracMass 1 := by
  have htail := binary_zero_atom_hasSum p hcrit
  rw [hzero] at htail
  have hnonneg :
      ∀ j : ℕ,
        0 ≤ (((j + 2 : ℕ) : ℝ) - 1) * (2 : ℝ) ^ (j + 2) * p (j + 2) := by
    intro j
    have hindex : (1 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ j + 2 by omega)
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hindex) (pow_nonneg (by norm_num) (j + 2)))
      (p.nonneg (j + 2))
  have hzeroFunction :
      (fun j : ℕ ↦
        (((j + 2 : ℕ) : ℝ) - 1) * (2 : ℝ) ^ (j + 2) * p (j + 2)) = 0 :=
    (hasSum_zero_iff_of_nonneg hnonneg).mp htail
  have htailAtom : ∀ j : ℕ, p (j + 2) = 0 := by
    intro j
    have hj :
        (((j + 2 : ℕ) : ℝ) - 1) * (2 : ℝ) ^ (j + 2) * p (j + 2) = 0 := by
      simpa using congrFun hzeroFunction j
    have hcoefficient :
        (((j + 2 : ℕ) : ℝ) - 1) * (2 : ℝ) ^ (j + 2) ≠ 0 := by
      have hindex : (1 : ℝ) < ((j + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 < j + 2 by omega)
      exact mul_ne_zero (ne_of_gt (sub_pos.mpr hindex)) (pow_ne_zero _ (by norm_num))
    exact (mul_eq_zero.mp (by simpa only [mul_assoc] using hj)).resolve_left hcoefficient
  have hmassTail : HasSum (fun j : ℕ ↦ p (j + 2)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0) using 1
    funext j
    exact htailAtom j
  have hmassSplit := (hasSum_nat_add_iff' (f := fun k : ℕ ↦ p k) 2).2 p.hasSum_coe
  have hlimit := hmassTail.unique hmassSplit
  have hone : p 1 = 1 := by
    norm_num [Finset.sum_range_succ, hzero] at hlimit
    linarith
  apply ProbabilityMass.ext
  intro k
  cases k with
  | zero => simp [hzero]
  | succ k =>
      cases k with
      | zero => simp [hone]
      | succ j => simp [htailAtom j, diracMass_apply]

/-- Initial zero-atom positivity under exactly the source's admissibility condition. -/
theorem zeroTilt_pos_of_admissible
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p = diracMass 1)) :
    0 < zeroTilt m p := by
  by_cases hmTwo : m = 2
  · subst m
    have hqNonneg := normalizedTilt_nonneg 2 p (by norm_num) hcrit 0
    by_contra hnotPos
    have hqZero : zeroTilt 2 p = 0 := by
      apply le_antisymm (le_of_not_gt hnotPos)
      simpa [zeroTilt] using hqNonneg
    have hG := normalizedTilt_denominator_pos 2 p (by norm_num) hcrit
    have hpZero : p 0 = 0 := by
      rw [zeroTilt_eq] at hqZero
      exact (div_eq_zero_iff.mp hqZero).resolve_right hG.ne'
    exact hnotBinaryFixedPoint
      ⟨rfl, binary_eq_diracMass_one_of_zero p hcrit hpZero⟩
  · exact zeroTilt_pos_of_three_le m p (by omega) hcrit

/-- The exact one-step zero-coefficient recursion preserves strict positivity. -/
theorem zeroTilt_drStepProb_pos
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hx : 0 < zeroTilt m p) :
    0 < zeroTilt m (drStepProb m p) := by
  change 0 < normalizedTilt m (drStepProb m p) 0
  rw [normalizedTilt_drStepProb_zero m p hm hcrit]
  apply div_pos _ (tiltDenom_pos m p hm hcrit)
  have hconv : 0 ≤ convPow m (normalizedTilt m p) 1 :=
    convPow_nonneg m (normalizedTilt m p)
      (normalizedTilt_nonneg m p hm hcrit) 1
  have hmPos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hpositive : 0 < (m : ℝ) * zeroTilt m p ^ m :=
    mul_pos hmPos (pow_pos hx m)
  linarith

/-- The paper-facing step also preserves strict positivity. -/
theorem zeroTilt_drStep_pos
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hx : 0 < zeroTilt m p) :
    0 < zeroTilt m (drStep m p) := by
  rw [drStep_eq_drStepProb]
  exact zeroTilt_drStepProb_pos m p hm hcrit hx

/-- Every generation of an admissible orbit has a strictly positive normalized zero
atom. -/
theorem orbit_zeroTilt_pos
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (n : ℕ) :
    0 < zeroTilt m (orbit m p₀ n) := by
  have hmOne : 1 ≤ m := by omega
  induction n with
  | zero => simpa using
      zeroTilt_pos_of_admissible m p₀ hm hcrit hnotBinaryFixedPoint
  | succ n ih =>
      rw [orbit_succ]
      exact zeroTilt_drStep_pos m (orbit m p₀ n) hmOne
        (orbit_critical m p₀ hmOne hcrit n) ih

end

end DerridaRetaux
