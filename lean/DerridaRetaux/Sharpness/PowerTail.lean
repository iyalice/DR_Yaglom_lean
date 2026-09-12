import DerridaRetaux.Basic.ProbabilityMass
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Explicit power-tail laws for the sharpness branch

This file contains only the internal heavy-tail construction.  It does not import
the external Chen--Shi input.  Natural indices are shifted by two throughout the
infinite tail, so every use of `Real.rpow` has a strictly positive base.
-/

noncomputable section

/-- An explicit exponent in `(max {3, r + 1}, 4)` whenever `0 ≤ r < 3`. -/
def sharpPowerExponent (r : ℝ) : ℝ :=
  7 / 2 + r / 6

theorem three_lt_sharpPowerExponent (r : ℝ) (hr : 0 ≤ r) :
    3 < sharpPowerExponent r := by
  simp only [sharpPowerExponent]
  linarith

theorem add_one_lt_sharpPowerExponent (r : ℝ) (hr : r < 3) :
    r + 1 < sharpPowerExponent r := by
  simp only [sharpPowerExponent]
  linarith

theorem sharpPowerExponent_lt_four (r : ℝ) (hr : r < 3) :
    sharpPowerExponent r < 4 := by
  simp only [sharpPowerExponent]
  linarith

theorem max_three_add_one_lt_sharpPowerExponent (r : ℝ) (hr₀ : 0 ≤ r)
    (hr₃ : r < 3) :
    max 3 (r + 1) < sharpPowerExponent r := by
  rw [max_lt_iff]
  exact ⟨three_lt_sharpPowerExponent r hr₀, add_one_lt_sharpPowerExponent r hr₃⟩

/-- The shifted real-power series with terms `(n + 2)^β`. -/
def shiftedRpowSeries (β : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n + 2 : ℝ) β

@[simp]
theorem shiftedRpowSeries_apply (β : ℝ) (n : ℕ) :
    shiftedRpowSeries β n = Real.rpow (n + 2 : ℝ) β :=
  rfl

/-- Exact p-series threshold after removing the first two indices. -/
theorem shiftedRpowSeries_summable_iff (β : ℝ) :
    Summable (shiftedRpowSeries β) ↔ β < -1 := by
  change Summable (fun n : ℕ ↦ Real.rpow (n + 2 : ℝ) β) ↔ β < -1
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    ((summable_nat_add_iff (f := fun n : ℕ ↦ Real.rpow (n : ℝ) β) 2).trans
      Real.summable_nat_rpow)

/-- Multiplying two real powers on the shifted positive indices adds exponents. -/
theorem shiftedRpow_mul (s α : ℝ) (n : ℕ) :
    Real.rpow (n + 2 : ℝ) s * Real.rpow (n + 2 : ℝ) (-α) =
      shiftedRpowSeries (s - α) n := by
  have hpos : (0 : ℝ) < n + 2 := by positivity
  calc
    Real.rpow (n + 2 : ℝ) s * Real.rpow (n + 2 : ℝ) (-α) =
        Real.rpow (n + 2 : ℝ) (s + -α) := (Real.rpow_add hpos s (-α)).symm
    _ = shiftedRpowSeries (s - α) n := by
      rw [shiftedRpowSeries_apply]
      congr 1

/-- Exact moment threshold for a shifted `k^{-α}` tail. -/
theorem shiftedPowerTailMoment_summable_iff (s α : ℝ) :
    Summable
        (fun n : ℕ ↦
          Real.rpow (n + 2 : ℝ) s * Real.rpow (n + 2 : ℝ) (-α)) ↔
      s < α - 1 := by
  have heq :
      (fun n : ℕ ↦ Real.rpow (n + 2 : ℝ) s * Real.rpow (n + 2 : ℝ) (-α)) =
        shiftedRpowSeries (s - α) := by
    funext n
    exact shiftedRpow_mul s α n
  rw [heq, shiftedRpowSeries_summable_iff]
  constructor <;> intro h <;> linarith

/-- The third power moment diverges for every tail exponent below four. -/
theorem shiftedPowerTail_third_not_summable (α : ℝ) (hα : α < 4) :
    ¬Summable
      (fun n : ℕ ↦
        Real.rpow (n + 2 : ℝ) 3 * Real.rpow (n + 2 : ℝ) (-α)) := by
  rw [shiftedPowerTailMoment_summable_iff]
  linarith

/-- Total mass of the unscaled `k^{-α}` tail on `k ≥ 2`. -/
def powerTailMassSum (α : ℝ) : ℝ :=
  ∑' n : ℕ, shiftedRpowSeries (-α) n

/-- First moment of the unscaled `k^{-α}` tail on `k ≥ 2`. -/
def powerTailFirstSum (α : ℝ) : ℝ :=
  ∑' n : ℕ, shiftedRpowSeries (1 - α) n

theorem powerTailMass_summable (α : ℝ) (hα : 1 < α) :
    Summable (shiftedRpowSeries (-α)) := by
  rw [shiftedRpowSeries_summable_iff]
  linarith

theorem powerTailFirst_summable (α : ℝ) (hα : 2 < α) :
    Summable (shiftedRpowSeries (1 - α)) := by
  rw [shiftedRpowSeries_summable_iff]
  linarith

theorem powerTailMassSum_pos (α : ℝ) (hα : 1 < α) :
    0 < powerTailMassSum α := by
  exact (powerTailMass_summable α hα).tsum_pos
    (fun n ↦ Real.rpow_nonneg (by positivity) (-α)) 0
    (Real.rpow_pos_of_pos (by norm_num) (-α))

theorem powerTailFirstSum_pos (α : ℝ) (hα : 2 < α) :
    0 < powerTailFirstSum α := by
  exact (powerTailFirst_summable α hα).tsum_pos
    (fun n ↦ Real.rpow_nonneg (by positivity) (1 - α)) 0
    (Real.rpow_pos_of_pos (by norm_num) (1 - α))

/-- For `α > 2`, the first tail sum strictly dominates the mass tail sum. -/
theorem powerTailMassSum_lt_firstSum (α : ℝ) (hα : 2 < α) :
    powerTailMassSum α < powerTailFirstSum α := by
  rw [powerTailMassSum, powerTailFirstSum]
  refine Summable.tsum_lt_tsum
    (f := shiftedRpowSeries (-α)) (g := shiftedRpowSeries (1 - α))
    (i := (0 : ℕ)) ?_ ?_ (powerTailMass_summable α (by linarith))
      (powerTailFirst_summable α hα)
  · intro n
    change Real.rpow (n + 2 : ℝ) (-α) ≤ Real.rpow (n + 2 : ℝ) (1 - α)
    have hnNat : 1 < n + 2 := by omega
    have hn : (1 : ℝ) < (n : ℝ) + 2 := by exact_mod_cast hnNat
    exact (Real.rpow_lt_rpow_of_exponent_lt (x := (n : ℝ) + 2) hn
      (by linarith : -α < 1 - α)).le
  · simp only [shiftedRpowSeries_apply, Nat.cast_zero, zero_add]
    exact Real.rpow_lt_rpow_of_exponent_lt (x := (2 : ℝ)) (by norm_num)
      (by linarith : -α < 1 - α)

/-- The explicit small constant `1 / (2 (m - 1) S₁)`. -/
def sharpTailConstant (m : ℕ) (α : ℝ) : ℝ :=
  1 / (2 * ((m : ℝ) - 1) * powerTailFirstSum α)

theorem sharpTailConstant_pos (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    0 < sharpTailConstant m α := by
  rw [sharpTailConstant, one_div_pos]
  have hmReal : (1 : ℝ) < m := by exact_mod_cast hm
  exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hmReal))
    (powerTailFirstSum_pos α hα)

theorem sharpTailConstant_mul_firstSum
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    sharpTailConstant m α * powerTailFirstSum α =
      1 / (2 * ((m : ℝ) - 1)) := by
  have hmReal : (1 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hmReal)
  have hsum0 : powerTailFirstSum α ≠ 0 :=
    ne_of_gt (powerTailFirstSum_pos α hα)
  rw [sharpTailConstant]
  field_simp
  ring

/-- The first atom left after subtracting the explicit tail mean. -/
theorem one_div_sub_sharpTailConstant_mul_firstSum
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    1 / ((m : ℝ) - 1) - sharpTailConstant m α * powerTailFirstSum α =
      1 / (2 * ((m : ℝ) - 1)) := by
  rw [sharpTailConstant_mul_firstSum m α hm hα]
  have hmReal : (1 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hmReal)
  field_simp
  ring

/-- The source's tilted law before normalization back to the original coordinates. -/
def sharpTiltedSeq (m : ℕ) (α : ℝ) : Seq
  | 0 =>
      1 - 1 / ((m : ℝ) - 1) +
        sharpTailConstant m α * (powerTailFirstSum α - powerTailMassSum α)
  | 1 => 1 / ((m : ℝ) - 1) - sharpTailConstant m α * powerTailFirstSum α
  | k + 2 => sharpTailConstant m α * Real.rpow (k + 2 : ℝ) (-α)

@[simp]
theorem sharpTiltedSeq_zero (m : ℕ) (α : ℝ) :
    sharpTiltedSeq m α 0 =
      1 - 1 / ((m : ℝ) - 1) +
        sharpTailConstant m α * (powerTailFirstSum α - powerTailMassSum α) :=
  rfl

@[simp]
theorem sharpTiltedSeq_one (m : ℕ) (α : ℝ) :
    sharpTiltedSeq m α 1 =
      1 / ((m : ℝ) - 1) - sharpTailConstant m α * powerTailFirstSum α :=
  rfl

@[simp]
theorem sharpTiltedSeq_tail (m : ℕ) (α : ℝ) (k : ℕ) :
    sharpTiltedSeq m α (k + 2) =
      sharpTailConstant m α * Real.rpow (k + 2 : ℝ) (-α) :=
  rfl

theorem one_div_m_sub_one_le_one (m : ℕ) (hm : 2 ≤ m) :
    1 / ((m : ℝ) - 1) ≤ 1 := by
  have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  apply (div_le_one (by linarith : (0 : ℝ) < m - 1)).mpr
  linarith

theorem sharpTiltedSeq_zero_pos
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    0 < sharpTiltedSeq m α 0 := by
  rw [sharpTiltedSeq_zero]
  have hbase : 0 ≤ 1 - 1 / ((m : ℝ) - 1) :=
    sub_nonneg.mpr (one_div_m_sub_one_le_one m hm)
  have htail : 0 < powerTailFirstSum α - powerTailMassSum α :=
    sub_pos.mpr (powerTailMassSum_lt_firstSum α hα)
  exact add_pos_of_nonneg_of_pos hbase (mul_pos (sharpTailConstant_pos m α hm hα) htail)

theorem sharpTiltedSeq_one_eq_half
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    sharpTiltedSeq m α 1 = 1 / (2 * ((m : ℝ) - 1)) := by
  rw [sharpTiltedSeq_one, one_div_sub_sharpTailConstant_mul_firstSum m α hm hα]

theorem sharpTiltedSeq_one_pos
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    0 < sharpTiltedSeq m α 1 := by
  rw [sharpTiltedSeq_one_eq_half m α hm hα, one_div_pos]
  have hmReal : (1 : ℝ) < m := by exact_mod_cast hm
  exact mul_pos (by norm_num) (sub_pos.mpr hmReal)

theorem sharpTiltedSeq_tail_pos
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    0 < sharpTiltedSeq m α (k + 2) := by
  rw [sharpTiltedSeq_tail]
  exact mul_pos (sharpTailConstant_pos m α hm hα)
    (Real.rpow_pos_of_pos (by positivity) (-α))

theorem sharpTiltedSeq_nonneg
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    0 ≤ sharpTiltedSeq m α k := by
  rcases k with (_ | _ | k)
  · exact (sharpTiltedSeq_zero_pos m α hm hα).le
  · exact (sharpTiltedSeq_one_pos m α hm hα).le
  · exact (sharpTiltedSeq_tail_pos m α hm hα k).le

theorem sharpTiltedSeq_tail_hasSum
    (m : ℕ) (α : ℝ) (hα : 1 < α) :
    HasSum (fun k : ℕ ↦ sharpTiltedSeq m α (k + 2))
      (sharpTailConstant m α * powerTailMassSum α) := by
  have h := (powerTailMass_summable α hα).hasSum.mul_left
    (sharpTailConstant m α)
  simpa [powerTailMassSum, sharpTiltedSeq_tail, shiftedRpowSeries] using h

/-- The tilted atoms have total mass one. -/
theorem sharpTiltedSeq_hasSum_one
    (m : ℕ) (α : ℝ) (hα : 1 < α) :
    HasSum (sharpTiltedSeq m α) 1 := by
  have h := (hasSum_nat_add_iff (f := sharpTiltedSeq m α) 2).mp
    (sharpTiltedSeq_tail_hasSum m α hα)
  convert h using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    sharpTiltedSeq_zero, sharpTiltedSeq_one]
  ring

theorem sharpTiltedSeq_first_tail_hasSum
    (m : ℕ) (α : ℝ) (hα : 2 < α) :
    HasSum (fun k : ℕ ↦ (k + 2 : ℕ) * sharpTiltedSeq m α (k + 2))
      (sharpTailConstant m α * powerTailFirstSum α) := by
  have h := (powerTailFirst_summable α hα).hasSum.mul_left (sharpTailConstant m α)
  convert h using 1
  funext k
  rw [sharpTiltedSeq_tail]
  calc
    ((k + 2 : ℕ) : ℝ) *
          (sharpTailConstant m α * Real.rpow (k + 2 : ℝ) (-α)) =
        sharpTailConstant m α *
          (Real.rpow (k + 2 : ℝ) 1 * Real.rpow (k + 2 : ℝ) (-α)) := by
      rw [Nat.cast_add, Nat.cast_ofNat]
      have hone : Real.rpow ((k : ℝ) + 2) 1 = (k : ℝ) + 2 := Real.rpow_one _
      rw [hone]
      ring
    _ = sharpTailConstant m α * shiftedRpowSeries (1 - α) k := by
      rw [shiftedRpow_mul]

/-- The tilted law has mean exactly `1 / (m - 1)`. -/
theorem sharpTiltedSeq_first_hasSum
    (m : ℕ) (α : ℝ) (hα : 2 < α) :
    HasSum (fun k : ℕ ↦ (k : ℝ) * sharpTiltedSeq m α k) (1 / ((m : ℝ) - 1)) := by
  have h :=
    (hasSum_nat_add_iff (f := fun k : ℕ ↦ (k : ℝ) * sharpTiltedSeq m α k) 2).mp
      (sharpTiltedSeq_first_tail_hasSum m α hα)
  convert h using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, zero_mul, Nat.cast_one, one_mul, sharpTiltedSeq_one]
  ring

/-- The normalized tilted probability law `q₀`. -/
def sharpTiltedLaw (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) : ProbabilityMass where
  mass := sharpTiltedSeq m α
  nonneg := sharpTiltedSeq_nonneg m α hm hα
  hasSum_one := sharpTiltedSeq_hasSum_one m α (by linarith)

@[simp]
theorem sharpTiltedLaw_apply
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    sharpTiltedLaw m α hm hα k = sharpTiltedSeq m α k :=
  rfl

theorem sharpTiltedLaw_first_hasSum
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    HasSum (fun k : ℕ ↦ (k : ℝ) * sharpTiltedLaw m α hm hα k)
      (1 / ((m : ℝ) - 1)) :=
  sharpTiltedSeq_first_hasSum m α hα

/-- The exponentially downweighted tilted coefficients before normalization. -/
def sharpOriginalWeight (m : ℕ) (α : ℝ) (k : ℕ) : ℝ :=
  (m : ℝ)⁻¹ ^ k * sharpTiltedSeq m α k

/-- The normalizing denominator used to return from tilted to original coordinates. -/
def sharpNormalizingDenominator (m : ℕ) (α : ℝ) : ℝ :=
  ∑' k : ℕ, sharpOriginalWeight m α k

/-- The reciprocal normalizing constant used to define the original law. -/
def sharpNormalizingConstant (m : ℕ) (α : ℝ) : ℝ :=
  (sharpNormalizingDenominator m α)⁻¹

theorem sharpOriginalWeight_summable
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    Summable (sharpOriginalWeight m α) := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hminv_nonneg : (0 : ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr hmpos.le
  have hminv_le_one : (m : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hmpos]
    exact_mod_cast (show 1 ≤ m by omega)
  apply (sharpTiltedLaw m α hm hα).summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (pow_nonneg hminv_nonneg k)
      (sharpTiltedSeq_nonneg m α hm hα k)
  · intro k
    rw [sharpOriginalWeight]
    exact mul_le_of_le_one_left (sharpTiltedSeq_nonneg m α hm hα k)
      (pow_le_one₀ hminv_nonneg hminv_le_one)

theorem sharpNormalizingDenominator_pos
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    0 < sharpNormalizingDenominator m α := by
  rw [sharpNormalizingDenominator]
  exact (sharpOriginalWeight_summable m α hm hα).tsum_pos
    (fun k ↦ mul_nonneg (pow_nonneg (inv_nonneg.mpr (by positivity)) k)
      (sharpTiltedSeq_nonneg m α hm hα k)) 0
    (by simpa [sharpOriginalWeight] using sharpTiltedSeq_zero_pos m α hm hα)

theorem sharpNormalizingConstant_pos
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    0 < sharpNormalizingConstant m α := by
  rw [sharpNormalizingConstant]
  exact inv_pos.mpr (sharpNormalizingDenominator_pos m α hm hα)

/-- The original-coordinate sequence obtained by undoing the exponential tilt. -/
def sharpOriginalSeq (m : ℕ) (α : ℝ) (k : ℕ) : ℝ :=
  sharpNormalizingConstant m α * sharpOriginalWeight m α k

theorem sharpOriginalSeq_nonneg
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    0 ≤ sharpOriginalSeq m α k := by
  exact mul_nonneg (sharpNormalizingConstant_pos m α hm hα).le
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr (by positivity)) k)
      (sharpTiltedSeq_nonneg m α hm hα k))

theorem sharpOriginalSeq_hasSum_one
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    HasSum (sharpOriginalSeq m α) 1 := by
  have h := (sharpOriginalWeight_summable m α hm hα).hasSum.mul_left
    (sharpNormalizingConstant m α)
  change HasSum
    (fun k : ℕ ↦ sharpNormalizingConstant m α * sharpOriginalWeight m α k) 1
  convert h using 1
  rw [sharpNormalizingConstant, sharpNormalizingDenominator]
  exact (inv_mul_cancel₀
    (ne_of_gt (sharpNormalizingDenominator_pos m α hm hα))).symm

/-- The normalized original probability law with the prescribed power tail. -/
def sharpOriginalLaw
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) : ProbabilityMass where
  mass := sharpOriginalSeq m α
  nonneg := sharpOriginalSeq_nonneg m α hm hα
  hasSum_one := sharpOriginalSeq_hasSum_one m α hm hα

@[simp]
theorem sharpOriginalLaw_apply
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    sharpOriginalLaw m α hm hα k = sharpOriginalSeq m α k :=
  rfl

/-- Exact formula for every original-coordinate tail atom. -/
@[simp]
theorem sharpOriginalLaw_tail
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    sharpOriginalLaw m α hm hα (k + 2) =
      sharpNormalizingConstant m α * (m : ℝ)⁻¹ ^ (k + 2) *
        sharpTailConstant m α * Real.rpow (k + 2 : ℝ) (-α) := by
  rw [sharpOriginalLaw_apply, sharpOriginalSeq, sharpOriginalWeight,
    sharpTiltedSeq_tail]
  ring

/-- Multiplication by `m^k` exactly cancels the inverse exponential tilt. -/
theorem sharpOriginalLaw_tilted_coeff
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    (m : ℝ) ^ k * sharpOriginalLaw m α hm hα k =
      sharpNormalizingConstant m α * sharpTiltedLaw m α hm hα k := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hcancel : (m : ℝ) ^ k * (m : ℝ)⁻¹ ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hm0, one_pow]
  rw [sharpOriginalLaw_apply, sharpOriginalSeq, sharpOriginalWeight,
    sharpTiltedLaw_apply]
  calc
    (m : ℝ) ^ k *
          (sharpNormalizingConstant m α * ((m : ℝ)⁻¹ ^ k * sharpTiltedSeq m α k)) =
        sharpNormalizingConstant m α *
          (((m : ℝ) ^ k * (m : ℝ)⁻¹ ^ k) * sharpTiltedSeq m α k) := by
      ring
    _ = sharpNormalizingConstant m α * sharpTiltedSeq m α k := by
      rw [hcancel, one_mul]

theorem sharpOriginalLaw_tilted_zero_hasSum
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    HasSum
        (fun k : ℕ ↦ (k : ℝ) ^ 0 * (m : ℝ) ^ k *
          sharpOriginalLaw m α hm hα k)
      (sharpNormalizingConstant m α) := by
  have h := (sharpTiltedLaw m α hm hα).hasSum_coe.mul_left
    (sharpNormalizingConstant m α)
  convert h using 1
  · funext k
    rw [pow_zero, one_mul, sharpOriginalLaw_tilted_coeff]
  · ring

theorem sharpOriginalLaw_tilted_first_hasSum
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    HasSum
        (fun k : ℕ ↦ (k : ℝ) ^ 1 * (m : ℝ) ^ k *
          sharpOriginalLaw m α hm hα k)
      (sharpNormalizingConstant m α / ((m : ℝ) - 1)) := by
  have h := (sharpTiltedLaw_first_hasSum m α hm hα).mul_left
    (sharpNormalizingConstant m α)
  convert h using 1
  · funext k
    rw [pow_one]
    calc
      (k : ℝ) * (m : ℝ) ^ k * sharpOriginalLaw m α hm hα k =
          (k : ℝ) * ((m : ℝ) ^ k * sharpOriginalLaw m α hm hα k) := by
        ring
      _ = (k : ℝ) *
          (sharpNormalizingConstant m α * sharpTiltedLaw m α hm hα k) := by
        rw [sharpOriginalLaw_tilted_coeff]
      _ = sharpNormalizingConstant m α *
          ((k : ℝ) * sharpTiltedLaw m α hm hα k) := by
        ring
  · ring

theorem sharpOriginalLaw_tiltSummable_zero
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    TiltSummable m 0 (sharpOriginalLaw m α hm hα) :=
  (sharpOriginalLaw_tilted_zero_hasSum m α hm hα).summable

theorem sharpOriginalLaw_tiltSummable_one
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    TiltSummable m 1 (sharpOriginalLaw m α hm hα) :=
  (sharpOriginalLaw_tilted_first_hasSum m α hm hα).summable

@[simp]
theorem sharpOriginalLaw_tiltedMoment_zero
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    tiltedMoment m 0 (sharpOriginalLaw m α hm hα) =
      sharpNormalizingConstant m α :=
  tiltedMoment_eq_of_hasSum m 0 (sharpOriginalLaw m α hm hα)
    (sharpNormalizingConstant m α)
    (sharpOriginalLaw_tilted_zero_hasSum m α hm hα)

@[simp]
theorem sharpOriginalLaw_tiltedMoment_one
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    tiltedMoment m 1 (sharpOriginalLaw m α hm hα) =
      sharpNormalizingConstant m α / ((m : ℝ) - 1) :=
  tiltedMoment_eq_of_hasSum m 1 (sharpOriginalLaw m α hm hα)
    (sharpNormalizingConstant m α / ((m : ℝ) - 1))
    (sharpOriginalLaw_tilted_first_hasSum m α hm hα)

/-- The normalized original law satisfies the Derrida--Retaux criticality identity. -/
theorem sharpOriginalLaw_critical
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    Critical m (sharpOriginalLaw m α hm hα) := by
  refine ⟨sharpOriginalLaw_tiltSummable_zero m α hm hα,
    sharpOriginalLaw_tiltSummable_one m α hm hα, ?_⟩
  rw [sharpOriginalLaw_tiltedMoment_zero, sharpOriginalLaw_tiltedMoment_one]
  have hmReal : (1 : ℝ) < m := by exact_mod_cast hm
  field_simp [ne_of_gt (sub_pos.mpr hmReal)]

theorem sharpOriginalLaw_zero_pos
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    0 < sharpOriginalLaw m α hm hα 0 := by
  rw [sharpOriginalLaw_apply, sharpOriginalSeq, sharpOriginalWeight]
  simpa using mul_pos (sharpNormalizingConstant_pos m α hm hα)
    (sharpTiltedSeq_zero_pos m α hm hα)

theorem sharpOriginalLaw_tail_pos
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    0 < sharpOriginalLaw m α hm hα (k + 2) := by
  rw [sharpOriginalLaw_tail]
  exact mul_pos
    (mul_pos
      (mul_pos (sharpNormalizingConstant_pos m α hm hα)
        (pow_pos (inv_pos.mpr (by positivity)) (k + 2)))
      (sharpTailConstant_pos m α hm hα))
    (Real.rpow_pos_of_pos (by positivity) (-α))

/-- The power-tail law is never a Dirac mass. -/
theorem sharpOriginalLaw_not_isDirac
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    ¬IsDirac (sharpOriginalLaw m α hm hα) := by
  rintro ⟨j, hj⟩
  by_cases hj0 : j = 0
  · subst j
    have htwo := congrArg (fun p : ProbabilityMass ↦ p 2) hj
    change sharpOriginalLaw m α hm hα 2 = diracMass 0 2 at htwo
    rw [diracMass_of_ne 0 2 (by norm_num)] at htwo
    exact (ne_of_gt (sharpOriginalLaw_tail_pos m α hm hα 0)) htwo
  · have hzero := congrArg (fun p : ProbabilityMass ↦ p 0) hj
    change sharpOriginalLaw m α hm hα 0 = diracMass j 0 at hzero
    rw [diracMass_of_ne j 0 (Ne.symm hj0)] at hzero
    exact (ne_of_gt (sharpOriginalLaw_zero_pos m α hm hα)) hzero

theorem realMomentWeight_eq_rpow (s : ℝ) (k : ℕ) :
    realMomentWeight s k = Real.rpow (k : ℝ) s := by
  by_cases hs : s = 0
  · subst s
    simp
  · exact realMomentWeight_of_ne_zero s k hs

/-- On the tail, undoing the tilt leaves a nonzero constant times a p-series. -/
theorem sharpOriginalLaw_realMoment_tail
    (m : ℕ) (α s : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (k : ℕ) :
    realMomentWeight s (k + 2) * (m : ℝ) ^ (k + 2) *
        sharpOriginalLaw m α hm hα (k + 2) =
      (sharpNormalizingConstant m α * sharpTailConstant m α) *
        (Real.rpow (k + 2 : ℝ) s * Real.rpow (k + 2 : ℝ) (-α)) := by
  have hw : realMomentWeight s (k + 2) = Real.rpow (k + 2 : ℝ) s :=
    by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        realMomentWeight_eq_rpow s (k + 2)
  calc
    realMomentWeight s (k + 2) * (m : ℝ) ^ (k + 2) *
          sharpOriginalLaw m α hm hα (k + 2) =
        realMomentWeight s (k + 2) *
          ((m : ℝ) ^ (k + 2) * sharpOriginalLaw m α hm hα (k + 2)) := by
      ring
    _ = realMomentWeight s (k + 2) *
          (sharpNormalizingConstant m α *
            sharpTiltedLaw m α hm hα (k + 2)) := by
      rw [sharpOriginalLaw_tilted_coeff]
    _ = (sharpNormalizingConstant m α * sharpTailConstant m α) *
          (Real.rpow (k + 2 : ℝ) s * Real.rpow (k + 2 : ℝ) (-α)) := by
      rw [sharpTiltedLaw_apply, sharpTiltedSeq_tail, hw]
      ring

/-- Exact real-order moment threshold for the normalized original law. -/
theorem sharpOriginalLaw_realTiltSummable_iff
    (m : ℕ) (α s : ℝ) (hm : 2 ≤ m) (hα : 2 < α) :
    RealTiltSummable m s (sharpOriginalLaw m α hm hα) ↔ s < α - 1 := by
  let f : ℕ → ℝ := fun k : ℕ ↦
    realMomentWeight s k * (m : ℝ) ^ k * sharpOriginalLaw m α hm hα k
  let g : ℕ → ℝ := fun k : ℕ ↦
    Real.rpow (k + 2 : ℝ) s * Real.rpow (k + 2 : ℝ) (-α)
  let c : ℝ := sharpNormalizingConstant m α * sharpTailConstant m α
  have hc : c ≠ 0 := ne_of_gt (mul_pos
    (sharpNormalizingConstant_pos m α hm hα)
    (sharpTailConstant_pos m α hm hα))
  have hfg : (fun k : ℕ ↦ f (k + 2)) = fun k : ℕ ↦ c * g k := by
    funext k
    exact sharpOriginalLaw_realMoment_tail m α s hm hα k
  change Summable f ↔ s < α - 1
  rw [← (summable_nat_add_iff (f := f) 2), hfg, summable_mul_left_iff hc]
  exact shiftedPowerTailMoment_summable_iff s α

/-- Real-order moments at natural exponents agree with integer-order moments. -/
theorem realTiltSummable_nat_iff_tiltSummable
    (m n : ℕ) (p : ProbabilityMass) :
    RealTiltSummable m (n : ℝ) p ↔ TiltSummable m n p := by
  unfold RealTiltSummable TiltSummable
  apply summable_congr
  intro k
  rw [realMomentWeight_eq_rpow]
  exact congrArg (fun x : ℝ ↦ x * (m : ℝ) ^ k * p k)
    (Real.rpow_natCast (k : ℝ) n)

theorem sharpOriginalLaw_realTiltSummable
    (m : ℕ) (α s : ℝ) (hm : 2 ≤ m) (hα : 2 < α) (hs : s < α - 1) :
    RealTiltSummable m s (sharpOriginalLaw m α hm hα) :=
  (sharpOriginalLaw_realTiltSummable_iff m α s hm hα).mpr hs

/-- The third integer tilted moment diverges whenever the power exponent is below four. -/
theorem sharpOriginalLaw_not_tiltSummable_three
    (m : ℕ) (α : ℝ) (hm : 2 ≤ m) (hα₂ : 2 < α) (hα₄ : α < 4) :
    ¬TiltSummable m 3 (sharpOriginalLaw m α hm hα₂) := by
  intro hthird
  have hthirdReal : RealTiltSummable m (3 : ℝ) (sharpOriginalLaw m α hm hα₂) :=
    (realTiltSummable_nat_iff_tiltSummable m 3
      (sharpOriginalLaw m α hm hα₂)).mpr hthird
  have hthreshold :=
    (sharpOriginalLaw_realTiltSummable_iff m α 3 hm hα₂).mp hthirdReal
  linarith

/-- The fully explicit sharpness law with exponent `7/2 + r/6`. -/
def sharpnessPowerLaw
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    ProbabilityMass :=
  sharpOriginalLaw m (sharpPowerExponent r) hm
    (by
      have hmax := max_three_add_one_lt_sharpPowerExponent r hr₀ hr₃
      exact lt_trans (by norm_num : (2 : ℝ) < 3)
        (lt_of_le_of_lt (le_max_left 3 (r + 1)) hmax))

theorem sharpnessPowerLaw_critical
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    Critical m (sharpnessPowerLaw m r hm hr₀ hr₃) := by
  unfold sharpnessPowerLaw
  exact sharpOriginalLaw_critical m (sharpPowerExponent r) hm
    (by linarith [three_lt_sharpPowerExponent r hr₀])

theorem sharpnessPowerLaw_not_isDirac
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    ¬IsDirac (sharpnessPowerLaw m r hm hr₀ hr₃) := by
  unfold sharpnessPowerLaw
  exact sharpOriginalLaw_not_isDirac m (sharpPowerExponent r) hm
    (by linarith [three_lt_sharpPowerExponent r hr₀])

theorem sharpnessPowerLaw_realTiltSummable
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    RealTiltSummable m r (sharpnessPowerLaw m r hm hr₀ hr₃) := by
  unfold sharpnessPowerLaw
  apply sharpOriginalLaw_realTiltSummable
  linarith [add_one_lt_sharpPowerExponent r hr₃]

theorem sharpnessPowerLaw_not_tiltSummable_three
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    ¬TiltSummable m 3 (sharpnessPowerLaw m r hm hr₀ hr₃) := by
  unfold sharpnessPowerLaw
  exact sharpOriginalLaw_not_tiltSummable_three m (sharpPowerExponent r) hm
    (by linarith [three_lt_sharpPowerExponent r hr₀])
    (sharpPowerExponent_lt_four r hr₃)

/-- Exact tail identity for the fully explicit law, valid at every `k + 2`. -/
theorem sharpnessPowerLaw_tail
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) (k : ℕ) :
    sharpnessPowerLaw m r hm hr₀ hr₃ (k + 2) =
      sharpNormalizingConstant m (sharpPowerExponent r) *
        (m : ℝ)⁻¹ ^ (k + 2) * sharpTailConstant m (sharpPowerExponent r) *
          Real.rpow (k + 2 : ℝ) (-sharpPowerExponent r) := by
  unfold sharpnessPowerLaw
  exact sharpOriginalLaw_tail m (sharpPowerExponent r) hm
    (by linarith [three_lt_sharpPowerExponent r hr₀]) k

/-- The explicit heavy-tail law packaged as admissible critical initial data. -/
def sharpnessCriticalInitialData
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    CriticalInitialData m where
  arity := hm
  law := sharpnessPowerLaw m r hm hr₀ hr₃
  critical := sharpnessPowerLaw_critical m r hm hr₀ hr₃
  notBinaryFixedPoint := by
    rintro ⟨_, hfixed⟩
    exact sharpnessPowerLaw_not_isDirac m r hm hr₀ hr₃ ⟨1, hfixed⟩

end

end DerridaRetaux
