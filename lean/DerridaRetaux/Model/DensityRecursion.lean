import DerridaRetaux.Model.TransportCoefficient
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Exact recursion for the shifted positive tilted density

The derivation is coefficientwise.  Its only power-series use is the already finite
binomial theorem for a convolution power; no Laurent series or coefficient division is
introduced.
-/

/-- Iterated zero-extending right shift, the source's `T^r`. -/
def shiftRightPow : ℕ → Seq → Seq
  | 0, a => a
  | r + 1, a => shiftRightPow r (shiftRight a)

/-- The coefficient `d_r` in source equation `eq:rhor`. -/
def densityCoeff (m r : ℕ) (p : ProbabilityMass) : ℝ :=
  (Nat.choose m r : ℝ) * zeroTilt m p ^ (m - r) /
    (tiltDenom m p * ((m : ℝ) - 1) ^ (r - 1))

private theorem mul_inv_pow_succ (a : ℝ) (ha : a ≠ 0) (n : ℕ) :
    a * a⁻¹ ^ (n + 1) = a⁻¹ ^ n := by
  rw [pow_succ]
  calc
    a * (a⁻¹ ^ n * a⁻¹) = (a * a⁻¹) * a⁻¹ ^ n := by ring
    _ = a⁻¹ ^ n := by rw [mul_inv_cancel₀ ha, one_mul]

@[simp]
theorem shiftRightPow_zero (a : Seq) : shiftRightPow 0 a = a :=
  rfl

@[simp]
theorem shiftRightPow_succ (r : ℕ) (a : Seq) :
    shiftRightPow (r + 1) a = shiftRightPow r (shiftRight a) :=
  rfl

@[simp]
theorem shiftRightPow_two_apply (a : Seq) (j : ℕ) :
    shiftRightPow 2 a (j + 2) = a j := by
  rfl

/-- One additional right shift can be moved across an iterated right shift. -/
theorem shiftRightPow_shiftRight (r : ℕ) (a : Seq) :
    shiftRightPow r (shiftRight a) = shiftRight (shiftRightPow r a) := by
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
      simpa only [shiftRightPow_succ] using ih (shiftRight a)

/-- Iterated right shifts compose additively. -/
theorem shiftRightPow_add (r s : ℕ) (a : Seq) :
    shiftRightPow (r + s) a = shiftRightPow r (shiftRightPow s a) := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
      simp only [Nat.succ_add, shiftRightPow_succ]
      rw [ih]
      rw [shiftRightPow_shiftRight]

/-- A right shift in the left input becomes a right shift of the convolution. -/
theorem conv_shiftRight_left (a b : Seq) :
    conv (shiftRight a) b = shiftRight (conv a b) := by
  funext n
  cases n with
  | zero => simp
  | succ n => exact conv_shiftRight_left_succ a b n

/-- A right shift in the right input becomes a right shift of the convolution. -/
theorem conv_shiftRight_right (a b : Seq) :
    conv a (shiftRight b) = shiftRight (conv a b) := by
  funext n
  cases n with
  | zero => simp
  | succ n => exact conv_shiftRight_right_succ a b n

/-- An iterated right shift commutes with convolution in the left input. -/
theorem conv_shiftRightPow_left (r : ℕ) (a b : Seq) :
    conv (shiftRightPow r a) b = shiftRightPow r (conv a b) := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
      simp only [shiftRightPow_succ]
      rw [ih, conv_shiftRight_left]

/-- Shifting every factor shifts an `r`-fold convolution by exactly `r`. -/
theorem convPow_shiftRight (r : ℕ) (a : Seq) :
    convPow r (shiftRight a) = shiftRightPow r (convPow r a) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [convPow_succ, convPow_succ, ih, conv_shiftRightPow_left,
        conv_shiftRight_right]
      rfl

/-- After cancelling two of those shifts, the remaining power is `T^(r-2)`. -/
theorem convPow_shiftRight_apply_add_two
    (r : ℕ) (a : Seq) (j : ℕ) (hr : 2 ≤ r) :
    convPow r (shiftRight a) (j + 2) =
      shiftRightPow (r - 2) (convPow r a) j := by
  rw [convPow_shiftRight]
  nth_rw 1 [show r = 2 + (r - 2) by omega]
  rw [shiftRightPow_add]
  exact shiftRightPow_two_apply _ _

/-- Scaling both inputs factors out of a finite Cauchy coefficient. -/
theorem conv_const_mul (c d : ℝ) (a b : Seq) :
    conv (fun k : ℕ ↦ c * a k) (fun k : ℕ ↦ d * b k) =
      fun n : ℕ ↦ (c * d) * conv a b n := by
  funext n
  rw [conv_apply, conv_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A scalar raised to the convolution power factors coefficientwise. -/
theorem convPow_const_mul (r : ℕ) (c : ℝ) (a : Seq) :
    convPow r (fun k : ℕ ↦ c * a k) =
      fun n : ℕ ↦ c ^ r * convPow r a n := by
  induction r with
  | zero =>
      funext n
      simp
  | succ r ih =>
      rw [convPow_succ, convPow_succ, ih, conv_const_mul]
      funext n
      rw [pow_succ]

/-- The sequence-to-power-series embedding sends convolution powers to ordinary powers. -/
theorem powerSeries_mk_convPow (r : ℕ) (a : Seq) :
    PowerSeries.mk (convPow r a) = (PowerSeries.mk a) ^ r := by
  induction r with
  | zero =>
      apply PowerSeries.ext
      intro n
      simp [convPow, diracSeq]
  | succ r ih =>
      rw [convPow_succ, powerSeries_mk_conv, ih, pow_succ]

/-- Adding a scalar Dirac atom becomes addition of a constant power series. -/
theorem powerSeries_mk_zeroAtom_add (x : ℝ) (b : Seq) :
    PowerSeries.mk (fun k : ℕ ↦ x * diracSeq 0 k + b k) =
      PowerSeries.mk b + PowerSeries.C ℝ x := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [diracSeq]
      ring
  | succ n => simp [diracSeq]

/-- Finite binomial expansion of a convolution power around its zero atom. -/
theorem convPow_zeroAtom_add_apply (m : ℕ) (x : ℝ) (b : Seq) (n : ℕ) :
    convPow m (fun k : ℕ ↦ x * diracSeq 0 k + b k) n =
      ∑ r ∈ Finset.range (m + 1),
        (Nat.choose m r : ℝ) * x ^ (m - r) * convPow r b n := by
  have hseries :
      PowerSeries.mk (convPow m (fun k : ℕ ↦ x * diracSeq 0 k + b k)) =
        ∑ r ∈ Finset.range (m + 1),
          PowerSeries.mk
            (fun n : ℕ ↦
              (Nat.choose m r : ℝ) * x ^ (m - r) * convPow r b n) := by
    calc
      PowerSeries.mk (convPow m (fun k : ℕ ↦ x * diracSeq 0 k + b k)) =
          (PowerSeries.mk (fun k : ℕ ↦ x * diracSeq 0 k + b k)) ^ m :=
        powerSeries_mk_convPow m _
      _ = (PowerSeries.mk b + PowerSeries.C ℝ x) ^ m := by
        rw [powerSeries_mk_zeroAtom_add]
      _ = ∑ r ∈ Finset.range (m + 1),
          (PowerSeries.mk b) ^ r * (PowerSeries.C ℝ x) ^ (m - r) *
            (Nat.choose m r : PowerSeries ℝ) := by
        rw [add_pow]
      _ = ∑ r ∈ Finset.range (m + 1),
          PowerSeries.mk
            (fun n : ℕ ↦
              (Nat.choose m r : ℝ) * x ^ (m - r) * convPow r b n) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [← powerSeries_mk_convPow]
        apply PowerSeries.ext
        intro j
        rw [mul_comm
          (PowerSeries.mk (convPow r b) * (PowerSeries.C ℝ x) ^ (m - r))]
        change PowerSeries.coeff ℝ j
          (PowerSeries.C ℝ (Nat.choose m r : ℝ) *
            (PowerSeries.mk (convPow r b) * (PowerSeries.C ℝ x) ^ (m - r))) = _
        rw [← PowerSeries.smul_eq_C_mul]
        rw [← map_pow, PowerSeries.coeff_smul, PowerSeries.coeff_mul_C]
        simp
        ring
  have hcoeff := congrArg (fun f : PowerSeries ℝ ↦ PowerSeries.coeff ℝ n f) hseries
  simpa using hcoeff

/-- A normalized tilt is its zero atom plus the right-shifted density divided by `m-1`. -/
theorem normalizedTilt_eq_zeroAtom_add_density
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    normalizedTilt m p = fun k : ℕ ↦
      zeroTilt m p * diracSeq 0 k +
        ((m : ℝ) - 1)⁻¹ * shiftRight (positiveTiltedDensity m p) k := by
  have hfactor := critical_tiltFactor_pos m p (by omega) hcrit
  funext k
  cases k with
  | zero => simp [zeroTilt, diracSeq]
  | succ k =>
      simp only [diracSeq_apply, Nat.succ_ne_zero, if_false, mul_zero, zero_add,
        shiftRight_succ, positiveTiltedDensity_apply]
      field_simp [hfactor.ne']

/-- Binomial expansion of the normalized-tilt convolution power in density variables. -/
theorem convPow_normalizedTilt_density_apply
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (n : ℕ) :
    convPow m (normalizedTilt m p) n =
      ∑ r ∈ Finset.range (m + 1),
        (Nat.choose m r : ℝ) * zeroTilt m p ^ (m - r) *
          (((m : ℝ) - 1)⁻¹) ^ r *
            convPow r (shiftRight (positiveTiltedDensity m p)) n := by
  rw [normalizedTilt_eq_zeroAtom_add_density m p hm hcrit]
  rw [convPow_zeroAtom_add_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [congrFun (convPow_const_mul r (((m : ℝ) - 1)⁻¹)
    (shiftRight (positiveTiltedDensity m p))) n]
  ring

/-- Split a finite range into its first two indices and the remaining offset range. -/
theorem sum_range_add_two (f : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ Finset.range (n + 2), f r =
      f 0 + f 1 + ∑ t ∈ Finset.range n, f (t + 2) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.add_assoc]
  norm_num
  ring

/-- Positive-coefficient expansion with the zero term removed and the linear term exposed. -/
theorem convPow_normalizedTilt_density_apply_add_two
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (j : ℕ) :
    convPow m (normalizedTilt m p) (j + 2) =
      (m : ℝ) * zeroTilt m p ^ (m - 1) * ((m : ℝ) - 1)⁻¹ *
          positiveTiltedDensity m p (j + 1) +
        ∑ t ∈ Finset.range (m - 1),
          (Nat.choose m (t + 2) : ℝ) * zeroTilt m p ^ (m - (t + 2)) *
            (((m : ℝ) - 1)⁻¹) ^ (t + 2) *
              shiftRightPow t
                (convPow (t + 2) (positiveTiltedDensity m p)) j := by
  rw [convPow_normalizedTilt_density_apply m p hm hcrit]
  rw [show m + 1 = (m - 1) + 2 by omega, sum_range_add_two]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul,
    pow_zero, mul_one]
  have hzero :
      convPow 0 (shiftRight (positiveTiltedDensity m p)) (j + 2) = 0 := by
    simp [convPow, diracSeq]
  rw [hzero, mul_zero, zero_add]
  rw [convPow_one, shiftRight_succ]
  simp only [pow_one]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro t _
  rw [convPow_shiftRight_apply_add_two (t + 2)
    (positiveTiltedDensity m p) j (by omega)]
  simp

/-- Offset-indexed coefficient form of the exact density recursion. -/
theorem positiveTiltedDensity_drStepProb_apply_offset
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (j : ℕ) :
    positiveTiltedDensity m (drStepProb m p) j =
      transportCoeff m p * shiftLeft (positiveTiltedDensity m p) j +
        ∑ t ∈ Finset.range (m - 1),
          densityCoeff m (t + 2) p *
            shiftRightPow t
              (convPow (t + 2) (positiveTiltedDensity m p)) j := by
  have hfactor := critical_tiltFactor_pos m p (by omega) hcrit
  have hD := tiltDenom_pos m p (by omega) hcrit
  rw [positiveTiltedDensity_apply,
    normalizedTilt_drStepProb_succ m p (by omega) hcrit j,
    convPow_normalizedTilt_density_apply_add_two m p hm hcrit j]
  rw [add_div, mul_add, Finset.sum_div, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · rw [shiftLeft_apply, transportCoeff]
    calc
      ((m : ℝ) - 1) *
          ((m : ℝ) * zeroTilt m p ^ (m - 1) * ((m : ℝ) - 1)⁻¹ *
              positiveTiltedDensity m p (j + 1) / tiltDenom m p) =
          (((m : ℝ) - 1) * ((m : ℝ) - 1)⁻¹) *
            (((m : ℝ) * zeroTilt m p ^ (m - 1) / tiltDenom m p) *
              positiveTiltedDensity m p (j + 1)) := by ring
      _ = (m : ℝ) * zeroTilt m p ^ (m - 1) / tiltDenom m p *
          positiveTiltedDensity m p (j + 1) := by
            rw [mul_inv_cancel₀ hfactor.ne', one_mul]
  · apply Finset.sum_congr rfl
    intro t _
    simp only [densityCoeff]
    have hindex : t + 2 - 1 = t + 1 := by omega
    rw [hindex]
    have hcancel :
        ((m : ℝ) - 1) * ((m : ℝ) - 1)⁻¹ ^ (t + 2) =
          ((m : ℝ) - 1)⁻¹ ^ (t + 1) := by
      exact mul_inv_pow_succ ((m : ℝ) - 1) hfactor.ne' (t + 1)
    calc
      ((m : ℝ) - 1) *
          ((Nat.choose m (t + 2) : ℝ) * zeroTilt m p ^ (m - (t + 2)) *
              ((m : ℝ) - 1)⁻¹ ^ (t + 2) *
                shiftRightPow t
                  (convPow (t + 2) (positiveTiltedDensity m p)) j /
            tiltDenom m p) =
          ((Nat.choose m (t + 2) : ℝ) * zeroTilt m p ^ (m - (t + 2)) /
              tiltDenom m p) *
            shiftRightPow t
                (convPow (t + 2) (positiveTiltedDensity m p)) j *
              (((m : ℝ) - 1) * ((m : ℝ) - 1)⁻¹ ^ (t + 2)) := by ring
      _ = ((Nat.choose m (t + 2) : ℝ) * zeroTilt m p ^ (m - (t + 2)) /
              tiltDenom m p) *
            shiftRightPow t
                (convPow (t + 2) (positiveTiltedDensity m p)) j *
              ((m : ℝ) - 1)⁻¹ ^ (t + 1) := by rw [hcancel]
      _ = (Nat.choose m (t + 2) : ℝ) * zeroTilt m p ^ (m - (t + 2)) /
              (tiltDenom m p * ((m : ℝ) - 1) ^ (t + 1)) *
            shiftRightPow t
              (convPow (t + 2) (positiveTiltedDensity m p)) j := by
            simp only [div_eq_mul_inv, mul_inv, inv_pow]
            ring

/-- Sequence-valued offset form of the exact density recursion. -/
theorem positiveTiltedDensity_drStepProb_offset
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    positiveTiltedDensity m (drStepProb m p) = fun j : ℕ ↦
      transportCoeff m p * shiftLeft (positiveTiltedDensity m p) j +
        ∑ t ∈ Finset.range (m - 1),
          densityCoeff m (t + 2) p *
            shiftRightPow t
              (convPow (t + 2) (positiveTiltedDensity m p)) j := by
  funext j
  exact positiveTiltedDensity_drStepProb_apply_offset m p hm hcrit j

/-- Source-indexed coefficient form of equation `eq:rhor`, with `2 ≤ r ≤ m`. -/
theorem positiveTiltedDensity_drStepProb_apply
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) (j : ℕ) :
    positiveTiltedDensity m (drStepProb m p) j =
      transportCoeff m p * shiftLeft (positiveTiltedDensity m p) j +
        ∑ r ∈ Finset.Ico 2 (m + 1),
          densityCoeff m r p *
            shiftRightPow (r - 2) (convPow r (positiveTiltedDensity m p)) j := by
  rw [positiveTiltedDensity_drStepProb_apply_offset m p hm hcrit j]
  apply congrArg₂ (· + ·) rfl
  rw [Finset.sum_Ico_eq_sum_range]
  have hlength : m + 1 - 2 = m - 1 := by omega
  rw [hlength]
  apply Finset.sum_congr rfl
  intro t _
  simp [Nat.add_comm]

/-- Sequence-valued source-indexed form of equation `eq:rhor`. -/
theorem positiveTiltedDensity_drStepProb
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    positiveTiltedDensity m (drStepProb m p) = fun j : ℕ ↦
      transportCoeff m p * shiftLeft (positiveTiltedDensity m p) j +
        ∑ r ∈ Finset.Ico 2 (m + 1),
          densityCoeff m r p *
            shiftRightPow (r - 2) (convPow r (positiveTiltedDensity m p)) j := by
  funext j
  exact positiveTiltedDensity_drStepProb_apply m p hm hcrit j

/-- The paper-facing PMF-backed step satisfies the same exact density recursion. -/
theorem positiveTiltedDensity_drStep
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    positiveTiltedDensity m (drStep m p) = fun j : ℕ ↦
      transportCoeff m p * shiftLeft (positiveTiltedDensity m p) j +
        ∑ r ∈ Finset.Ico 2 (m + 1),
          densityCoeff m r p *
            shiftRightPow (r - 2) (convPow r (positiveTiltedDensity m p)) j := by
  rw [drStep_eq_drStepProb]
  exact positiveTiltedDensity_drStepProb m p hm hcrit

/-- Equation `eq:rhor` along every generation of a critical orbit. -/
theorem positiveTiltedDensity_orbit_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    positiveTiltedDensity m (orbit m p₀ (n + 1)) = fun j : ℕ ↦
      transportCoeff m (orbit m p₀ n) *
          shiftLeft (positiveTiltedDensity m (orbit m p₀ n)) j +
        ∑ r ∈ Finset.Ico 2 (m + 1),
          densityCoeff m r (orbit m p₀ n) *
            shiftRightPow (r - 2)
              (convPow r (positiveTiltedDensity m (orbit m p₀ n))) j := by
  rw [orbit_succ]
  exact positiveTiltedDensity_drStep m (orbit m p₀ n) hm
    (orbit_critical m p₀ (by omega) hcrit n)

/-- At arity two the nonlinear range contains exactly the quadratic term; it is not empty. -/
theorem positiveTiltedDensity_drStepProb_two
    (p : ProbabilityMass) (hcrit : Critical 2 p) :
    positiveTiltedDensity 2 (drStepProb 2 p) = fun j : ℕ ↦
      transportCoeff 2 p * shiftLeft (positiveTiltedDensity 2 p) j +
        densityCoeff 2 2 p * convPow 2 (positiveTiltedDensity 2 p) j := by
  rw [positiveTiltedDensity_drStepProb_offset 2 p (by omega) hcrit]
  simp

end

end DerridaRetaux
