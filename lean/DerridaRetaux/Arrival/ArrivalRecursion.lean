import DerridaRetaux.Arrival.IntegerShift
import DerridaRetaux.Model.TransportCoefficient
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Arrival-coordinate recursion

This file gives coefficient-level versions of the source formulas around
`lem:arrival`.  Integer shifts are interpreted through `shiftByInt`, so expressions
such as `(r - 2) (1 - s)` never use truncated natural subtraction.
-/

noncomputable section

/-- Delete the constant coefficient of a sequence.  These are the coefficients of
`Q(z) = H(z) - H(0)`. -/
def removeZeroCoeff (a : Seq) : Seq
  | 0 => 0
  | k + 1 => a (k + 1)

@[simp]
theorem removeZeroCoeff_zero (a : Seq) : removeZeroCoeff a 0 = 0 :=
  rfl

@[simp]
theorem removeZeroCoeff_succ (a : Seq) (k : ℕ) :
    removeZeroCoeff a (k + 1) = a (k + 1) :=
  rfl

/-- A scalar sequence supported at degree zero. -/
def constantCoeff (x : ℝ) : Seq :=
  fun k ↦ x * diracSeq 0 k

@[simp]
theorem constantCoeff_zero (x : ℝ) : constantCoeff x 0 = x := by
  simp [constantCoeff]

@[simp]
theorem constantCoeff_succ (x : ℝ) (k : ℕ) : constantCoeff x (k + 1) = 0 := by
  simp [constantCoeff, diracSeq]

/-- Every sequence is its constant coefficient plus its positive part. -/
theorem constantCoeff_add_removeZeroCoeff (a : Seq) :
    (fun k : ℕ ↦ constantCoeff (a 0) k + removeZeroCoeff a k) = a := by
  funext k
  cases k <;> simp

/-- Convolution powers become ordinary powers after embedding into formal series. -/
theorem powerSeries_mk_convPow (r : ℕ) (a : Seq) :
    PowerSeries.mk (convPow r a) = PowerSeries.mk a ^ r := by
  induction r with
  | zero =>
      apply PowerSeries.ext
      intro k
      cases k <;> simp [convPow, diracSeq]
  | succ r ih =>
      rw [convPow_succ, powerSeries_mk_conv, ih, pow_succ]

/-- The scalar sequence embeds as the constant formal power series. -/
theorem powerSeries_mk_constantCoeff (x : ℝ) :
    PowerSeries.mk (constantCoeff x) = PowerSeries.C ℝ x := by
  apply PowerSeries.ext
  intro k
  cases k <;> simp [constantCoeff, diracSeq, PowerSeries.coeff_C]

theorem powerSeries_mk_split_zero (a : Seq) :
    PowerSeries.mk a =
      PowerSeries.mk (removeZeroCoeff a) + PowerSeries.C ℝ (a 0) := by
  apply PowerSeries.ext
  intro k
  cases k <;> simp [PowerSeries.coeff_C]

/-- Coefficientwise binomial expansion separating the constant coefficient. -/
theorem convPow_split_zero_coeff (r : ℕ) (a : Seq) (n : ℕ) :
    convPow r a n =
      ∑ j ∈ Finset.range (r + 1),
        (r.choose j : ℝ) * a 0 ^ (r - j) * convPow j (removeZeroCoeff a) n := by
  have hseries :
      PowerSeries.mk (convPow r a) =
        ∑ j ∈ Finset.range (r + 1),
          PowerSeries.mk (removeZeroCoeff a) ^ j *
            (PowerSeries.C ℝ (a 0)) ^ (r - j) * (r.choose j : PowerSeries ℝ) := by
    rw [powerSeries_mk_convPow, powerSeries_mk_split_zero, add_pow]
  have hcoeff := congrArg (fun f ↦ PowerSeries.coeff ℝ n f) hseries
  simp_rw [← powerSeries_mk_convPow] at hcoeff
  simp_rw [← map_pow (PowerSeries.C ℝ)] at hcoeff
  simp_rw [← map_natCast (PowerSeries.C ℝ)] at hcoeff
  simp only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_mul_C] at hcoeff
  rw [hcoeff]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The part of an `m`-fold convolution coefficient using at least two positive
inputs.  The index set is literally `Icc 2 m`, as in `eq:arrivalA`. -/
def positiveConvolutionSource (m : ℕ) (a : Seq) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 m,
    (m.choose r : ℝ) * a 0 ^ (m - r) * convPow r (removeZeroCoeff a) n

@[simp]
theorem positiveConvolutionSource_arity_zero (a : Seq) (n : ℕ) :
    positiveConvolutionSource 0 a n = 0 := by
  simp [positiveConvolutionSource]

@[simp]
theorem positiveConvolutionSource_arity_one (a : Seq) (n : ℕ) :
    positiveConvolutionSource 1 a n = 0 := by
  simp [positiveConvolutionSource]

theorem positiveConvolutionSource_nonneg
    (m : ℕ) (a : Seq) (ha : ∀ k : ℕ, 0 ≤ a k) (n : ℕ) :
    0 ≤ positiveConvolutionSource m a n := by
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (ha 0) (m - r)))
    (convPow_nonneg r (removeZeroCoeff a)
      (fun k ↦ by cases k <;> simp [ha]) n)

/-- The positive-degree binomial expansion: the `r=0` contribution vanishes and
the `r=1` contribution is the linear transport term. -/
theorem convPow_positive_eq_linear_add_source
    (m : ℕ) (a : Seq) (hm : 2 ≤ m) (k : ℕ) :
    convPow m a (k + 1) =
      (m : ℝ) * a 0 ^ (m - 1) * a (k + 1) +
        positiveConvolutionSource m a (k + 1) := by
  rw [convPow_split_zero_coeff]
  have hrange :
      Finset.range (m + 1) = {0, 1} ∪ Finset.Icc 2 m := by
    ext r
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_union]
  · simp [positiveConvolutionSource, removeZeroCoeff, convPow, diracSeq,
      Nat.choose_one_right, hm]
  · simp

/-- The normalized tilted coefficients at generation `s`. -/
def orbitTilt (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  normalizedTilt m (orbit m p₀ s)

/-- The positive coefficients of `Q_s(z) = H_s(z) - x_s`. -/
def orbitPositiveTilt (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  removeZeroCoeff (orbitTilt m p₀ s)

/-- Source notation `x_s = q_{s,0}`. -/
def arrivalZero (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : ℝ :=
  zeroTilt m (orbit m p₀ s)

/-- Source notation `D_s`. -/
def arrivalDenom (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : ℝ :=
  tiltDenom m (orbit m p₀ s)

/-- Source notation `C_s`. -/
def arrivalProduct (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : ℝ :=
  transportProduct m p₀ s

@[simp]
theorem arrivalProduct_zero (m : ℕ) (p₀ : ProbabilityMass) :
    arrivalProduct m p₀ 0 = 1 := by
  simp [arrivalProduct]

/-- The total coefficient array of `F_s`, extended by zero below degree `s`. -/
def arrivalCoeff (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) : ℝ :=
  if s ≤ N then
    orbitTilt m p₀ s (N - s + 1) / arrivalProduct m p₀ s
  else
    0

/-- Source notation `b_s = phi_{s,s}`. -/
def arrivalBoundary (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : ℝ :=
  arrivalCoeff m p₀ s s

/-- Source notation `kappa_s = C_s / x_s`. -/
def arrivalKappa (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : ℝ :=
  arrivalProduct m p₀ s / arrivalZero m p₀ s

/-- Source coefficient `alpha_(r,s) = m⁻¹ choose(m,r) kappa_s^(r-1)`. -/
def arrivalAlpha
    (m : ℕ) (p₀ : ProbabilityMass) (s r : ℕ) : ℝ :=
  (1 / (m : ℝ)) * (m.choose r : ℝ) * arrivalKappa m p₀ s ^ (r - 1)

/-- The literal finite coefficient formula for `A_s` in `eq:arrivalA`. -/
def arrivalFormulaSource
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 m,
    arrivalAlpha m p₀ s r *
      shiftByInt (((r : ℤ) - 2) * (1 - (s : ℤ)))
        (convPow r (arrivalCoeff m p₀ s)) N

@[simp]
theorem arrivalFormulaSource_arity_zero
    (p₀ : ProbabilityMass) (s N : ℕ) :
    arrivalFormulaSource 0 p₀ s N = 0 := by
  simp [arrivalFormulaSource]

@[simp]
theorem arrivalFormulaSource_arity_one
    (p₀ : ProbabilityMass) (s N : ℕ) :
    arrivalFormulaSource 1 p₀ s N = 0 := by
  simp [arrivalFormulaSource]

theorem arrivalCoeff_eq_of_le
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) (hN : s ≤ N) :
    arrivalCoeff m p₀ s N =
      orbitTilt m p₀ s (N - s + 1) / arrivalProduct m p₀ s := by
  simp [arrivalCoeff, hN]

theorem arrivalCoeff_eq_zero_of_lt
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) (hN : N < s) :
    arrivalCoeff m p₀ s N = 0 := by
  simp [arrivalCoeff, Nat.not_le.mpr hN]

@[simp]
theorem arrivalCoeff_zero_generation
    (m : ℕ) (p₀ : ProbabilityMass) (N : ℕ) :
    arrivalCoeff m p₀ 0 N = orbitTilt m p₀ 0 (N + 1) := by
  simp [arrivalCoeff, arrivalProduct]

@[simp]
theorem arrivalBoundary_eq
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    arrivalBoundary m p₀ s =
    orbitTilt m p₀ s 1 / arrivalProduct m p₀ s := by
  simp [arrivalBoundary, arrivalCoeff]

theorem orbitTilt_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (s k : ℕ) :
    0 ≤ orbitTilt m p₀ s k := by
  exact normalizedTilt_nonneg m (orbit m p₀ s) hm
    (orbit_critical m p₀ hm hcrit s) k

theorem orbitPositiveTilt_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (s k : ℕ) :
    0 ≤ orbitPositiveTilt m p₀ s k := by
  cases k with
  | zero => simp [orbitPositiveTilt]
  | succ k =>
      simpa [orbitPositiveTilt] using orbitTilt_nonneg m p₀ hm hcrit s (k + 1)

theorem arrivalCoeff_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ) :
    0 ≤ arrivalCoeff m p₀ s N := by
  by_cases hN : s ≤ N
  · rw [arrivalCoeff_eq_of_le m p₀ s N hN]
    exact div_nonneg (orbitTilt_nonneg m p₀ (by omega) hcrit s (N - s + 1))
      (transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint s).le
  · rw [arrivalCoeff_eq_zero_of_lt m p₀ s N (by omega)]

theorem arrivalBoundary_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    0 ≤ arrivalBoundary m p₀ s := by
  exact arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s s

theorem arrivalKappa_pos
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    0 < arrivalKappa m p₀ s := by
  exact div_pos
    (transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint s)
    (orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint s)

theorem arrivalAlpha_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s r : ℕ) :
    0 ≤ arrivalAlpha m p₀ s r := by
  exact mul_nonneg
    (mul_nonneg (by positivity) (Nat.cast_nonneg _))
    (pow_nonneg (arrivalKappa_pos m p₀ hm hcrit hnotBinaryFixedPoint s).le (r - 1))

/-- Coefficient form of `Q_s = C_s z^(1-s) F_s` at positive degrees. -/
theorem orbitPositiveTilt_succ_eq_product_shift_arrival
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s k : ℕ) :
    orbitPositiveTilt m p₀ s (k + 1) =
      arrivalProduct m p₀ s *
        shiftByInt (1 - (s : ℤ)) (arrivalCoeff m p₀ s) (k + 1) := by
  have hC : 0 < arrivalProduct m p₀ s :=
    transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint s
  have hz :
      (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - (1 - (s : ℤ)) := by
    omega
  rw [orbitPositiveTilt, removeZeroCoeff_succ, shiftByInt,
    zeroExtend_eq_of_nonneg _ _ hz]
  have hindex :
      (((k + 1 : ℕ) : ℤ) - (1 - (s : ℤ))).toNat = s + k := by
    omega
  rw [hindex, arrivalCoeff_eq_of_le m p₀ s (s + k) (by omega)]
  have hsub : s + k - s + 1 = k + 1 := by omega
  rw [hsub]
  field_simp [hC.ne']

/-- The constant coefficient in the same factorization is zero on both sides. -/
theorem orbitPositiveTilt_zero_eq_product_shift_arrival
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    orbitPositiveTilt m p₀ s 0 =
      arrivalProduct m p₀ s *
        shiftByInt (1 - (s : ℤ)) (arrivalCoeff m p₀ s) 0 := by
  rw [orbitPositiveTilt, removeZeroCoeff_zero]
  suffices shiftByInt (1 - (s : ℤ)) (arrivalCoeff m p₀ s) 0 = 0 by
    rw [this, mul_zero]
  cases s with
  | zero =>
      exact shiftByInt_eq_zero_of_lt 1 0 (arrivalCoeff m p₀ 0) (by omega)
  | succ s =>
      rw [shiftByInt]
      have hz : (0 : ℤ) ≤ (0 : ℤ) - (1 - ((s + 1 : ℕ) : ℤ)) := by omega
      norm_num only [Int.ofNat_zero]
      rw [zeroExtend_eq_of_nonneg _ _ hz]
      have hindex : ((0 : ℤ) - (1 - ((s + 1 : ℕ) : ℤ))).toNat = s := by
        omega
      rw [hindex]
      exact arrivalCoeff_eq_zero_of_lt m p₀ (s + 1) s (by omega)

/-- Full coefficient-array form of `eq:Qfactor`. -/
theorem orbitPositiveTilt_eq_product_shift_arrival
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    orbitPositiveTilt m p₀ s =
      fun k : ℕ ↦ arrivalProduct m p₀ s *
        shiftByInt (1 - (s : ℤ)) (arrivalCoeff m p₀ s) k := by
  funext k
  cases k with
  | zero => exact orbitPositiveTilt_zero_eq_product_shift_arrival m p₀ s
  | succ k =>
      exact orbitPositiveTilt_succ_eq_product_shift_arrival m p₀ hm hcrit
        hnotBinaryFixedPoint s k

/-- Exact scalar identity `D_s C_(s+1) = m x_s^(m-1) C_s`. -/
theorem arrivalDenom_mul_product_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (s : ℕ) :
    arrivalDenom m p₀ s * arrivalProduct m p₀ (s + 1) =
      (m : ℝ) * arrivalZero m p₀ s ^ (m - 1) * arrivalProduct m p₀ s := by
  have hD0 : tiltDenom m (orbit m p₀ s) ≠ 0 :=
    (tiltDenom_pos m (orbit m p₀ s) hm
      (orbit_critical m p₀ hm hcrit s)).ne'
  rw [arrivalDenom, arrivalProduct, arrivalZero, transportProduct_succ]
  change
    tiltDenom m (orbit m p₀ s) *
        (transportProduct m p₀ s * transportCoeff m (orbit m p₀ s)) =
      (m : ℝ) * zeroTilt m (orbit m p₀ s) ^ (m - 1) *
        transportProduct m p₀ s
  rw [transportCoeff]
  calc
    tiltDenom m (orbit m p₀ s) *
          (transportProduct m p₀ s *
            ((m : ℝ) * zeroTilt m (orbit m p₀ s) ^ (m - 1) /
              tiltDenom m (orbit m p₀ s))) =
        transportProduct m p₀ s *
          (tiltDenom m (orbit m p₀ s) *
            ((m : ℝ) * zeroTilt m (orbit m p₀ s) ^ (m - 1) /
              tiltDenom m (orbit m p₀ s))) := by
      ring
    _ = transportProduct m p₀ s *
        ((m : ℝ) * zeroTilt m (orbit m p₀ s) ^ (m - 1)) := by
      rw [mul_div_cancel₀ _ hD0]
    _ = (m : ℝ) * zeroTilt m (orbit m p₀ s) ^ (m - 1) *
        transportProduct m p₀ s := by
      ring

/-- The positive-coefficient tilted recursion split into its unary transport and
nonlinear (`r ≥ 2`) source. -/
theorem orbitTilt_succ_positive_cross
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (s k : ℕ) :
    arrivalDenom m p₀ s * orbitTilt m p₀ (s + 1) (k + 1) =
      (m : ℝ) * arrivalZero m p₀ s ^ (m - 1) *
          orbitTilt m p₀ s (k + 2) +
        positiveConvolutionSource m (orbitTilt m p₀ s) (k + 2) := by
  have hstep := normalizedTilt_drStepProb_succ_cross m (orbit m p₀ s) (by omega)
    (orbit_critical m p₀ (by omega) hcrit s) k
  rw [← drStep_eq_drStepProb, ← orbit_succ] at hstep
  rw [show k + 2 = (k + 1) + 1 by omega,
    convPow_positive_eq_linear_add_source m
      (normalizedTilt m (orbit m p₀ s)) hm (k + 1)] at hstep
  simpa [arrivalDenom, arrivalZero, orbitTilt] using hstep

/-- Coefficients of the positive nonlinear term `z^(1-s) A_s` in `eq:Arec`. -/
def arrivalIncrement
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) : ℝ :=
  if s < N then
    positiveConvolutionSource m (orbitTilt m p₀ s) (N - s + 1) /
      (arrivalDenom m p₀ s * arrivalProduct m p₀ (s + 1))
  else
    0

theorem arrivalIncrement_eq_of_lt
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) (hN : s < N) :
    arrivalIncrement m p₀ s N =
      positiveConvolutionSource m (orbitTilt m p₀ s) (N - s + 1) /
        (arrivalDenom m p₀ s * arrivalProduct m p₀ (s + 1)) := by
  simp [arrivalIncrement, hN]

theorem arrivalIncrement_eq_zero_of_le
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) (hN : N ≤ s) :
    arrivalIncrement m p₀ s N = 0 := by
  simp [arrivalIncrement, not_lt.mpr hN]

/-- The nonlinear arrival increment has nonnegative coefficients. -/
theorem arrivalIncrement_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ) :
    0 ≤ arrivalIncrement m p₀ s N := by
  by_cases hN : s < N
  · rw [arrivalIncrement_eq_of_lt m p₀ s N hN]
    exact div_nonneg
      (positiveConvolutionSource_nonneg m (orbitTilt m p₀ s)
        (orbitTilt_nonneg m p₀ (by omega) hcrit s) (N - s + 1))
      (mul_nonneg
        (tiltDenom_pos m (orbit m p₀ s) (by omega)
          (orbit_critical m p₀ (by omega) hcrit s)).le
        (transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint (s + 1)).le)
  · rw [arrivalIncrement_eq_zero_of_le m p₀ s N (by omega)]

private theorem div_transport_add_source
    (D C Cnext A q qnext S : ℝ)
    (hD : D ≠ 0) (hC : C ≠ 0) (hCnext : Cnext ≠ 0)
    (hstep : D * qnext = A * q + S) (hproduct : D * Cnext = A * C) :
    qnext / Cnext = q / C + S / (D * Cnext) := by
  have hA : A ≠ 0 := by
    intro hAzero
    rw [hAzero, zero_mul] at hproduct
    exact (mul_ne_zero hD hCnext) hproduct
  calc
    qnext / Cnext = (D * qnext) / (D * Cnext) := by
      field_simp [hD, hCnext]
      ring
    _ = (A * q + S) / (A * C) := by rw [hstep, hproduct]
    _ = q / C + S / (A * C) := by
      field_simp [hA, hC]
      ring
    _ = q / C + S / (D * Cnext) := by rw [hproduct]

/-- Coefficientwise form of `eq:Arec`, including the empty lower range and the
boundary coefficient `N = s`.  The last term is coefficientwise nonnegative. -/
theorem arrivalCoeff_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ) :
    arrivalCoeff m p₀ (s + 1) N =
      arrivalCoeff m p₀ s N -
          (if N = s then arrivalBoundary m p₀ s else 0) +
        arrivalIncrement m p₀ s N := by
  rcases lt_trichotomy N s with hNs | hNs | hNs
  · rw [arrivalCoeff_eq_zero_of_lt m p₀ (s + 1) N (by omega),
      arrivalCoeff_eq_zero_of_lt m p₀ s N hNs,
      arrivalIncrement_eq_zero_of_le m p₀ s N (by omega)]
    simp [ne_of_lt hNs]
  · subst N
    rw [arrivalCoeff_eq_zero_of_lt m p₀ (s + 1) s (by omega),
      arrivalIncrement_eq_zero_of_le m p₀ s s le_rfl]
    simp [arrivalBoundary]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = s + 1 + k := by
      refine ⟨N - (s + 1), ?_⟩
      omega
    have hC : 0 < arrivalProduct m p₀ s :=
      transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint s
    have hCnext : 0 < arrivalProduct m p₀ (s + 1) :=
      transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint (s + 1)
    have hD : 0 < arrivalDenom m p₀ s :=
      tiltDenom_pos m (orbit m p₀ s) (by omega)
        (orbit_critical m p₀ (by omega) hcrit s)
    rw [arrivalCoeff_eq_of_le m p₀ (s + 1) (s + 1 + k) (by omega),
      arrivalCoeff_eq_of_le m p₀ s (s + 1 + k) (by omega),
      arrivalIncrement_eq_of_lt m p₀ s (s + 1 + k) (by omega)]
    have hindexNext : s + 1 + k - (s + 1) + 1 = k + 1 := by omega
    have hindexNow : s + 1 + k - s + 1 = k + 2 := by omega
    rw [hindexNext, hindexNow]
    rw [if_neg (by omega : s + 1 + k ≠ s), sub_zero]
    apply div_transport_add_source
      (arrivalDenom m p₀ s) (arrivalProduct m p₀ s)
      (arrivalProduct m p₀ (s + 1))
      ((m : ℝ) * arrivalZero m p₀ s ^ (m - 1))
      (orbitTilt m p₀ s (k + 2)) (orbitTilt m p₀ (s + 1) (k + 1))
      (positiveConvolutionSource m (orbitTilt m p₀ s) (k + 2))
      hD.ne' hC.ne' hCnext.ne'
      (orbitTilt_succ_positive_cross m p₀ hm hcrit s k)
      (arrivalDenom_mul_product_succ m p₀ (by omega) hcrit s)

/-- Coefficients of the aggregate source `A_s`.  This is the inverse monomial shift
of its occurrence `z^(1-s) A_s` in the renewal equation. -/
def arrivalSource
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  shiftByInt ((s : ℤ) - 1) (arrivalIncrement m p₀ s)

/-- The two opposite integer shifts cancel because the renewal increment vanishes
through degree `s`.  This includes the exceptional pair `s = N = 0`. -/
theorem shift_arrivalSource
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    shiftByInt (1 - (s : ℤ)) (arrivalSource m p₀ s) =
      arrivalIncrement m p₀ s := by
  funext N
  cases s with
  | zero =>
      cases N with
      | zero => simp [arrivalSource, arrivalIncrement, shiftByInt, zeroExtend]
      | succ N =>
          simp [arrivalSource, shiftByInt_one, shiftByInt_neg_one]
  | succ s =>
      have hneg : 1 - ((s + 1 : ℕ) : ℤ) = -(s : ℤ) := by omega
      have hpos : ((s + 1 : ℕ) : ℤ) - 1 = (s : ℤ) := by omega
      rw [arrivalSource, hneg, hpos, shiftByInt_neg_ofNat]
      rw [shiftByInt_of_le s (N + s) (arrivalIncrement m p₀ (s + 1)) (by omega)]
      congr
      omega

theorem shiftByInt_nonneg
    (d : ℤ) (a : Seq) (ha : ∀ k : ℕ, 0 ≤ a k) (N : ℕ) :
    0 ≤ shiftByInt d a N := by
  rw [shiftByInt]
  by_cases hindex : 0 ≤ (N : ℤ) - d
  · rw [zeroExtend_eq_of_nonneg _ _ hindex]
    exact ha _
  · rw [zeroExtend_eq_zero_of_neg]
    exact lt_of_not_ge hindex

/-- A coefficient array vanishes strictly below a natural lower support bound. -/
def CoeffSupportedFrom (d : ℕ) (a : Seq) : Prop :=
  ∀ n : ℕ, n < d → a n = 0

theorem conv_supportedFrom
    (a b : Seq) (d e : ℕ) (ha : CoeffSupportedFrom d a)
    (hb : CoeffSupportedFrom e b) :
    CoeffSupportedFrom (d + e) (conv a b) := by
  intro n hn
  rw [conv_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k ≤ n := by
    have : k < n + 1 := Finset.mem_range.mp hk
    omega
  by_cases hkd : k < d
  · rw [ha k hkd, zero_mul]
  · have hrest : n - k < e := by omega
    rw [hb (n - k) hrest, mul_zero]

theorem convPow_supportedFrom
    (r d : ℕ) (a : Seq) (ha : CoeffSupportedFrom d a) :
    CoeffSupportedFrom (r * d) (convPow r a) := by
  induction r with
  | zero =>
      intro n hn
      omega
  | succ r ih =>
      rw [convPow_succ]
      have hsupport := conv_supportedFrom (convPow r a) a (r * d) d ih ha
      simpa [Nat.succ_mul] using hsupport

theorem powerSeries_mk_shiftByInt_ofNat (d : ℕ) (a : Seq) :
    PowerSeries.mk (shiftByInt (d : ℤ) a) =
      PowerSeries.X ^ d * PowerSeries.mk a := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
  by_cases hdn : d ≤ n
  · rw [if_pos hdn, PowerSeries.coeff_mk,
      shiftByInt_of_le d n a hdn]
  · rw [if_neg hdn,
      shiftByInt_eq_zero_of_lt d n a (lt_of_not_ge hdn)]

theorem powerSeries_X_pow_mul_shiftByInt_neg
    (d : ℕ) (a : Seq) (ha : CoeffSupportedFrom d a) :
    PowerSeries.X ^ d * PowerSeries.mk (shiftByInt (-(d : ℤ)) a) =
      PowerSeries.mk a := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hdn : d ≤ n
  · rw [if_pos hdn, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      shiftByInt_neg_ofNat]
    congr
    omega
  · rw [if_neg hdn, PowerSeries.coeff_mk, ha n (lt_of_not_ge hdn)]

theorem convPow_shiftByInt_ofNat (r d : ℕ) (a : Seq) :
    convPow r (shiftByInt (d : ℤ) a) =
      shiftByInt ((r * d : ℕ) : ℤ) (convPow r a) := by
  have hseries :
      PowerSeries.mk (convPow r (shiftByInt (d : ℤ) a)) =
        PowerSeries.mk (shiftByInt ((r * d : ℕ) : ℤ) (convPow r a)) := by
    rw [powerSeries_mk_convPow, powerSeries_mk_shiftByInt_ofNat,
      powerSeries_mk_shiftByInt_ofNat, powerSeries_mk_convPow, mul_pow]
    rw [← pow_mul, Nat.mul_comm d r]
  funext n
  have hcoeff := congrArg (fun f ↦ PowerSeries.coeff ℝ n f) hseries
  simpa using hcoeff

theorem convPow_shiftByInt_neg
    (r d : ℕ) (a : Seq) (ha : CoeffSupportedFrom d a) :
    convPow r (shiftByInt (-(d : ℤ)) a) =
      shiftByInt (-((r * d : ℕ) : ℤ)) (convPow r a) := by
  have hbase := powerSeries_X_pow_mul_shiftByInt_neg d a ha
  have hleft :
      PowerSeries.X ^ (r * d) *
          PowerSeries.mk (convPow r (shiftByInt (-(d : ℤ)) a)) =
        PowerSeries.mk (convPow r a) := by
    calc
      PowerSeries.X ^ (r * d) *
            PowerSeries.mk (convPow r (shiftByInt (-(d : ℤ)) a)) =
          (PowerSeries.X ^ d) ^ r *
            (PowerSeries.mk (shiftByInt (-(d : ℤ)) a)) ^ r := by
        rw [powerSeries_mk_convPow, Nat.mul_comm r d, pow_mul]
      _ = (PowerSeries.X ^ d *
          PowerSeries.mk (shiftByInt (-(d : ℤ)) a)) ^ r := by
        rw [mul_pow]
      _ = PowerSeries.mk a ^ r := by rw [hbase]
      _ = PowerSeries.mk (convPow r a) := by rw [powerSeries_mk_convPow]
  have hright := powerSeries_X_pow_mul_shiftByInt_neg (r * d) (convPow r a)
    (convPow_supportedFrom r d a ha)
  have hseries :
      PowerSeries.mk (convPow r (shiftByInt (-(d : ℤ)) a)) =
        PowerSeries.mk (shiftByInt (-((r * d : ℕ) : ℤ)) (convPow r a)) := by
    apply PowerSeries.X_pow_mul_cancel
    exact hleft.trans hright.symm
  funext n
  have hcoeff := congrArg (fun f ↦ PowerSeries.coeff ℝ n f) hseries
  simpa using hcoeff

theorem arrivalCoeff_supportedFrom
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    CoeffSupportedFrom s (arrivalCoeff m p₀ s) := by
  intro N hN
  exact arrivalCoeff_eq_zero_of_lt m p₀ s N hN

/-- Convolution powers respect the particular integer shift `1-s` used in
arrival coordinates. -/
theorem convPow_shift_arrivalCoeff
    (r m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) :
    convPow r (shiftByInt (1 - (s : ℤ)) (arrivalCoeff m p₀ s)) =
      shiftByInt ((r : ℤ) * (1 - (s : ℤ)))
        (convPow r (arrivalCoeff m p₀ s)) := by
  cases s with
  | zero =>
      simpa using convPow_shiftByInt_ofNat r 1 (arrivalCoeff m p₀ 0)
  | succ s =>
      have hsupp : CoeffSupportedFrom s (arrivalCoeff m p₀ (s + 1)) := by
        intro N hN
        exact arrivalCoeff_eq_zero_of_lt m p₀ (s + 1) N (by omega)
      have hshift : 1 - (((s + 1 : ℕ) : ℤ)) = -(s : ℤ) := by omega
      have hmul : (r : ℤ) * -(s : ℤ) = -((r * s : ℕ) : ℤ) := by
        rw [mul_neg, ← Int.natCast_mul]
      rw [hshift, hmul]
      exact convPow_shiftByInt_neg r s (arrivalCoeff m p₀ (s + 1)) hsupp

theorem convPow_const_mul (r : ℕ) (c : ℝ) (a : Seq) :
    convPow r (fun k : ℕ ↦ c * a k) =
      fun k : ℕ ↦ c ^ r * convPow r a k := by
  induction r with
  | zero =>
      funext k
      simp [convPow]
  | succ r ih =>
      funext n
      rw [convPow_succ, convPow_succ, ih, conv_apply, conv_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_succ]
      ring

/-- Convolution-power form of the coefficient identity `eq:Qfactor`. -/
theorem convPow_orbitPositiveTilt
    (r m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    convPow r (orbitPositiveTilt m p₀ s) =
      fun N : ℕ ↦ arrivalProduct m p₀ s ^ r *
        shiftByInt ((r : ℤ) * (1 - (s : ℤ)))
          (convPow r (arrivalCoeff m p₀ s)) N := by
  rw [orbitPositiveTilt_eq_product_shift_arrival m p₀ hm hcrit
    hnotBinaryFixedPoint s]
  rw [convPow_const_mul, convPow_shift_arrivalCoeff]

private theorem source_scalar_identity
    (m r : ℕ) (x C D Cnext choose : ℝ) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hrm : r ≤ m) (hx : x ≠ 0) (hC : C ≠ 0)
    (hproduct : D * Cnext = (m : ℝ) * x ^ (m - 1) * C) :
    choose * x ^ (m - r) * C ^ r / (D * Cnext) =
      (1 / (m : ℝ)) * choose * (C / x) ^ (r - 1) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hxpow : x ^ (m - 1) = x ^ (m - r) * x ^ (r - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hCpow : C ^ r = C ^ (r - 1) * C := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  rw [hproduct, div_pow, hxpow, hCpow]
  field_simp [hm0, hx, hC]
  ring

/-- The scalar normalization of every order-`r` nonlinear source is exactly
`alpha_(r,s)`. -/
theorem arrivalSource_scalar_eq_alpha
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s r : ℕ)
    (hr : r ∈ Finset.Icc 2 m) :
    (m.choose r : ℝ) * arrivalZero m p₀ s ^ (m - r) *
          arrivalProduct m p₀ s ^ r /
        (arrivalDenom m p₀ s * arrivalProduct m p₀ (s + 1)) =
      arrivalAlpha m p₀ s r := by
  have hx := orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint s
  have hC := transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint s
  have hrBounds := Finset.mem_Icc.mp hr
  have hrOne : 1 ≤ r := by omega
  exact source_scalar_identity m r (arrivalZero m p₀ s) (arrivalProduct m p₀ s)
    (arrivalDenom m p₀ s) (arrivalProduct m p₀ (s + 1)) (m.choose r : ℝ)
    (by omega) hrOne hrBounds.2 hx.ne' hC.ne'
    (arrivalDenom_mul_product_succ m p₀ (by omega) hcrit s)

theorem shiftByInt_arrival_source_index
    (r s M : ℕ) (a : Seq) (hM : s < M) :
    shiftByInt ((r : ℤ) * (1 - (s : ℤ))) a (M - s + 1) =
      shiftByInt (((r : ℤ) - 2) * (1 - (s : ℤ))) a (M + s - 1) := by
  rw [shiftByInt, shiftByInt]
  congr 1
  have hsM : s ≤ M := by omega
  have hone : 1 ≤ M + s := by omega
  push_cast [hsM, hone]
  ring

/-- Individual order-`r` source terms agree after the `Q_s` factorization and
the scalar identity `D_s C_(s+1) = m x_s^(m-1) C_s`. -/
theorem arrivalIncrement_term_eq_formula
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s M r : ℕ)
    (hM : s < M) (hr : r ∈ Finset.Icc 2 m) :
    ((m.choose r : ℝ) * arrivalZero m p₀ s ^ (m - r) *
          convPow r (orbitPositiveTilt m p₀ s) (M - s + 1)) /
        (arrivalDenom m p₀ s * arrivalProduct m p₀ (s + 1)) =
      arrivalAlpha m p₀ s r *
        shiftByInt (((r : ℤ) - 2) * (1 - (s : ℤ)))
          (convPow r (arrivalCoeff m p₀ s)) (M + s - 1) := by
  have hQ := congrFun
    (convPow_orbitPositiveTilt r m p₀ hm hcrit hnotBinaryFixedPoint s)
    (M - s + 1)
  rw [hQ]
  rw [shiftByInt_arrival_source_index r s M
    (convPow r (arrivalCoeff m p₀ s)) hM]
  calc
    (m.choose r : ℝ) * arrivalZero m p₀ s ^ (m - r) *
          (arrivalProduct m p₀ s ^ r *
            shiftByInt (((r : ℤ) - 2) * (1 - (s : ℤ)))
              (convPow r (arrivalCoeff m p₀ s)) (M + s - 1)) /
        (arrivalDenom m p₀ s * arrivalProduct m p₀ (s + 1)) =
      (((m.choose r : ℝ) * arrivalZero m p₀ s ^ (m - r) *
            arrivalProduct m p₀ s ^ r) /
          (arrivalDenom m p₀ s * arrivalProduct m p₀ (s + 1))) *
        shiftByInt (((r : ℤ) - 2) * (1 - (s : ℤ)))
          (convPow r (arrivalCoeff m p₀ s)) (M + s - 1) := by
      ring
    _ = arrivalAlpha m p₀ s r *
        shiftByInt (((r : ℤ) - 2) * (1 - (s : ℤ)))
          (convPow r (arrivalCoeff m p₀ s)) (M + s - 1) := by
      rw [arrivalSource_scalar_eq_alpha m p₀ hm hcrit hnotBinaryFixedPoint s r hr]

theorem shiftByInt_eq_zero_of_index_lt
    (a : Seq) (d : ℕ) (e : ℤ) (N : ℕ) (ha : CoeffSupportedFrom d a)
    (hindex : (N : ℤ) - e < (d : ℤ)) :
    shiftByInt e a N = 0 := by
  rw [shiftByInt]
  by_cases hz : 0 ≤ (N : ℤ) - e
  · rw [zeroExtend_eq_of_nonneg _ _ hz]
    apply ha
    omega
  · exact zeroExtend_eq_zero_of_neg _ _ (lt_of_not_ge hz)

/-- Every term of the literal source formula has the manuscript lower support
`2s + r - 2`; the hypothesis is written without truncated subtraction. -/
theorem arrivalFormulaSource_term_eq_zero
    (m : ℕ) (p₀ : ProbabilityMass) (s N r : ℕ)
    (hN : N + 2 < 2 * s + r) :
    shiftByInt (((r : ℤ) - 2) * (1 - (s : ℤ)))
        (convPow r (arrivalCoeff m p₀ s)) N = 0 := by
  apply shiftByInt_eq_zero_of_index_lt
    (convPow r (arrivalCoeff m p₀ s)) (r * s)
    (((r : ℤ) - 2) * (1 - (s : ℤ))) N
    (convPow_supportedFrom r s (arrivalCoeff m p₀ s)
      (arrivalCoeff_supportedFrom m p₀ s))
  have hNZ : (N : ℤ) + 2 < 2 * (s : ℤ) + r := by exact_mod_cast hN
  norm_num only [Nat.cast_mul]
  have hNZ' : (N : ℤ) < 2 * (s : ℤ) + r - 2 := by linarith
  calc
    (N : ℤ) - ((r : ℤ) - 2) * (1 - (s : ℤ)) <
        (2 * (s : ℤ) + r - 2) - ((r : ℤ) - 2) * (1 - (s : ℤ)) :=
      sub_lt_sub_right hNZ' _
    _ = (r : ℤ) * s := by ring

/-- The literal finite `A_s` formula is coefficientwise nonnegative. -/
theorem arrivalFormulaSource_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ) :
    0 ≤ arrivalFormulaSource m p₀ s N := by
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg
    (arrivalAlpha_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s r)
    (shiftByInt_nonneg (((r : ℤ) - 2) * (1 - (s : ℤ)))
      (convPow r (arrivalCoeff m p₀ s))
      (convPow_nonneg r (arrivalCoeff m p₀ s)
        (arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s)) N)

/-- The whole literal source vanishes below degree `2s` (the `r = 2` boundary). -/
theorem arrivalFormulaSource_eq_zero_of_lt
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) (hN : N < 2 * s) :
    arrivalFormulaSource m p₀ s N = 0 := by
  rw [arrivalFormulaSource]
  apply Finset.sum_eq_zero
  intro r hr
  have hrTwo : 2 ≤ r := (Finset.mem_Icc.mp hr).1
  rw [arrivalFormulaSource_term_eq_zero m p₀ s N r (by omega), mul_zero]

/-- The aggregate source has nonnegative coefficients. -/
theorem arrivalSource_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ) :
    0 ≤ arrivalSource m p₀ s N := by
  exact shiftByInt_nonneg ((s : ℤ) - 1) (arrivalIncrement m p₀ s)
    (arrivalIncrement_nonneg m p₀ hm hcrit hnotBinaryFixedPoint s) N

/-- The aggregate `A_s` has no coefficient below degree `2s`. -/
theorem arrivalSource_eq_zero_of_lt
    (m : ℕ) (p₀ : ProbabilityMass) (s N : ℕ) (hN : N < 2 * s) :
    arrivalSource m p₀ s N = 0 := by
  cases s with
  | zero => omega
  | succ s =>
      rw [arrivalSource]
      have hshift : (((s + 1 : ℕ) : ℤ) - 1) = (s : ℤ) := by omega
      rw [hshift]
      by_cases hNs : N < s
      · exact shiftByInt_eq_zero_of_lt s N (arrivalIncrement m p₀ (s + 1)) hNs
      · rw [shiftByInt_of_le s N (arrivalIncrement m p₀ (s + 1)) (by omega)]
        apply arrivalIncrement_eq_zero_of_le
        omega

/-- Literal coefficient form of the renewal identity
`F_(s+1) = F_s - b_s z^s + z^(1-s) A_s`. -/
theorem arrivalCoeff_succ_eq_source_shift
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ) :
    arrivalCoeff m p₀ (s + 1) N =
      arrivalCoeff m p₀ s N -
          (if N = s then arrivalBoundary m p₀ s else 0) +
        shiftByInt (1 - (s : ℤ)) (arrivalSource m p₀ s) N := by
  rw [congrFun (shift_arrivalSource m p₀ s) N]
  exact arrivalCoeff_succ m p₀ hm hcrit hnotBinaryFixedPoint s N

/-- Above the boundary, the Laurent-style shift is an ordinary coefficient lookup. -/
theorem shiftByInt_one_sub_apply
    (s N : ℕ) (a : Seq) (hN : s < N) :
    shiftByInt (1 - (s : ℤ)) a N = a (N + s - 1) := by
  rw [shiftByInt]
  have hz : (0 : ℤ) ≤ (N : ℤ) - (1 - (s : ℤ)) := by omega
  rw [zeroExtend_eq_of_nonneg _ _ hz]
  congr
  omega

theorem shift_formulaSource_eq_zero_of_le
    (m : ℕ) (p₀ : ProbabilityMass) (s M : ℕ) (hM : M ≤ s) :
    shiftByInt (1 - (s : ℤ)) (arrivalFormulaSource m p₀ s) M = 0 := by
  cases s with
  | zero =>
      have hMzero : M = 0 := by omega
      subst M
      exact shiftByInt_eq_zero_of_lt 1 0 (arrivalFormulaSource m p₀ 0) (by omega)
  | succ s =>
      have hshift : 1 - (((s + 1 : ℕ) : ℤ)) = -(s : ℤ) := by omega
      rw [hshift, shiftByInt_neg_ofNat]
      apply arrivalFormulaSource_eq_zero_of_lt
      omega

/-- The aggregate positive increment is exactly `z^(1-s)` times the literal finite
source formula from `eq:arrivalA`. -/
theorem arrivalIncrement_eq_formula_shift
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s M : ℕ) :
    arrivalIncrement m p₀ s M =
      shiftByInt (1 - (s : ℤ)) (arrivalFormulaSource m p₀ s) M := by
  by_cases hM : s < M
  · rw [arrivalIncrement_eq_of_lt m p₀ s M hM,
      shiftByInt_one_sub_apply s M (arrivalFormulaSource m p₀ s) hM,
      arrivalFormulaSource, positiveConvolutionSource, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    exact arrivalIncrement_term_eq_formula m p₀ hm hcrit
      hnotBinaryFixedPoint s M r hM hr
  · rw [arrivalIncrement_eq_zero_of_le m p₀ s M (by omega),
      shift_formulaSource_eq_zero_of_le m p₀ s M (by omega)]

/-- Canonical coefficientwise form of `eq:arrivalrenewal`, with `A_s` given by the
literal finite formula `arrivalFormulaSource`. -/
theorem arrivalCoeff_succ_eq_formulaSource
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ) :
    arrivalCoeff m p₀ (s + 1) N =
      arrivalCoeff m p₀ s N -
          (if N = s then arrivalBoundary m p₀ s else 0) +
        shiftByInt (1 - (s : ℤ)) (arrivalFormulaSource m p₀ s) N := by
  rw [← arrivalIncrement_eq_formula_shift m p₀ hm hcrit hnotBinaryFixedPoint s N]
  exact arrivalCoeff_succ m p₀ hm hcrit hnotBinaryFixedPoint s N

/-- The coefficientwise Duhamel identity in `lem:arrival`.  At `s = 0` the range is
empty, and the statement reduces definitionally to the initial coefficient. -/
theorem arrivalCoeff_duhamel_aggregate
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ)
    (hN : s ≤ N) :
    arrivalCoeff m p₀ s N =
      arrivalCoeff m p₀ 0 N +
        ∑ j ∈ Finset.range s, arrivalSource m p₀ j (N + j - 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hsN : s < N := by omega
      rw [arrivalCoeff_succ_eq_source_shift m p₀ hm hcrit
        hnotBinaryFixedPoint s N]
      rw [if_neg (by omega : N ≠ s), sub_zero,
        shiftByInt_one_sub_apply s N (arrivalSource m p₀ s) hsN]
      rw [ih (by omega), Finset.sum_range_succ]
      ring

/-- Canonical coefficient Duhamel identity using the literal finite source `A_j`. -/
theorem arrivalCoeff_duhamel
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s N : ℕ)
    (hN : s ≤ N) :
    arrivalCoeff m p₀ s N =
      arrivalCoeff m p₀ 0 N +
        ∑ j ∈ Finset.range s, arrivalFormulaSource m p₀ j (N + j - 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hsN : s < N := by omega
      rw [arrivalCoeff_succ_eq_formulaSource m p₀ hm hcrit
        hnotBinaryFixedPoint s N]
      rw [if_neg (by omega : N ≠ s), sub_zero,
        shiftByInt_one_sub_apply s N (arrivalFormulaSource m p₀ s) hsN]
      rw [ih (by omega), Finset.sum_range_succ]
      ring

/-- The zero atom evolves by the same unary transport coefficient used in `C_s`. -/
theorem arrivalZero_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (s : ℕ) :
    arrivalZero m p₀ (s + 1) =
      transportCoeff m (orbit m p₀ s) *
        (arrivalZero m p₀ s + orbitTilt m p₀ s 1) := by
  rw [arrivalZero, orbitTilt]
  rw [zeroTilt_orbit_succ m p₀ hm hcrit s]
  rw [transportCoeff]
  simp only [arrivalZero]
  ring

private theorem kappa_fraction_identity
    (C c x q : ℝ) (hC : C ≠ 0) (hc : c ≠ 0) (hx : x ≠ 0)
    (hxq : x + q ≠ 0) :
    (C * c) / (c * (x + q)) =
      (C / x) / (1 + (C / x) * (q / C)) := by
  have hden : 1 + (C / x) * (q / C) = (x + q) / x := by
    field_simp [hC, hx]
    ring
  rw [hden]
  field_simp [hc, hx, hxq]
  ring

/-- The second recursion in `lem:arrival`:
`kappa_(s+1) = kappa_s / (1 + kappa_s b_s)`. -/
theorem arrivalKappa_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1)) (s : ℕ) :
    arrivalKappa m p₀ (s + 1) =
      arrivalKappa m p₀ s /
        (1 + arrivalKappa m p₀ s * arrivalBoundary m p₀ s) := by
  have hx : 0 < arrivalZero m p₀ s :=
    orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint s
  have hq : 0 ≤ orbitTilt m p₀ s 1 :=
    orbitTilt_nonneg m p₀ (by omega) hcrit s 1
  have hC : 0 < arrivalProduct m p₀ s :=
    transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint s
  have hc : 0 < transportCoeff m (orbit m p₀ s) :=
    transportCoeff_pos m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s) hx
  rw [arrivalKappa, arrivalBoundary_eq, arrivalProduct, transportProduct_succ,
    arrivalZero_succ m p₀ (by omega) hcrit s]
  exact kappa_fraction_identity
    (transportProduct m p₀ s) (transportCoeff m (orbit m p₀ s))
    (arrivalZero m p₀ s) (orbitTilt m p₀ s 1)
    hC.ne' hc.ne' hx.ne' (ne_of_gt (add_pos_of_pos_of_nonneg hx hq))

end

end DerridaRetaux
