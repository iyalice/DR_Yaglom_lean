import DerridaRetaux.Model.Criticality
import DerridaRetaux.Model.NormalizedTilt
import Mathlib.Tactic

/-!
# The normalized tilted recursion

This file proves the coefficientwise and summability-safe forms of source equation
`eq:tilt`.  The apparent division by the generating-function variable is removed at the
coefficient level.  Divided forms are stated only after the relevant tilted partition,
arity, and recursion denominators have been proved nonzero.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- The source denominator `D = 1 + (m - 1) x^m`, with `x = q(0)`. -/
def tiltDenom (m : ℕ) (p : ProbabilityMass) : ℝ :=
  1 + ((m : ℝ) - 1) * zeroTilt m p ^ m

theorem tiltDenom_eq (m : ℕ) (p : ProbabilityMass) :
    tiltDenom m p = 1 + ((m : ℝ) - 1) * zeroTilt m p ^ m :=
  rfl

/-- The recursion denominator is at least one for a critical law. -/
theorem tiltDenom_one_le (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : 1 ≤ tiltDenom m p := by
  rw [tiltDenom]
  exact le_add_of_nonneg_right
    (mul_nonneg (critical_tiltFactor_pos m p hm hcrit).le
      (pow_nonneg (normalizedTilt_nonneg m p hm hcrit 0) m))

/-- In particular, division by the recursion denominator is legitimate. -/
theorem tiltDenom_pos (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) : 0 < tiltDenom m p :=
  lt_of_lt_of_le zero_lt_one (tiltDenom_one_le m p hm hcrit)

private theorem convPow_const_mul (r : ℕ) (c : ℝ) (a : Seq) :
    convPow r (fun k : ℕ ↦ c * a k) = fun k : ℕ ↦ c ^ r * convPow r a k := by
  induction r with
  | zero =>
      funext k
      simp [convPow]
  | succ r ih =>
      funext n
      rw [convPow_succ, convPow_succ, ih, conv_apply, conv_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ]
      ring

/-- Convolution powers of the normalized tilt are normalized tilted convolution powers.

The denominator is established positive before the coefficient identity is cleared.
-/
theorem convPow_normalizedTilt (r m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    convPow r (normalizedTilt m p) = fun k : ℕ ↦
      (m : ℝ) ^ k * convPow r p k / tiltedPartition m p ^ r := by
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  have hq :
      normalizedTilt m p =
        fun k : ℕ ↦ (tiltedPartition m p)⁻¹ * powerScale (m : ℝ) p k := by
    funext k
    simp [normalizedTilt, powerScale, div_eq_mul_inv, mul_comm]
  rw [hq, convPow_const_mul, convPow_powerScale]
  funext k
  simp only [powerScale_apply]
  field_simp [hG.ne']

/-- The coefficient of degree one in a convolution power. -/
theorem convPow_apply_one (r : ℕ) (a : Seq) :
    convPow r a 1 = (r : ℝ) * a 0 ^ (r - 1) * a 1 := by
  cases r with
  | zero => simp [convPow, diracSeq]
  | succ r =>
      induction r with
      | zero => simp
      | succ r ih =>
          rw [convPow_succ, conv_succ_left]
          simp only [convPow_apply_zero, shiftLeft_apply, conv_zero]
          rw [ih]
          push_cast
          ring

/-- The scalar part of `eq:tilt` for the coefficient-level DR step:
`G(next) = G^m D / m`. -/
theorem tiltedPartition_drStepProb_eq (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    tiltedPartition m (drStepProb m p) =
      tiltedPartition m p ^ m * tiltDenom m p / (m : ℝ) := by
  have hm0Nat : m ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0Nat
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  apply (eq_div_iff hm0).2
  rw [mul_comm]
  rw [tiltedPartition_drStepProb_cross m p hm hcrit.1]
  rw [tiltDenom, zeroTilt_eq]
  field_simp [hG.ne']
  ring

/-- The same scalar recursion for the PMF-backed paper step. -/
theorem tiltedPartition_drStep_eq (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p) :
    tiltedPartition m (drStep m p) =
      tiltedPartition m p ^ m * tiltDenom m p / (m : ℝ) := by
  rw [drStep_eq_drStepProb]
  exact tiltedPartition_drStepProb_eq m p hm hcrit

/-- The source-indexed scalar recursion `G_(n+1) = G_n^m D_n / m`. -/
theorem tiltedPartition_orbit_succ_eq (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p₀) (n : ℕ) :
    tiltedPartition m (orbit m p₀ (n + 1)) =
      tiltedPartition m (orbit m p₀ n) ^ m * tiltDenom m (orbit m p₀ n) /
        (m : ℝ) := by
  rw [orbit_succ]
  exact tiltedPartition_drStep_eq m (orbit m p₀ n) hm (orbit_critical m p₀ hm hcrit n)

/-- The zero coefficient of `eq:tilt`, in cross-multiplied form. -/
theorem normalizedTilt_drStepProb_zero_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    tiltDenom m p * normalizedTilt m (drStepProb m p) 0 =
      convPow m (normalizedTilt m p) 1 + (m : ℝ) * zeroTilt m p ^ m := by
  have hm0Nat : m ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0Nat
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  have hD := tiltDenom_pos m p hm hcrit
  rw [normalizedTilt_apply, drStepProb_apply, drStepSeq_zero, convPow_apply_zero]
  rw [congrFun (convPow_normalizedTilt m m p hm hcrit) 1]
  rw [tiltedPartition_drStepProb_eq m p hm hcrit]
  rw [zeroTilt_eq]
  norm_num only [Nat.cast_one, pow_one]
  field_simp [hG.ne', hD.ne', hm0]
  ring

/-- The factored zero-atom recursion extracted from `eq:tilt`. -/
theorem zeroTilt_drStepProb_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    tiltDenom m p * zeroTilt m (drStepProb m p) =
      (m : ℝ) * zeroTilt m p ^ (m - 1) *
        (zeroTilt m p + normalizedTilt m p 1) := by
  rw [zeroTilt, normalizedTilt_drStepProb_zero_cross m p hm hcrit]
  rw [convPow_apply_one]
  change (m : ℝ) * zeroTilt m p ^ (m - 1) * normalizedTilt m p 1 +
      (m : ℝ) * zeroTilt m p ^ m = _
  have hpow : zeroTilt m p ^ (m - 1) * zeroTilt m p = zeroTilt m p ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [← hpow]
  ring

/-- The divided factored zero-atom recursion, after proving `D > 0`. -/
theorem zeroTilt_drStepProb
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    zeroTilt m (drStepProb m p) =
      ((m : ℝ) * zeroTilt m p ^ (m - 1) *
        (zeroTilt m p + normalizedTilt m p 1)) / tiltDenom m p := by
  have hD := tiltDenom_pos m p hm hcrit
  apply (eq_div_iff hD.ne').2
  simpa [mul_comm] using zeroTilt_drStepProb_cross m p hm hcrit

/-- Every positive coefficient of `eq:tilt`, in cross-multiplied form. -/
theorem normalizedTilt_drStepProb_succ_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) (k : ℕ) :
    tiltDenom m p * normalizedTilt m (drStepProb m p) (k + 1) =
      convPow m (normalizedTilt m p) (k + 2) := by
  have hm0Nat : m ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0Nat
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  have hD := tiltDenom_pos m p hm hcrit
  rw [normalizedTilt_apply, drStepProb_apply, drStepSeq_succ]
  rw [congrFun (convPow_normalizedTilt m m p hm hcrit) (k + 2)]
  rw [tiltedPartition_drStepProb_eq m p hm hcrit]
  field_simp [hG.ne', hD.ne', hm0]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring

/-- Uniform coefficientwise form of the removable `z`-division in `eq:tilt`. -/
theorem normalizedTilt_drStepProb_coeff_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) (k : ℕ) :
    tiltDenom m p * normalizedTilt m (drStepProb m p) k =
      convPow m (normalizedTilt m p) (k + 1) +
        if k = 0 then (m : ℝ) * zeroTilt m p ^ m else 0 := by
  cases k with
  | zero => simpa using normalizedTilt_drStepProb_zero_cross m p hm hcrit
  | succ k => simpa using normalizedTilt_drStepProb_succ_cross m p hm hcrit k

/-- The divided zero-coefficient recursion, after proving `D > 0`. -/
theorem normalizedTilt_drStepProb_zero
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    normalizedTilt m (drStepProb m p) 0 =
      (convPow m (normalizedTilt m p) 1 + (m : ℝ) * zeroTilt m p ^ m) /
        tiltDenom m p := by
  have hD := tiltDenom_pos m p hm hcrit
  apply (eq_div_iff hD.ne').2
  simpa [mul_comm] using normalizedTilt_drStepProb_zero_cross m p hm hcrit

/-- The divided positive-coefficient recursion, after proving `D > 0`. -/
theorem normalizedTilt_drStepProb_succ
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) (k : ℕ) :
    normalizedTilt m (drStepProb m p) (k + 1) =
      convPow m (normalizedTilt m p) (k + 2) / tiltDenom m p := by
  have hD := tiltDenom_pos m p hm hcrit
  apply (eq_div_iff hD.ne').2
  simpa [mul_comm] using normalizedTilt_drStepProb_succ_cross m p hm hcrit k

/-- Uniform divided coefficient recursion. -/
theorem normalizedTilt_drStepProb_coeff
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) (k : ℕ) :
    normalizedTilt m (drStepProb m p) k =
      (convPow m (normalizedTilt m p) (k + 1) +
        if k = 0 then (m : ℝ) * zeroTilt m p ^ m else 0) / tiltDenom m p := by
  have hD := tiltDenom_pos m p hm hcrit
  apply (eq_div_iff hD.ne').2
  simpa [mul_comm] using normalizedTilt_drStepProb_coeff_cross m p hm hcrit k

/-- Orbit form of the coefficient recursion, including its exceptional zero coefficient. -/
theorem normalizedTilt_orbit_succ_coeff
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (n k : ℕ) :
    normalizedTilt m (orbit m p₀ (n + 1)) k =
      (convPow m (normalizedTilt m (orbit m p₀ n)) (k + 1) +
        if k = 0 then (m : ℝ) * zeroTilt m (orbit m p₀ n) ^ m else 0) /
          tiltDenom m (orbit m p₀ n) := by
  rw [orbit_succ, drStep_eq_drStepProb]
  exact normalizedTilt_drStepProb_coeff m (orbit m p₀ n) hm
    (orbit_critical m p₀ hm hcrit n) k

/-- Source-indexed factored recursion for the zero tilted atom `x_n`. -/
theorem zeroTilt_orbit_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀) (n : ℕ) :
    zeroTilt m (orbit m p₀ (n + 1)) =
      ((m : ℝ) * zeroTilt m (orbit m p₀ n) ^ (m - 1) *
        (zeroTilt m (orbit m p₀ n) + normalizedTilt m (orbit m p₀ n) 1)) /
          tiltDenom m (orbit m p₀ n) := by
  rw [orbit_succ, drStep_eq_drStepProb]
  exact zeroTilt_drStepProb m (orbit m p₀ n) hm (orbit_critical m p₀ hm hcrit n)

/-- The normalized tilted generating series has the scaled original series as its sum. -/
theorem normalizedTiltGenerating_hasSum
    (z : ℝ) (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (h : GeneratingSummable ((m : ℝ) * z) p) :
    HasSum (fun k : ℕ ↦ z ^ k * normalizedTilt m p k)
      (generatingFunction ((m : ℝ) * z) p / tiltedPartition m p) := by
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  have hscaled :=
    (generatingFunction_hasSum ((m : ℝ) * z) p h).div_const (tiltedPartition m p)
  convert hscaled using 1
  funext k
  simp only [powerScale_apply, normalizedTilt_apply]
  rw [mul_pow]
  field_simp [hG.ne']
  ring

/-- The normalized tilted generating function `H(z)`. -/
def normalizedTiltGeneratingFunction (z : ℝ) (m : ℕ) (p : ProbabilityMass) : ℝ :=
  ∑' k : ℕ, z ^ k * normalizedTilt m p k

/-- Summability of `H` follows from summability of the original series at `m z`. -/
theorem normalizedTiltGenerating_summable
    (z : ℝ) (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (h : GeneratingSummable ((m : ℝ) * z) p) :
    Summable (fun k : ℕ ↦ z ^ k * normalizedTilt m p k) :=
  (normalizedTiltGenerating_hasSum z m p hm hcrit h).summable

/-- Evaluation of `H` through the existing generating-function API. -/
theorem normalizedTiltGeneratingFunction_eq
    (z : ℝ) (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (h : GeneratingSummable ((m : ℝ) * z) p) :
    normalizedTiltGeneratingFunction z m p =
      generatingFunction ((m : ℝ) * z) p / tiltedPartition m p :=
  (normalizedTiltGenerating_hasSum z m p hm hcrit h).tsum_eq

/-- The normalized series is the generating function of `normalizedTiltLaw`. -/
theorem normalizedTiltGeneratingFunction_eq_law
    (z : ℝ) (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    normalizedTiltGeneratingFunction z m p =
      generatingFunction z (normalizedTiltLaw m p hm hcrit) :=
  rfl

/-- Cross-multiplied, summability-safe form of the generating-function part of `eq:tilt`.

It remains valid at `z = 0`; hence no removable singularity is introduced.
-/
theorem normalizedTiltGeneratingFunction_drStepProb_cross
    (z : ℝ) (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hp : GeneratingSummable ((m : ℝ) * z) p)
    (hnext : GeneratingSummable ((m : ℝ) * z) (drStepProb m p)) :
    z * tiltDenom m p * normalizedTiltGeneratingFunction z m (drStepProb m p) =
      normalizedTiltGeneratingFunction z m p ^ m +
        ((m : ℝ) * z - 1) * zeroTilt m p ^ m := by
  have hm0Nat : m ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0Nat
  have hG := normalizedTilt_denominator_pos m p hm hcrit
  have hD := tiltDenom_pos m p hm hcrit
  have hnextCrit := critical_drStepProb m p hm hcrit
  have hcross := generatingFunction_drStep_cross m ((m : ℝ) * z) p hp hnext
  rw [normalizedTiltGeneratingFunction_eq z m p hm hcrit hp]
  rw [normalizedTiltGeneratingFunction_eq z m (drStepProb m p) hm hnextCrit hnext]
  rw [tiltedPartition_drStepProb_eq m p hm hcrit]
  rw [zeroTilt_eq]
  field_simp [hm0, hG.ne', hD.ne']
  linear_combination tiltDenom m p * tiltedPartition m p ^ m * hcross

/-- The divided manuscript form of `eq:tilt`, valid after proving `z D` nonzero. -/
theorem normalizedTiltGeneratingFunction_drStepProb
    (z : ℝ) (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hp : GeneratingSummable ((m : ℝ) * z) p)
    (hnext : GeneratingSummable ((m : ℝ) * z) (drStepProb m p)) (hz : z ≠ 0) :
    normalizedTiltGeneratingFunction z m (drStepProb m p) =
      (normalizedTiltGeneratingFunction z m p ^ m +
        ((m : ℝ) * z - 1) * zeroTilt m p ^ m) / (z * tiltDenom m p) := by
  have hD := tiltDenom_pos m p hm hcrit
  apply (eq_div_iff (mul_ne_zero hz hD.ne')).2
  calc
    normalizedTiltGeneratingFunction z m (drStepProb m p) * (z * tiltDenom m p) =
        z * tiltDenom m p * normalizedTiltGeneratingFunction z m (drStepProb m p) := by
      ring
    _ = normalizedTiltGeneratingFunction z m p ^ m +
        ((m : ℝ) * z - 1) * zeroTilt m p ^ m :=
      normalizedTiltGeneratingFunction_drStepProb_cross z m p hm hcrit hp hnext

/-- Cross-multiplied `eq:tilt` for the PMF-backed paper step. -/
theorem normalizedTiltGeneratingFunction_drStep_cross
    (z : ℝ) (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hp : GeneratingSummable ((m : ℝ) * z) p)
    (hnext : GeneratingSummable ((m : ℝ) * z) (drStep m p)) :
    z * tiltDenom m p * normalizedTiltGeneratingFunction z m (drStep m p) =
      normalizedTiltGeneratingFunction z m p ^ m +
        ((m : ℝ) * z - 1) * zeroTilt m p ^ m := by
  rw [drStep_eq_drStepProb] at hnext ⊢
  exact normalizedTiltGeneratingFunction_drStepProb_cross z m p hm hcrit hp hnext

/-- Divided `eq:tilt` for the PMF-backed paper step. -/
theorem normalizedTiltGeneratingFunction_drStep
    (z : ℝ) (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hp : GeneratingSummable ((m : ℝ) * z) p)
    (hnext : GeneratingSummable ((m : ℝ) * z) (drStep m p)) (hz : z ≠ 0) :
    normalizedTiltGeneratingFunction z m (drStep m p) =
      (normalizedTiltGeneratingFunction z m p ^ m +
        ((m : ℝ) * z - 1) * zeroTilt m p ^ m) / (z * tiltDenom m p) := by
  rw [drStep_eq_drStepProb] at hnext ⊢
  exact normalizedTiltGeneratingFunction_drStepProb z m p hm hcrit hp hnext hz

/-- Cross-multiplied source-indexed form of `eq:tilt`. -/
theorem normalizedTiltGeneratingFunction_orbit_succ_cross
    (z : ℝ) (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p₀) (n : ℕ)
    (hn : GeneratingSummable ((m : ℝ) * z) (orbit m p₀ n))
    (hsucc : GeneratingSummable ((m : ℝ) * z) (orbit m p₀ (n + 1))) :
    z * tiltDenom m (orbit m p₀ n) *
        normalizedTiltGeneratingFunction z m (orbit m p₀ (n + 1)) =
      normalizedTiltGeneratingFunction z m (orbit m p₀ n) ^ m +
        ((m : ℝ) * z - 1) * zeroTilt m (orbit m p₀ n) ^ m := by
  rw [orbit_succ, drStep_eq_drStepProb] at hsucc ⊢
  exact normalizedTiltGeneratingFunction_drStepProb_cross z m (orbit m p₀ n) hm
    (orbit_critical m p₀ hm hcrit n) hn hsucc

/-- Divided source-indexed form of `eq:tilt`, valid for `z ≠ 0`. -/
theorem normalizedTiltGeneratingFunction_orbit_succ
    (z : ℝ) (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m)
    (hcrit : Critical m p₀) (n : ℕ)
    (hn : GeneratingSummable ((m : ℝ) * z) (orbit m p₀ n))
    (hsucc : GeneratingSummable ((m : ℝ) * z) (orbit m p₀ (n + 1))) (hz : z ≠ 0) :
    normalizedTiltGeneratingFunction z m (orbit m p₀ (n + 1)) =
      (normalizedTiltGeneratingFunction z m (orbit m p₀ n) ^ m +
        ((m : ℝ) * z - 1) * zeroTilt m (orbit m p₀ n) ^ m) /
          (z * tiltDenom m (orbit m p₀ n)) := by
  rw [orbit_succ, drStep_eq_drStepProb] at hsucc ⊢
  exact normalizedTiltGeneratingFunction_drStepProb z m (orbit m p₀ n) hm
    (orbit_critical m p₀ hm hcrit n) hn hsucc hz

end

end DerridaRetaux
