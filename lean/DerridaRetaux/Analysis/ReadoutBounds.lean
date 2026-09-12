import DerridaRetaux.Model.Readout
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Geometric readout bounds

This file carries out the exact telescoping and geometric-series calculation used
after source equation `eq:survivalread` (`U14`).
-/

/-- The geometric readout weights have total mass `1/(m-1)`. -/
theorem inversePower_succ_hasSum (m : ℕ) (hm : 2 ≤ m) :
    HasSum (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹) (1 / ((m : ℝ) - 1)) := by
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hr0 : 0 ≤ (m : ℝ)⁻¹ := by positivity
  have hr1 : (m : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hmReal
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (m : ℝ)⁻¹
  convert hgeo using 1
  · funext j
    rw [← inv_pow, pow_succ']
  · field_simp

/-- The first moment of the geometric readout weights is `1/(m-1)^2`. -/
theorem nat_mul_inversePower_succ_hasSum (m : ℕ) (hm : 2 ≤ m) :
    HasSum (fun j : ℕ ↦ (j : ℝ) * ((m : ℝ) ^ (j + 1))⁻¹)
      (1 / ((m : ℝ) - 1) ^ 2) := by
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hrNorm : ‖(m : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ hmReal
  have hgeo :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hrNorm).mul_left (m : ℝ)⁻¹
  convert hgeo using 1
  · funext j
    rw [← inv_pow, pow_succ']
    ring
  · have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hmReal)
    have hfactor : (m : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hmReal)
    have hratio :
        (m : ℝ)⁻¹ / (1 - (m : ℝ)⁻¹) = 1 / ((m : ℝ) - 1) := by
      field_simp [hm0, hfactor]
    have hvalue :
      (m : ℝ)⁻¹ * ((m : ℝ)⁻¹ / (1 - (m : ℝ)⁻¹) ^ 2) =
          1 / ((m : ℝ) - 1) ^ 2 := by
      calc
        (m : ℝ)⁻¹ * ((m : ℝ)⁻¹ / (1 - (m : ℝ)⁻¹) ^ 2) =
            (m : ℝ)⁻¹ ^ 2 / (1 - (m : ℝ)⁻¹) ^ 2 := by ring
        _ = ((m : ℝ)⁻¹ / (1 - (m : ℝ)⁻¹)) ^ 2 := by rw [div_pow]
        _ = (1 / ((m : ℝ) - 1)) ^ 2 := by rw [hratio]
        _ = 1 / ((m : ℝ) - 1) ^ 2 := by rw [div_pow]; norm_num
    exact hvalue.symm

/-- A uniform first-difference bound telescopes to a linear pointwise bound. -/
theorem abs_sub_zero_le_of_discreteDerivative
    (f : Seq) (B : ℝ) (hB : 0 ≤ B) (hdelta : SupLE (discreteDerivative f) B)
    (j : ℕ) :
    |f j - f 0| ≤ (j : ℝ) * B := by
  induction j with
  | zero =>
      have hzero : 0 ≤ (0 : ℝ) * B := mul_nonneg (le_refl 0) hB
      simpa only [sub_self, abs_zero, Nat.cast_zero] using hzero
  | succ j ih =>
      have hstep := hdelta j
      simp only [discreteDerivative_apply] at hstep
      calc
        |f (j + 1) - f 0| = |(f j - f 0) - (f j - f (j + 1))| := by ring_nf
        _ ≤ |f j - f 0| + |f j - f (j + 1)| := abs_sub _ _
        _ ≤ (j : ℝ) * B + B := add_le_add ih hstep
        _ = ((j + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- A Lipschitz sequence differs from its boundary-constant geometric readout by the
exact source constant `B/(m-1)^2`. -/
theorem geometricReadout_sub_boundary_le
    (m : ℕ) (hm : 2 ≤ m) (f : Seq) (R B : ℝ) (hB : 0 ≤ B)
    (hdelta : SupLE (discreteDerivative f) B)
    (hreadout : HasSum (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹ * f j) R) :
    |R - f 0 / ((m : ℝ) - 1)| ≤ B / ((m : ℝ) - 1) ^ 2 := by
  have hconstant := (inversePower_succ_hasSum m hm).mul_right (f 0)
  have herror :
      HasSum
        (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹ * (f j - f 0))
        (R - f 0 / ((m : ℝ) - 1)) := by
    convert hreadout.sub hconstant using 1
    · funext j
      ring
    · ring
  have hmajor := (nat_mul_inversePower_succ_hasSum m hm).mul_left B
  have hbound : ∀ j : ℕ,
      ‖((m : ℝ) ^ (j + 1))⁻¹ * (f j - f 0)‖ ≤
        B * ((j : ℝ) * ((m : ℝ) ^ (j + 1))⁻¹) := by
    intro j
    have hweight : 0 ≤ ((m : ℝ) ^ (j + 1))⁻¹ := by positivity
    have hj := abs_sub_zero_le_of_discreteDerivative f B hB hdelta j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight]
    calc
      ((m : ℝ) ^ (j + 1))⁻¹ * |f j - f 0| ≤
          ((m : ℝ) ^ (j + 1))⁻¹ * ((j : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hj hweight
      _ = B * ((j : ℝ) * ((m : ℝ) ^ (j + 1))⁻¹) := by ring
  have hnorm := herror.norm_le_of_bounded hmajor hbound
  simpa [Real.norm_eq_abs] using hnorm

/-- Literal survival-probability estimate obtained by multiplying the geometric
readout error by `G/(m-1)`. -/
theorem survival_sub_boundary_le
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (B : ℝ) (hB : 0 ≤ B) (hdelta : SupLE (discreteDerivative (rho m p)) B) :
    |survival p -
        tiltedPartition m p * rho m p 0 / ((m : ℝ) - 1) ^ 2| ≤
      tiltedPartition m p * B / ((m : ℝ) - 1) ^ 3 := by
  have hmOne : 1 ≤ m := by omega
  have hfactor : 0 < (m : ℝ) - 1 := critical_tiltFactor_pos m p hmOne hcrit
  have hG : 0 < tiltedPartition m p := normalizedTilt_denominator_pos m p hmOne hcrit
  have hreadout := geometricReadout_sub_boundary_le m hm (rho m p)
    (survivalReadout m p) B hB hdelta
    (by simpa [survivalReadout] using
      (show HasSum
        (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹ * rho m p j)
        (survivalReadout m p) from
          ((survivalReadout_hasSum m p hmOne hcrit).summable.hasSum)))
  have hsurvival := survival_eq_partition_mul_readout m p hm hcrit
  have hscale : 0 ≤ tiltedPartition m p / ((m : ℝ) - 1) :=
    div_nonneg hG.le hfactor.le
  have heq :
      survival p - tiltedPartition m p * rho m p 0 / ((m : ℝ) - 1) ^ 2 =
        (tiltedPartition m p / ((m : ℝ) - 1)) *
          (survivalReadout m p - rho m p 0 / ((m : ℝ) - 1)) := by
    rw [hsurvival]
    field_simp [hfactor.ne']
    ring
  calc
    |survival p - tiltedPartition m p * rho m p 0 / ((m : ℝ) - 1) ^ 2| =
        (tiltedPartition m p / ((m : ℝ) - 1)) *
          |survivalReadout m p - rho m p 0 / ((m : ℝ) - 1)| := by
      rw [heq, abs_mul, abs_of_nonneg hscale]
    _ ≤ (tiltedPartition m p / ((m : ℝ) - 1)) *
        (B / ((m : ℝ) - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hreadout hscale
    _ = tiltedPartition m p * B / ((m : ℝ) - 1) ^ 3 := by
      rw [div_mul_div_comm]
      congr 1
      rw [pow_succ']
      ring

end

end DerridaRetaux
