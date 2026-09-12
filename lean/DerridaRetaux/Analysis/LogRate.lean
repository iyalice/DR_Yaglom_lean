import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

/-!
# The logarithmic smoothing rate

The gradient estimate in the manuscript has size
`C * log (n + 2) / (n + 1)^3`.  This file proves directly that multiplication
by `n^2` still leaves a quantity tending to zero.
-/

/-- The standard `log x / x → 0` limit sampled at `x = n + 2`. -/
theorem log_nat_add_two_div_self_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2))
      atTop (𝓝 0) := by
  have hsample : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa only [Function.comp_apply, id_eq] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hsample

/-- Replacing the denominator `n + 2` by the source scale `n + 1` preserves
the zero limit. -/
theorem log_nat_add_two_div_succ_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  have hratio :
      Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2) / ((n : ℝ) + 1))
        atTop (𝓝 1) := by
    simpa only [one_mul, one_div, inv_one, add_comm] using
      RCLike.tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) 2 1 1 one_ne_zero
  have hproduct := log_nat_add_two_div_self_tendsto_zero.mul hratio
  convert hproduct using 1
  · funext n
    have hnOne : (n : ℝ) + 1 ≠ 0 := by positivity
    have hnTwo : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp only [hnOne, hnTwo]
    ring
  · ring

/-- Exact source rate: `n² * C log(n+2)/(n+1)³ → 0`. -/
theorem natSquare_mul_log_gradient_rate_tendsto_zero (C : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) ^ 2 *
          (C * Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 3))
      atTop (𝓝 0) := by
  have hratio :
      Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hconstant : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
  have hproduct :
      Tendsto
        (fun n : ℕ ↦
          C * ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 *
            (Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
    simpa only [one_pow, mul_zero] using
      (hconstant.mul (hratio.pow 2)).mul
        log_nat_add_two_div_succ_tendsto_zero
  convert hproduct using 1
  funext n
  have hnOne : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp only [hnOne]
  ring

end DerridaRetaux
