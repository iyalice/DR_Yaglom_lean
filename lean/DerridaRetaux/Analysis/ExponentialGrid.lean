import DerridaRetaux.Analysis.ProfileConsequences
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

/-!
# Exponential profile on a shrinking lattice

These lemmas evaluate the infinite Riemann sum of the candidate profile
`4 exp (-2x)` without appealing to a general integration theorem.
-/

noncomputable section

/-- The denominator of the geometric grid sum has its derivative limit. -/
theorem natCast_mul_one_sub_exp_neg_two_div_tendsto_two :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) * (1 - Real.exp (-2 / (n : ℝ))))
      atTop (𝓝 2) := by
  let error : ℕ → ℝ := fun n ↦ 4 / (n : ℝ)
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [error] using
      tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)
  apply tendsto_of_abs_sub_le_error tendsto_const_nhds herror
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  let x : ℝ := -2 / (n : ℝ)
  have hxabs : |x| ≤ 1 := by
    dsimp only [x]
    rw [abs_div, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
      abs_of_pos hnpos]
    exact (div_le_iff₀ hnpos).2 (by
      simpa only [one_mul] using (show (2 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn))
  have hremainder := Real.abs_exp_sub_one_sub_id_le hxabs
  have halgebra :
      (n : ℝ) * (1 - Real.exp x) - 2 =
        -(n : ℝ) * (Real.exp x - 1 - x) := by
    dsimp only [x]
    field_simp only [hn0]
    ring
  rw [halgebra, abs_mul, abs_neg, abs_of_pos hnpos]
  calc
    (n : ℝ) * |Real.exp x - 1 - x| ≤ (n : ℝ) * x ^ 2 :=
      mul_le_mul_of_nonneg_left hremainder hnpos.le
    _ = error n := by
      dsimp only [x, error]
      field_simp only [hn0]
      ring

/-- The full infinite grid sum of `4 exp (-2x)` converges to its mass `2`. -/
theorem exponentialProfile_gridMass_tendsto_two :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ)⁻¹ *
          ∑' j : ℕ, 4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ))))
      atTop (𝓝 2) := by
  have hdenom := natCast_mul_one_sub_exp_neg_two_div_tendsto_two
  have hinv :
      Tendsto
        (fun n : ℕ ↦
          ((n : ℝ) * (1 - Real.exp (-2 / (n : ℝ))))⁻¹)
        atTop (𝓝 (2 : ℝ)⁻¹) :=
    hdenom.inv₀ (by norm_num)
  have hscaled := (tendsto_const_nhds.mul hinv :
    Tendsto
      (fun n : ℕ ↦ 4 *
        ((n : ℝ) * (1 - Real.exp (-2 / (n : ℝ))))⁻¹)
      atTop (𝓝 (4 * (2 : ℝ)⁻¹)))
  have htarget : 4 * (2 : ℝ)⁻¹ = 2 := by norm_num
  rw [htarget] at hscaled
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  let r : ℝ := Real.exp (-2 / (n : ℝ))
  have hexponent : -2 / (n : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) hnpos
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr hexponent
  have hgeom := tsum_geometric_of_norm_lt_one hrnorm
  have hterms :
      (fun j : ℕ ↦ 4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))) =
        fun j : ℕ ↦ 4 * r ^ j := by
    funext j
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp only [hn0]
    ring
  rw [hterms, tsum_mul_left, hgeom]
  dsimp only [r]
  field_simp only [hn0]
  ring

end

end DerridaRetaux
