import DerridaRetaux.Model.TransportCoefficient
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Limit of the linear transport product

This file proves the analytic infinite-product step in source equation `eq:C`.
The orbit-specific estimate `Summable (fun n ↦ 1 - c_n)` is an explicit theorem
parameter here; the preceding coarse-estimate module supplies it without enlarging
the permanent human interface.
-/

/-- The infinite transport product `C_∞`. -/
def transportProductLimit (m : ℕ) (p₀ : ProbabilityMass) : ℝ :=
  ∏' n : ℕ, transportCoeff m (orbit m p₀ n)

private theorem transportCoeff_sub_one_summable
    (m : ℕ) (p₀ : ProbabilityMass)
    (hdefect : Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n))) :
    Summable (fun n : ℕ ↦ transportCoeff m (orbit m p₀ n) - 1) := by
  simpa only [neg_sub] using hdefect.neg

/-- Summable transport defects make the coefficient family multipliable. -/
theorem transportCoeff_multipliable_of_defect_summable
    (m : ℕ) (p₀ : ProbabilityMass)
    (hdefect : Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n))) :
    Multipliable (fun n : ℕ ↦ transportCoeff m (orbit m p₀ n)) := by
  have hsub := transportCoeff_sub_one_summable m p₀ hdefect
  convert Real.multipliable_one_add_of_summable hsub using 1
  funext n
  ring

/-- Along an admissible critical orbit the infinite product is strictly positive. -/
theorem transportProductLimit_pos_of_defect_summable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hdefect : Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n))) :
    0 < transportProductLimit m p₀ := by
  have hsub := transportCoeff_sub_one_summable m p₀ hdefect
  have hlog :
      Summable (fun n : ℕ ↦ Real.log (transportCoeff m (orbit m p₀ n))) := by
    convert Real.summable_log_one_add_of_summable hsub using 1
    funext n
    congr 1
    ring
  have hpositive : ∀ n : ℕ, 0 < transportCoeff m (orbit m p₀ n) := by
    intro n
    exact transportCoeff_pos m (orbit m p₀ n) (by omega)
      (orbit_critical m p₀ (by omega) hcrit n)
      (orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint n)
  have hproduct := Real.rexp_tsum_eq_tprod hpositive hlog
  rw [transportProductLimit, ← hproduct]
  exact Real.exp_pos _

/-- The finite products converge to the infinite product. -/
theorem tendsto_transportProduct_of_defect_summable
    (m : ℕ) (p₀ : ProbabilityMass)
    (hdefect : Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n))) :
    Tendsto (transportProduct m p₀) atTop (𝓝 (transportProductLimit m p₀)) := by
  have hmul := transportCoeff_multipliable_of_defect_summable m p₀ hdefect
  simpa only [transportProductLimit, transportProduct] using hmul.tendsto_prod_tprod_nat

/-- The finite transport products form a decreasing sequence. -/
theorem antitone_transportProduct
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀) :
    Antitone (transportProduct m p₀) :=
  antitone_nat_of_succ_le (transportProduct_succ_le m p₀ hm hcrit)

/-- Every finite product lies above its positive infinite-product limit. -/
theorem transportProductLimit_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (hdefect : Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n)))
    (n : ℕ) :
    transportProductLimit m p₀ ≤ transportProduct m p₀ n := by
  exact (antitone_transportProduct m p₀ hm hcrit).le_of_tendsto
    (tendsto_transportProduct_of_defect_summable m p₀ hdefect) n

/-- The infinite-product limit also bounds each individual transport coefficient. -/
theorem transportProductLimit_le_transportCoeff
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (hdefect : Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n)))
    (n : ℕ) :
    transportProductLimit m p₀ ≤ transportCoeff m (orbit m p₀ n) := by
  have hlimit := transportProductLimit_le m p₀ hm hcrit hdefect (n + 1)
  have hproductNonneg := transportProduct_nonneg m p₀ hm hcrit n
  have hproductOne : transportProduct m p₀ n ≤ 1 := by
    simpa [transportProduct_zero] using
      (antitone_transportProduct m p₀ hm hcrit (Nat.zero_le n))
  have hcoeffNonneg := transportCoeff_nonneg m (orbit m p₀ n) hm
    (orbit_critical m p₀ hm hcrit n)
  rw [transportProduct_succ] at hlimit
  calc
    transportProductLimit m p₀ ≤
        transportProduct m p₀ n * transportCoeff m (orbit m p₀ n) := hlimit
    _ ≤ 1 * transportCoeff m (orbit m p₀ n) :=
      mul_le_mul_of_nonneg_right hproductOne hcoeffNonneg
    _ = transportCoeff m (orbit m p₀ n) := one_mul _

/-- A single explicit constant uniformly bounds all inverse finite products. -/
theorem transportProduct_inverse_uniform
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hdefect : Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n))) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, (transportProduct m p₀ n)⁻¹ ≤ B := by
  have hlimitPos := transportProductLimit_pos_of_defect_summable m p₀ hm hcrit
    hnotBinaryFixedPoint hdefect
  refine ⟨(transportProductLimit m p₀)⁻¹, inv_pos.mpr hlimitPos, ?_⟩
  intro n
  exact (inv_le_inv₀ (transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint n)
    hlimitPos).2 (transportProductLimit_le m p₀ (by omega) hcrit hdefect n)

/-- The same limit yields a uniform inverse bound for the individual coefficients. -/
theorem transportCoeff_inverse_uniform
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hdefect : Summable (fun n : ℕ ↦ 1 - transportCoeff m (orbit m p₀ n))) :
    ∃ B : ℝ, 0 < B ∧
      ∀ n : ℕ, (transportCoeff m (orbit m p₀ n))⁻¹ ≤ B := by
  have hlimitPos := transportProductLimit_pos_of_defect_summable m p₀ hm hcrit
    hnotBinaryFixedPoint hdefect
  refine ⟨(transportProductLimit m p₀)⁻¹, inv_pos.mpr hlimitPos, ?_⟩
  intro n
  have hcoeffPos := transportCoeff_pos m (orbit m p₀ n) (by omega)
    (orbit_critical m p₀ (by omega) hcrit n)
    (orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint n)
  exact (inv_le_inv₀ hcoeffPos hlimitPos).2
    (transportProductLimit_le_transportCoeff m p₀ (by omega) hcrit hdefect n)

end

end DerridaRetaux
