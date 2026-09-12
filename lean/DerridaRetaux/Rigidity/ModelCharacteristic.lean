import DerridaRetaux.Rigidity.ModelVolterraEquation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

theorem modelStringEntranceSolution_eq_sinh_div
    {d p x : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) (hx : x ≠ 0) :
    modelStringEntranceSolution d p x =
      Real.sinh (d * p / (2 * x)) / (d * p / (2 * x)) := by
  rw [modelStringEntranceSolution, if_neg hx]
  rw [Real.sinh_eq]
  field_simp [hd, hp, hx]
  ring

theorem one_le_modelStringEntranceSolution
    {d p x : ℝ} (hd : 0 < d) (hp : 0 < p) (hx : x < 0) :
    1 ≤ modelStringEntranceSolution d p x := by
  let z := d * p / (2 * x)
  have hz : z < 0 := by
    dsimp only [z]
    exact div_neg_of_pos_of_neg (mul_pos hd hp)
      (mul_neg_of_pos_of_neg (by norm_num) hx)
  rw [modelStringEntranceSolution_eq_sinh_div hd.ne' hp.ne' hx.ne]
  change 1 ≤ Real.sinh z / z
  exact (le_div_iff_of_neg hz).2 (by simpa using (Real.sinh_le_self_iff).2 hz.le)

theorem measurable_modelStringEntranceSolution (d p : ℝ) :
    Measurable (modelStringEntranceSolution d p) := by
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · fun_prop

theorem intervalIntegrable_inv_sq_modelStringEntranceSolution
    {d p xi : ℝ} (hd : 0 < d) (hp : 0 < p) (hxi : xi < 0) :
    IntervalIntegrable
      (fun x : ℝ ↦ ((modelStringEntranceSolution d p x) ^ 2)⁻¹)
      volume xi 0 := by
  rw [intervalIntegrable_iff, uIoc_of_le hxi.le]
  have hone : IntegrableOn (fun _x : ℝ ↦ (1 : ℝ)) (Ioc xi 0) volume := by
    rw [integrableOn_const]
    exact Or.inr (measure_Ioc_lt_top)
  apply Integrable.mono' hone
  · exact ((measurable_modelStringEntranceSolution d p).pow_const 2).inv.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    by_cases hx0 : x = 0
    · simp [hx0, modelStringEntranceSolution]
    · have hxneg : x < 0 := lt_of_le_of_ne hx.2 hx0
      have hphi := one_le_modelStringEntranceSolution hd hp hxneg
      exact (inv_le_one₀ (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hphi))).2
        (by nlinarith)

/-- Quotient of the endpoint solution by the entrance-normalized solution. -/
def modelReductionRatio (d p x : ℝ) : ℝ :=
  modelStringEndpointSolution d p x / modelStringEntranceSolution d p x

theorem modelString_wronskian
    {d p x : ℝ} (hd : 0 < d) (hp : 0 < p) (hx : x < 0) :
    modelStringEndpointSolutionDeriv d p x * modelStringEntranceSolution d p x -
      modelStringEndpointSolution d p x * modelStringEntranceSolutionDeriv d p x = -1 := by
  simp only [modelStringEndpointSolutionDeriv, modelStringEndpointSolution,
    modelStringEntranceSolutionDeriv, modelStringEntranceSolution, if_neg hx.ne]
  field_simp [hd, hp, hx.ne, Real.exp_ne_zero]
  have hexp : Real.exp (d * p / (2 * x)) *
      Real.exp (-(d * p / (2 * x))) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  ring_nf at hexp ⊢
  linear_combination -(d ^ 2 * p ^ 2 * x ^ 2 * 4) * hexp
theorem hasDerivAt_modelReductionRatio
    {d p x : ℝ} (hd : 0 < d) (hp : 0 < p) (hx : x < 0) :
    HasDerivAt (modelReductionRatio d p)
      (-((modelStringEntranceSolution d p x) ^ 2)⁻¹) x := by
  have hphiPos := modelStringEntranceSolution_pos
    (hd)
    (hp) hx
  have hquot := (hasDerivAt_modelStringEndpointSolution d p hx.ne).div
    (hasDerivAt_modelStringEntranceSolution hd.ne' hp.ne' hx.ne) hphiPos.ne'
  change HasDerivAt
    (fun y : ℝ ↦ modelStringEndpointSolution d p y /
      modelStringEntranceSolution d p y)
    (-((modelStringEntranceSolution d p x) ^ 2)⁻¹) x
  apply hquot.congr_deriv
  rw [div_eq_iff (pow_ne_zero 2 hphiPos.ne')]
  rw [modelString_wronskian hd hp hx]
  field_simp [hphiPos.ne']

end

end DerridaRetaux
