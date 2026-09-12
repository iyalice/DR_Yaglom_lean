import DerridaRetaux.Rigidity.ModelEndpointProperties
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-!
# The entrance-normalized solution for the explicit model string

For `d,p > 0`, the normalized solution of the model ODE is the symmetric
combination of the two elementary exponential solutions.  This file proves its
normalization and differential equation; the Volterra integral identity is kept as
a separate next obligation.
-/

/-- Explicit entrance-normalized candidate for the model string. -/
def modelStringEntranceSolution (d p x : ℝ) : ℝ :=
  if x = 0 then 1 else
    x / (d * p) *
      (Real.exp (d * p / (2 * x)) - Real.exp (-(d * p / (2 * x))))

/-- Explicit first derivative of `modelStringEntranceSolution` away from zero. -/
def modelStringEntranceSolutionDeriv (d p x : ℝ) : ℝ :=
  (Real.exp (d * p / (2 * x)) - Real.exp (-(d * p / (2 * x)))) /
      (d * p) -
    (Real.exp (d * p / (2 * x)) + Real.exp (-(d * p / (2 * x)))) /
      (2 * x)

/-- Explicit second derivative of `modelStringEntranceSolution` away from zero. -/
def modelStringEntranceSolutionSecond (d p x : ℝ) : ℝ :=
  d * p *
    (Real.exp (d * p / (2 * x)) - Real.exp (-(d * p / (2 * x)))) /
      (4 * x ^ 3)

theorem hasDerivAt_modelStringEntranceSolution
    {d p x : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (modelStringEntranceSolution d p)
      (modelStringEntranceSolutionDeriv d p x) x := by
  have hinner := hasDerivAt_modelStringExponent d p hx
  have hexpPos := (Real.hasDerivAt_exp _).comp x hinner
  have hexpNeg := (Real.hasDerivAt_exp _).comp x hinner.neg
  have hdiff := hexpPos.sub hexpNeg
  have hproduct := (hasDerivAt_id x).div_const (d * p) |>.mul hdiff
  have hraw : HasDerivAt
      (fun y : ℝ ↦ y / (d * p) *
        (Real.exp (d * p / (2 * y)) - Real.exp (-(d * p / (2 * y)))))
      (modelStringEntranceSolutionDeriv d p x) x := by
    convert hproduct using 1
    simp only [modelStringEntranceSolutionDeriv, Function.comp_apply]
    field_simp [hd, hp, hx]
    ring
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp only [modelStringEntranceSolution, if_neg hy]

theorem hasDerivAt_modelStringEntranceSolutionDeriv
    {d p x : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (modelStringEntranceSolutionDeriv d p)
      (modelStringEntranceSolutionSecond d p x) x := by
  have hinner := hasDerivAt_modelStringExponent d p hx
  have hexpPos := (Real.hasDerivAt_exp _).comp x hinner
  have hexpNeg := (Real.hasDerivAt_exp _).comp x hinner.neg
  have hdiff := hexpPos.sub hexpNeg
  have hsum := hexpPos.add hexpNeg
  have hfirst := hdiff.div_const (d * p)
  have hden : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 x := by
    convert (hasDerivAt_const x 2).mul (hasDerivAt_id x) using 1 <;> ring
  have hsecond := hsum.div hden (mul_ne_zero (by norm_num) hx)
  have hresult := hfirst.sub hsecond
  convert hresult using 1
  simp only [modelStringEntranceSolutionDeriv, modelStringEntranceSolutionSecond]
  field_simp [hd, hp, hx]
  ring

/-- The entrance-normalized candidate solves the same model string ODE as the
decreasing endpoint solution. -/
theorem modelStringEntranceSolution_ode
    {d p x : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) (hx : x < 0) :
    modelStringEntranceSolutionSecond d p x =
      (p ^ 2 / 4) * modelStringDensity d x *
        modelStringEntranceSolution d p x := by
  rw [modelStringDensity_of_neg d hx]
  simp only [modelStringEntranceSolutionSecond, modelStringEntranceSolution,
    if_neg (ne_of_lt hx)]
  field_simp [hd, hp, ne_of_lt hx, ne_of_gt (neg_pos.mpr hx)]
  ring

theorem modelStringEntranceSolution_secondODE
    {d p x : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) (hx : x < 0) :
    HasDerivAt (modelStringEntranceSolutionDeriv d p)
      ((p ^ 2 / 4) * modelStringDensity d x *
        modelStringEntranceSolution d p x) x := by
  rw [← modelStringEntranceSolution_ode hd hp hx]
  exact hasDerivAt_modelStringEntranceSolutionDeriv hd hp (ne_of_lt hx)

/-- Entrance normalization `phi(-∞)=1` for the explicit model solution. -/
theorem tendsto_modelStringEntranceSolution_atBot
    {d p : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) :
    Tendsto (modelStringEntranceSolution d p) atBot (𝓝 1) := by
  let z : ℝ → ℝ := fun x ↦ d * p / (2 * x)
  have hz : Tendsto z atBot (𝓝 0) := by
    simpa only [z] using tendsto_modelStringExponent_atBot d p
  have hzNe : Tendsto z atBot (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_inf.2 ⟨hz, ?_⟩
    rw [tendsto_principal]
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    exact div_ne_zero (mul_ne_zero hd hp)
      (mul_ne_zero (by norm_num) hx.ne)
  have hnegz : Tendsto (fun x ↦ -z x) atBot (𝓝 0) := by
    simpa using hz.neg
  have hnegzNe : Tendsto (fun x ↦ -z x) atBot (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_inf.2 ⟨hnegz, ?_⟩
    rw [tendsto_principal]
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hd hp)
      (mul_ne_zero (by norm_num) hx.ne))
  have hplus := (Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hzNe
  have hminus := (Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hnegzNe
  have havg : Tendsto
      (fun x ↦ (1 / 2 : ℝ) *
        (z x)⁻¹ * (Real.exp (z x) - 1) +
        (1 / 2 : ℝ) *
          (-z x)⁻¹ * (Real.exp (-z x) - 1))
      atBot (𝓝 1) := by
    convert (hplus.const_mul (1 / 2 : ℝ)).add
      (hminus.const_mul (1 / 2 : ℝ)) using 1
    · funext x
      simp only [Function.comp_apply, smul_eq_mul, zero_add, Real.exp_zero]
      ring
    · norm_num
  apply havg.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  simp only [modelStringEntranceSolution, if_neg hx.ne, z]
  field_simp [hd, hp, hx.ne]
  ring

/-- The model entrance solution is positive on the negative half-line. -/
theorem modelStringEntranceSolution_pos
    {d p x : ℝ} (hd : 0 < d) (hp : 0 < p) (hx : x < 0) :
    0 < modelStringEntranceSolution d p x := by
  have hratio : d * p / (2 * x) < 0 :=
    div_neg_of_pos_of_neg (mul_pos hd hp)
      (mul_neg_of_pos_of_neg (by norm_num) hx)
  have hexp :
      Real.exp (d * p / (2 * x)) <
        Real.exp (-(d * p / (2 * x))) :=
    Real.exp_lt_exp.mpr (by linarith)
  rw [modelStringEntranceSolution, if_neg hx.ne]
  exact mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos hx (mul_pos hd hp)) (sub_neg.mpr hexp)

end

end DerridaRetaux
