import DerridaRetaux.Rigidity.ModelVolterraProperties

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

theorem tendsto_mul_modelStringEntranceSolutionDeriv_atBot
    {d p : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) :
    Tendsto (fun x : ℝ ↦ x * modelStringEntranceSolutionDeriv d p x)
      atBot (𝓝 0) := by
  have hphi := tendsto_modelStringEntranceSolution_atBot hd hp
  have hinner := tendsto_modelStringExponent_atBot d p
  have hexpPos : Tendsto (fun x : ℝ ↦ Real.exp (d * p / (2 * x)))
      atBot (𝓝 1) := Real.tendsto_exp_nhds_zero_nhds_one.comp hinner
  have hexpNeg : Tendsto (fun x : ℝ ↦ Real.exp (-(d * p / (2 * x))))
      atBot (𝓝 1) := by
    apply Real.tendsto_exp_nhds_zero_nhds_one.comp
    simpa using hinner.neg
  have havg : Tendsto
      (fun x : ℝ ↦
        (Real.exp (d * p / (2 * x)) + Real.exp (-(d * p / (2 * x)))) / 2)
      atBot (𝓝 1) := by
    convert (hexpPos.add hexpNeg).div_const 2 using 1 <;> ring
  have hdiff : Tendsto
      (fun x : ℝ ↦ modelStringEntranceSolution d p x -
        (Real.exp (d * p / (2 * x)) + Real.exp (-(d * p / (2 * x)))) / 2)
      atBot (𝓝 0) := by
    simpa using hphi.sub havg
  apply hdiff.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  simp only [modelStringEntranceSolutionDeriv, modelStringEntranceSolution,
    if_neg hx.ne]
  field_simp [hd, hp, hx.ne]
  ring

/-- A primitive whose derivative is the weighted model Volterra integrand. -/
def modelVolterraPrimitive (d p xi x : ℝ) : ℝ :=
  (xi - x) * modelStringEntranceSolutionDeriv d p x +
    modelStringEntranceSolution d p x

theorem hasDerivAt_modelVolterraPrimitive
    {d p xi x : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) (hx : x < 0) :
    HasDerivAt (modelVolterraPrimitive d p xi)
      ((xi - x) * modelStringEntranceSolutionSecond d p x) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ xi - y) (-1) x := by
    convert (hasDerivAt_const x xi).sub (hasDerivAt_id x) using 1 <;> ring
  have hfirst := hlin.mul (hasDerivAt_modelStringEntranceSolutionDeriv
    hd hp (ne_of_lt hx))
  have hsecond := hasDerivAt_modelStringEntranceSolution hd hp (ne_of_lt hx)
  change HasDerivAt
    (fun y : ℝ ↦ (xi - y) * modelStringEntranceSolutionDeriv d p y +
      modelStringEntranceSolution d p y)
    ((xi - x) * modelStringEntranceSolutionSecond d p x) x
  exact (hfirst.add hsecond).congr_deriv (by ring)

theorem tendsto_modelVolterraPrimitive_atBot
    {d p xi : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) :
    Tendsto (modelVolterraPrimitive d p xi) atBot (𝓝 1) := by
  have hderiv := tendsto_modelStringEntranceSolutionDeriv_atBot hd hp
  have hxderiv := tendsto_mul_modelStringEntranceSolutionDeriv_atBot hd hp
  have hweighted : Tendsto
      (fun x : ℝ ↦ (xi - x) * modelStringEntranceSolutionDeriv d p x)
      atBot (𝓝 0) := by
    convert (hderiv.const_mul xi).sub hxderiv using 1
    · funext x
      ring
    · ring
  change Tendsto
    (fun x : ℝ ↦ (xi - x) * modelStringEntranceSolutionDeriv d p x +
      modelStringEntranceSolution d p x) atBot (𝓝 1)
  convert hweighted.add (tendsto_modelStringEntranceSolution_atBot hd hp) using 1 <;> ring

theorem modelVolterraPrimitive_deriv_nonneg
    {d p xi x : ℝ} (hd : 0 < d) (hp : 0 < p)
    (hx : x ≤ xi) (hxi : xi < 0) :
    0 ≤ (xi - x) * modelStringEntranceSolutionSecond d p x := by
  have hx0 : x < 0 := lt_of_le_of_lt hx hxi
  rw [modelStringEntranceSolution_ode hd.ne' hp.ne' hx0]
  exact mul_nonneg (sub_nonneg.mpr hx)
    (mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg p) (by norm_num))
      (modelStringDensity_nonneg d x))
      (modelStringEntranceSolution_pos hd hp hx0).le)

end

end DerridaRetaux
