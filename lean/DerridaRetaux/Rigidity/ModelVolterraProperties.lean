import DerridaRetaux.Rigidity.ModelVolterra

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The explicit model entrance solution is continuous on the negative half-line. -/
theorem continuousOn_modelStringEntranceSolution
    {d p : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) :
    ContinuousOn (modelStringEntranceSolution d p) (Iio 0) := by
  exact continuousOn_of_forall_continuousAt fun x hx ↦
    (hasDerivAt_modelStringEntranceSolution hd hp (ne_of_lt hx)).continuousAt

/-- The derivative of the entrance-normalized model solution vanishes at the
left endpoint. -/
theorem tendsto_modelStringEntranceSolutionDeriv_atBot
    {d p : ℝ} (hd : d ≠ 0) (hp : p ≠ 0) :
    Tendsto (modelStringEntranceSolutionDeriv d p) atBot (𝓝 0) := by
  have hinner := tendsto_modelStringExponent_atBot d p
  have hexpPos : Tendsto (fun x : ℝ ↦ Real.exp (d * p / (2 * x)))
      atBot (𝓝 1) := Real.tendsto_exp_nhds_zero_nhds_one.comp hinner
  have hexpNeg : Tendsto (fun x : ℝ ↦ Real.exp (-(d * p / (2 * x))))
      atBot (𝓝 1) := by
    apply Real.tendsto_exp_nhds_zero_nhds_one.comp
    simpa using hinner.neg
  have hfirst : Tendsto
      (fun x : ℝ ↦
        (Real.exp (d * p / (2 * x)) - Real.exp (-(d * p / (2 * x)))) /
          (d * p)) atBot (𝓝 0) := by
    convert (hexpPos.sub hexpNeg).div_const (d * p) using 1 <;> ring
  have hinv : Tendsto (fun x : ℝ ↦ x⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atBot_zero
  have hsecond : Tendsto
      (fun x : ℝ ↦
        (Real.exp (d * p / (2 * x)) + Real.exp (-(d * p / (2 * x)))) /
          (2 * x)) atBot (𝓝 0) := by
    have hhalf : Tendsto
        (fun x : ℝ ↦ (1 / 2 : ℝ) *
          (Real.exp (d * p / (2 * x)) + Real.exp (-(d * p / (2 * x)))))
        atBot (𝓝 1) := by
      convert (hexpPos.add hexpNeg).const_mul (1 / 2 : ℝ) using 1 <;> ring
    convert hhalf.mul hinv using 1
    · funext x
      field_simp
    · ring
  simpa [modelStringEntranceSolutionDeriv] using hfirst.sub hsecond

end

end DerridaRetaux
