import DerridaRetaux.Rigidity.EndpointReductionDerivative
import Mathlib.Analysis.Calculus.LHopital

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The left-tail reduction integral vanishes at the entrance. -/
theorem tendsto_endpointReductionIntegral_atBot_zero
    {f : ℝ → ℝ} {h : ℝ}
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h)) :
    Tendsto (endpointReductionIntegral f) atBot (𝓝 0) := by
  let a : ℝ := -1
  let g : ℝ → ℝ := fun y ↦ ((f y) ^ 2)⁻¹
  have ha : a < 0 := by norm_num [a]
  have haInt : IntegrableOn g (Iic a) :=
    integrableOn_inv_sq_endpoint ha hfcont hfpos hlimit
  have hinter : Tendsto (fun x : ℝ ↦ ∫ y in x..a, g y) atBot
      (𝓝 (∫ y in Iic a, g y)) :=
    intervalIntegral_tendsto_integral_Iic a haInt tendsto_id
  have hzero : Tendsto
      (fun x : ℝ ↦ (∫ y in Iic a, g y) - ∫ y in x..a, g y)
      atBot (𝓝 0) := by
    convert tendsto_const_nhds.sub hinter using 1 <;> ring
  apply hzero.congr'
  filter_upwards [Iic_mem_atBot a] with x hx
  have hx0 : x < 0 := hx.trans_lt ha
  have hxInt : IntegrableOn g (Iic x) :=
    integrableOn_inv_sq_endpoint hx0 hfcont hfpos hlimit
  have hdiff := intervalIntegral.integral_Iic_sub_Iic hxInt haInt
  dsimp only [g] at hdiff ⊢
  unfold endpointReductionIntegral
  linarith

end

end DerridaRetaux
