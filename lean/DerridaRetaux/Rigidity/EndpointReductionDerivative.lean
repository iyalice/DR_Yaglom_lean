import DerridaRetaux.Rigidity.EndpointReductionIntegral

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The improper reduction integral differentiates with respect to its finite
upper endpoint. -/
theorem hasDerivAt_endpointReductionIntegral
    {f : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h)) :
    HasDerivAt (endpointReductionIntegral f) ((f x) ^ 2)⁻¹ x := by
  let g : ℝ → ℝ := fun y ↦ ((f y) ^ 2)⁻¹
  have hgOn : ContinuousOn g (Iio (0 : ℝ)) := (hfcont.pow 2).inv₀ fun y hy ↦ pow_ne_zero 2 (ne_of_gt (hfpos y hy))
  have hgcont : ContinuousAt g x := by
    have hfAt : ContinuousAt f x :=
      hfcont.continuousAt (isOpen_Iio.mem_nhds hx)
    exact (hfAt.pow 2).inv₀ (pow_ne_zero 2 (hfpos x hx).ne')
  have hbase : HasDerivAt (fun u : ℝ ↦ ∫ y in x..u, g y) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (by rw [intervalIntegrable_iff]; simp)
      (hgOn.stronglyMeasurableAtFilter isOpen_Iio x hx) hgcont
  have hmodel : HasDerivAt
      (fun u : ℝ ↦ endpointReductionIntegral f x + ∫ y in x..u, g y)
      (g x) x := hbase.const_add _
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with u hu
  have hxInt : IntegrableOn g (Iic x) :=
    integrableOn_inv_sq_endpoint hx hfcont hfpos hlimit
  have huInt : IntegrableOn g (Iic u) :=
    integrableOn_inv_sq_endpoint hu hfcont hfpos hlimit
  have hdiff := intervalIntegral.integral_Iic_sub_Iic hxInt huInt
  dsimp only [g] at hdiff ⊢
  unfold endpointReductionIntegral
  linarith

end

end DerridaRetaux
