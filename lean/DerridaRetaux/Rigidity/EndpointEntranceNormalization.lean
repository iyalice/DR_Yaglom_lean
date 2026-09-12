import DerridaRetaux.Rigidity.EndpointReductionAsymptotics

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Reduction of order turns an endpoint-normalized positive solution whose
slope tends to `-1` into an entrance-normalized solution. -/
theorem tendsto_entranceSolutionFromEndpoint_atBot_one
    {f f' : ℝ → ℝ} {h : ℝ}
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ x : ℝ, x < 0 → 0 < f x)
    (hlimit : Tendsto (fun x : ℝ ↦ f x + x) atBot (𝓝 h))
    (hfderiv : ∀ x : ℝ, x < 0 → HasDerivAt f (f' x) x)
    (hfprimeNeg : ∀ x : ℝ, x < 0 → f' x < 0)
    (hfprimeLimit : Tendsto f' atBot (𝓝 (-1))) :
    Tendsto (entranceSolutionFromEndpoint f) atBot (𝓝 1) := by
  have hfTop : Tendsto f atBot atTop := by
    have hsum := hlimit.add_atTop tendsto_neg_atBot_atTop
    convert hsum using 1
    funext x
    ring
  have hfinv : Tendsto (fun x : ℝ ↦ (f x)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hfTop
  have hred := tendsto_endpointReductionIntegral_atBot_zero
    hfcont hfpos hlimit
  have hderivRatio : Tendsto
      (fun x : ℝ ↦ ((f x) ^ 2)⁻¹ / (-f' x / f x ^ 2))
      atBot (𝓝 1) := by
    have hsimple : Tendsto (fun x : ℝ ↦ (-1 : ℝ) / f' x)
        atBot (𝓝 1) := by
      convert tendsto_const_nhds.div hfprimeLimit (by norm_num) using 1 <;> norm_num
    apply hsimple.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    field_simp [ne_of_gt (hfpos x hx), (hfprimeNeg x hx).ne]
  have hlhop := HasDerivAt.lhopital_zero_atBot_on_Iio
    (a := 0)
    (f := endpointReductionIntegral f)
    (f' := fun x : ℝ ↦ ((f x) ^ 2)⁻¹)
    (g := fun x : ℝ ↦ (f x)⁻¹)
    (g' := fun x : ℝ ↦ -f' x / f x ^ 2)
    (l := 𝓝 1)
    (fun x hx ↦ hasDerivAt_endpointReductionIntegral hx hfcont hfpos hlimit)
    (fun x hx ↦ (hfderiv x hx).inv (ne_of_gt (hfpos x hx)))
    (fun x hx ↦ div_ne_zero (neg_ne_zero.mpr (hfprimeNeg x hx).ne)
      (pow_ne_zero 2 (ne_of_gt (hfpos x hx))))
    hred hfinv hderivRatio
  apply hlhop.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  unfold entranceSolutionFromEndpoint
  field_simp [ne_of_gt (hfpos x hx)]
  ring

end

end DerridaRetaux
