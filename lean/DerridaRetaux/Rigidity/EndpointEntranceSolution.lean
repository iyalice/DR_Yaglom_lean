import DerridaRetaux.Rigidity.EndpointEntranceNormalization

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The natural first derivative of the reduction-of-order entrance solution. -/
def entranceSolutionFromEndpointSlope
    (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  f' x * endpointReductionIntegral f x + (f x)⁻¹

theorem endpointReductionIntegral_pos
    {f : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h)) :
    0 < endpointReductionIntegral f x := by
  let a : ℝ := x - 1
  let g : ℝ → ℝ := fun y ↦ ((f y) ^ 2)⁻¹
  have hax : a < x := by dsimp only [a]; linarith
  have ha0 : a < 0 := hax.trans hx
  have haInt : IntegrableOn g (Iic a) :=
    integrableOn_inv_sq_endpoint ha0 hfcont hfpos hlimit
  have hxInt : IntegrableOn g (Iic x) :=
    integrableOn_inv_sq_endpoint hx hfcont hfpos hlimit
  have hgcont : ContinuousOn g (Icc a x) := by
    have hfI : ContinuousOn f (Icc a x) :=
      hfcont.mono fun y hy ↦ hy.2.trans_lt hx
    exact (hfI.pow 2).inv₀ fun y hy ↦
      pow_ne_zero 2 (ne_of_gt (hfpos y (hy.2.trans_lt hx)))
  have hinter : 0 < ∫ y in a..x, g y := by
    apply intervalIntegral.integral_pos hax hgcont
    · intro y hy
      exact inv_nonneg.mpr (sq_nonneg _)
    · refine ⟨x, ⟨hax.le, le_rfl⟩, ?_⟩
      exact inv_pos.mpr (sq_pos_of_pos (hfpos x hx))
  have hleft : 0 ≤ ∫ y in Iic a, g y := by
    apply integral_nonneg_of_ae
    filter_upwards with y
    exact inv_nonneg.mpr (sq_nonneg _)
  have hdiff := intervalIntegral.integral_Iic_sub_Iic haInt hxInt
  dsimp only [g] at hdiff ⊢
  unfold endpointReductionIntegral
  linarith

theorem entranceSolutionFromEndpoint_pos
    {f : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h)) :
    0 < entranceSolutionFromEndpoint f x := by
  exact mul_pos (hfpos x hx)
    (endpointReductionIntegral_pos hx hfcont hfpos hlimit)

theorem hasDerivAt_entranceSolutionFromEndpoint
    {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : HasDerivAt f (f' x) x) :
    HasDerivAt (entranceSolutionFromEndpoint f)
      (entranceSolutionFromEndpointSlope f f' x) x := by
  have hI := hasDerivAt_endpointReductionIntegral hx hfcont hfpos hlimit
  have hmul := hfderiv.mul hI
  convert hmul using 1
  unfold entranceSolutionFromEndpointSlope
  field_simp [ne_of_gt (hfpos x hx)]
  ring

/-- The cancellation in reduction of order leaves the same second-order
equation as the original endpoint solution. -/
theorem hasDerivAt_entranceSolutionFromEndpointSlope
    {f f' q : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : HasDerivAt f (f' x) x)
    (hfprimeDeriv : HasDerivAt f' (q x * f x) x) :
    HasDerivAt (entranceSolutionFromEndpointSlope f f')
      (q x * entranceSolutionFromEndpoint f x) x := by
  have hI := hasDerivAt_endpointReductionIntegral hx hfcont hfpos hlimit
  have hfirst := hfprimeDeriv.mul hI
  have hsecond := hfderiv.inv (ne_of_gt (hfpos x hx))
  have hsum := hfirst.add hsecond
  convert hsum using 1
  unfold entranceSolutionFromEndpoint
  field_simp [ne_of_gt (hfpos x hx)]
  ring

theorem continuousOn_entranceSolutionFromEndpoint
    {f f' : ℝ → ℝ} {h : ℝ}
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ x : ℝ, x < 0 → HasDerivAt f (f' x) x) :
    ContinuousOn (entranceSolutionFromEndpoint f) (Iio (0 : ℝ)) :=
  continuousOn_of_forall_continuousAt fun x hx ↦
    (hasDerivAt_entranceSolutionFromEndpoint hx hfcont hfpos hlimit
      (hfderiv x hx)).continuousAt

end

end DerridaRetaux
