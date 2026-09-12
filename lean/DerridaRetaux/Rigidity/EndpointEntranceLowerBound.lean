import DerridaRetaux.Rigidity.EndpointEntranceMonotonicity

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

theorem monotoneOn_entranceSolutionFromEndpoint
    {f f' : ℝ → ℝ} {h : ℝ}
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ y : ℝ, y < 0 → HasDerivAt f (f' y) y)
    (hfprimeNeg : ∀ y : ℝ, y < 0 → f' y < 0)
    (hfprimeMono : MonotoneOn f' (Iio (0 : ℝ))) :
    MonotoneOn (entranceSolutionFromEndpoint f) (Iio (0 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iio 0)
    (continuousOn_entranceSolutionFromEndpoint hfcont hfpos hlimit hfderiv)
  · intro x hx
    rw [interior_Iio] at hx
    exact (hasDerivAt_entranceSolutionFromEndpoint hx hfcont hfpos hlimit
      (hfderiv x hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    rw [(hasDerivAt_entranceSolutionFromEndpoint hx hfcont hfpos hlimit
      (hfderiv x hx)).deriv]
    exact entranceSolutionFromEndpointSlope_nonneg hx hfcont hfpos hlimit
      hfderiv hfprimeNeg hfprimeMono

theorem one_le_entranceSolutionFromEndpoint
    {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ y : ℝ, y < 0 → HasDerivAt f (f' y) y)
    (hfprimeNeg : ∀ y : ℝ, y < 0 → f' y < 0)
    (hfprimeMono : MonotoneOn f' (Iio (0 : ℝ)))
    (hfprimeLimit : Tendsto f' atBot (𝓝 (-1))) :
    1 ≤ entranceSolutionFromEndpoint f x := by
  have hnorm := tendsto_entranceSolutionFromEndpoint_atBot_one
    hfcont hfpos hlimit hfderiv hfprimeNeg hfprimeLimit
  apply le_of_tendsto hnorm
  filter_upwards [Iic_mem_atBot x] with y hy
  exact monotoneOn_entranceSolutionFromEndpoint hfcont hfpos hlimit
    hfderiv hfprimeNeg hfprimeMono (hy.trans_lt hx) hx hy

end

end DerridaRetaux
