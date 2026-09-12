import DerridaRetaux.Rigidity.ConstructedEndpointGlobal

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The time-side normalization `Phi(t,p) → 1` at zero is exactly the
spatial derivative normalization `f'_p(ξ) → -1` at the entrance. -/
theorem tendsto_constructedEndpointSlope_atBot
    {Z f : ℝ → ℝ}
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    (hPhi : Tendsto (constructedPhi Z) (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto
      (constructedEndpointSlope Z (coordinateOrderIso f hmono hbij))
      atBot (𝓝 (-1)) := by
  have hcomp := hPhi.comp
    (tendsto_timeOfNegativeCoordinate_atBot_nhdsGT_zero
      (coordinateOrderIso f hmono hbij))
  simpa only [constructedEndpointSlope] using hcomp.neg

/-- Source-normalized spatial entrance expansion obtained from the already
proved time-coordinate expansion. -/
theorem tendsto_constructedEndpointSolution_add_id_atBot_source
    {κ p : ℝ} {A2 A3 Y Z : ℝ → ℝ}
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    (hTime : Tendsto
      (fun t : ℝ ↦ constructedEndpointAtTime p Y Z t +
        stringXi κ A2 A3 t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-κ * p / 3))) :
    Tendsto
      (fun x : ℝ ↦ constructedEndpointSolution p Y Z
        (coordinateOrderIso (stringXi κ A2 A3) hmono hbij) x + x)
      atBot (𝓝 (-κ * p / 3)) :=
  tendsto_constructedEndpointSolution_add_id_atBot
    p Y Z (stringXi κ A2 A3) hmono hbij hTime

end

end DerridaRetaux
