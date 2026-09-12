import DerridaRetaux.Rigidity.CharacteristicReduction
import DerridaRetaux.Rigidity.ConstructedEndpointProperties
import DerridaRetaux.Rigidity.StringAdmissibility

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The inverse of the coordinate order isomorphism sends the entrance
`x → -∞` to positive time `t → 0+`. -/
theorem tendsto_timeOfNegativeCoordinate_atBot_nhdsGT_zero
    (e : Ioi (0 : ℝ) ≃o Iio (0 : ℝ)) :
    Tendsto (timeOfNegativeCoordinate e) atBot (𝓝[>] (0 : ℝ)) := by
  refine tendsto_inf.2 ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    let tε : Ioi (0 : ℝ) := ⟨ε / 2, half_pos hε⟩
    have het : (e tε : ℝ) < 0 := (e tε).property
    filter_upwards [Iic_mem_atBot (e tε : ℝ)] with x hx
    have hxle : x ≤ (e tε : ℝ) := hx
    have hxneg : x < 0 := hxle.trans_lt het
    have hsub : (⟨x, hxneg⟩ : Iio (0 : ℝ)) ≤ e tε := hxle
    have horder : e.symm ⟨x, hxneg⟩ ≤ tε := by
      simpa using e.symm.monotone hsub
    have horder' : (e.symm ⟨x, hxneg⟩ : ℝ) ≤ ε / 2 := horder
    rw [timeOfNegativeCoordinate_of_neg e hxneg, Real.dist_eq, sub_zero,
      abs_of_pos (e.symm ⟨x, hxneg⟩).property]
    linarith
  · rw [tendsto_principal]
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    exact timeOfNegativeCoordinate_pos e hx

/-- A time-coordinate entrance expansion transfers verbatim to the negative
spatial coordinate. -/
theorem tendsto_constructedEndpointSolution_add_id_atBot
    (p : ℝ) (Y Z f : ℝ → ℝ)
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    {h : ℝ}
    (hTime : Tendsto
      (fun t : ℝ ↦ constructedEndpointAtTime p Y Z t + f t)
      (𝓝[>] (0 : ℝ)) (𝓝 h)) :
    Tendsto
      (fun x : ℝ ↦ constructedEndpointSolution p Y Z
        (coordinateOrderIso f hmono hbij) x + x)
      atBot (𝓝 h) := by
  let e := coordinateOrderIso f hmono hbij
  have hcomp := hTime.comp (tendsto_timeOfNegativeCoordinate_atBot_nhdsGT_zero e)
  apply hcomp.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  rw [constructedEndpointSolution]
  exact congrArg (fun y : ℝ ↦ constructedEndpointAtTime p Y Z
    (timeOfNegativeCoordinate e x) + y)
    (coordinateOrderIso_timeOfNegativeCoordinate f hmono hbij hx)

/-- The final characteristic step needs only the canonical Volterra solution
and its reduction-of-order representation; the source entrance expansion then
supplies the value. -/
theorem constructedEntranceString_hasSingularCharacteristic_of_representation
    {κ p : ℝ} {A2 A3 Y Z f phi : ℝ → ℝ}
    (hmono : StrictMonoOn f (Ioi 0))
    (hbij : BijOn f (Ioi 0) (Iio 0))
    (hvolterra : IsEntranceNormalizedVolterraSolution
      (constructedEntranceString κ A2 A3) (-(p ^ 2 / 4)) phi)
    (hrepresentation : ∀ᶠ xi : ℝ in atBot,
      constructedEndpointSolution p Y Z (coordinateOrderIso f hmono hbij) xi =
        phi xi * ∫ v in xi..0, ((phi v) ^ 2)⁻¹)
    {h : ℝ}
    (hexpansion : Tendsto
      (fun xi : ℝ ↦ constructedEndpointSolution p Y Z
        (coordinateOrderIso f hmono hbij) xi + xi)
      atBot (𝓝 h)) :
    HasSingularCharacteristic (constructedEntranceString κ A2 A3)
      (-(p ^ 2 / 4)) h := by
  exact hasSingularCharacteristic_of_endpoint_representation hvolterra
    hrepresentation hexpansion

end

end DerridaRetaux
