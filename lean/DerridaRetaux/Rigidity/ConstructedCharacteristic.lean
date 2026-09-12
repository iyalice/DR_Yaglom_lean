import DerridaRetaux.Rigidity.ConstructedStringVolterra

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The source ODE package constructs the singular characteristic of the
associated string without any additional primitive input. -/
theorem constructedEntranceString_hasSingularCharacteristic
    {κ c C p : ℝ} {A0 A2 A3 Z : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (hp : 0 < p)
    (hA2 : ∀ s : ℝ, 0 < s → HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s → HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s → c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hZ : ∀ s : ℝ, 0 < s → HasDerivAt Z
      (A0 s * Z s + (1 / 2 : ℝ) * (Z s ^ 2 - p ^ 2)) s)
    (hInt : ∀ s : ℝ, 0 < s → IntervalIntegrable Z volume 0 s)
    (hMeas : ∀ s : ℝ, 0 < s → StronglyMeasurableAtFilter Z (𝓝 s) volume)
    (hCont : ∀ s : ℝ, 0 < s → ContinuousAt Z s)
    (hZpos : ∀ s : ℝ, 0 < s → 0 < Z s)
    (hPhi : Tendsto (constructedPhi Z) (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hTime : Tendsto
      (fun t : ℝ ↦ constructedEndpointAtTime p (stringY κ A3) Z t +
        stringXi κ A2 A3 t)
      (𝓝[>] (0 : ℝ)) (𝓝 (-κ * p / 3)))
    (hEndpoint : Tendsto
      (constructedEndpointAtTime p (stringY κ A3) Z) atTop (𝓝 0)) :
    HasSingularCharacteristic (constructedEntranceString κ A2 A3)
      (-(p ^ 2 / 4)) (-κ * p / 3) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  let hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  let hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds
  let e := stringXiOrderIso κ A2 A3 hmono hbij
  let Y := stringY κ A3
  let f := constructedEndpointSolution p Y Z e
  let fp := constructedEndpointSlope Z e
  let rho := constructedStringLebesgueDensity κ A2 A3 hmono hbij
  let a : ℝ := p ^ 2 / 4
  have ha : 0 < a := by dsimp only [a]; positivity
  have hfpos : ∀ x : ℝ, x < 0 → 0 < f x := by
    intro x hx
    exact constructedEndpointSolution_pos_of_neg hmono hbij hp.ne'
      (fun t ht ↦ stringY_pos hκ (hA3pos t ht)) hZpos hx
  have hfderiv : ∀ x : ℝ, x < 0 → HasDerivAt f (fp x) x := by
    intro x hx
    let t := timeOfNegativeCoordinate e x
    have ht : 0 < t := timeOfNegativeCoordinate_pos e hx
    have hxt : stringXi κ A2 A3 t = x :=
      coordinateOrderIso_timeOfNegativeCoordinate
        (stringXi κ A2 A3) hmono hbij hx
    have hxi := hasDerivAt_stringXi κ A0 A2 A3
      (hA2 t ht) (hA3 t ht) (hA3pos t ht).ne'
    have hY := hasDerivAt_stringY κ A0 A3
      (hA3 t ht) (hA3pos t ht).ne'
    have hresult := hasDerivAt_constructedEndpointSolution_at
      p A0 Y Z (stringXi κ A2 A3) hmono hbij ht hp.ne'
        hxi (stringY_pos hκ (hA3pos t ht)).ne' hY
        (hZ t ht) (hInt t ht) (hMeas t ht) (hCont t ht)
    simpa only [f, fp, e, Y, hxt] using hresult
  have hfcont : ContinuousOn f (Iio (0 : ℝ)) :=
    continuousOn_of_forall_continuousAt fun x hx ↦
      (hfderiv x hx).continuousAt
  have hfpneg : ∀ x : ℝ, x < 0 → fp x < 0 := by
    intro x hx
    unfold fp constructedEndpointSlope
    exact neg_neg_of_pos (constructedPhi_pos Z _)
  have hfpderiv : ∀ x : ℝ, x < 0 →
      HasDerivAt fp (a * rho x * f x) x := by
    intro x hx
    let t := timeOfNegativeCoordinate e x
    have ht : 0 < t := timeOfNegativeCoordinate_pos e hx
    have hxt : stringXi κ A2 A3 t = x :=
      coordinateOrderIso_timeOfNegativeCoordinate
        (stringXi κ A2 A3) hmono hbij hx
    have hxi := hasDerivAt_stringXi κ A0 A2 A3
      (hA2 t ht) (hA3 t ht) (hA3pos t ht).ne'
    have hresult := hasDerivAt_constructedEndpointSlope_at
      p Y Z (stringXi κ A2 A3) hmono hbij ht hp.ne'
        hxi (stringY_pos hκ (hA3pos t ht)).ne'
        (hInt t ht) (hMeas t ht) (hCont t ht)
    simpa only [fp, f, rho, a, e, Y, hxt,
      constructedStringLebesgueDensity] using hresult
  have hfpmono : MonotoneOn fp (Iio (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iio 0)
    · exact continuousOn_of_forall_continuousAt fun x hx ↦
        (hfpderiv x hx).continuousAt
    · intro x hx
      rw [interior_Iio] at hx
      exact (hfpderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Iio] at hx
      rw [(hfpderiv x hx).deriv]
      exact mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) (hfpos x hx).le
  have hflimit : Tendsto (fun x : ℝ ↦ f x + x) atBot
      (𝓝 (-κ * p / 3)) := by
    simpa only [f, Y, e] using
      tendsto_constructedEndpointSolution_add_id_atBot_source hmono hbij hTime
  have hfplimit : Tendsto fp atBot (𝓝 (-1)) := by
    simpa only [fp, e] using tendsto_constructedEndpointSlope_atBot hmono hbij hPhi
  have hfend : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    simpa only [f, Y, e] using
      tendsto_constructedEndpointSolution_nhdsLT_zero p (stringY κ A3) Z e hEndpoint
  have hvolterra : IsEntranceNormalizedVolterraSolution
      (constructedEntranceString κ A2 A3) (-a)
      (entranceSolutionFromEndpoint f) :=
    entranceSolutionFromEndpoint_isVolterra_constructedString
      hκ hc hC ha hA2 hA3 hprodTop hbounds hmono hbij hfcont hfpos
        hflimit hfderiv hfpneg hfpmono hfplimit hfend hfpderiv
  have hrepr : ∀ x : ℝ, x < 0 →
      f x = entranceSolutionFromEndpoint f x *
        ∫ y in x..0, ((entranceSolutionFromEndpoint f y) ^ 2)⁻¹ := by
    intro x hx
    exact endpoint_reduction_representation hx hfcont hfpos hflimit hfderiv
      hfpneg hfpmono hfplimit hfend
  apply constructedEntranceString_hasSingularCharacteristic_of_representation
    hmono hbij hvolterra
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    simpa only [f, Y, e] using hrepr x hx
  · simpa only [f, Y, e] using hflimit

end

end DerridaRetaux
