import DerridaRetaux.Rigidity.EndpointEntranceLowerBound

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

def endpointRatioExtension (f phi : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < 0 then f x / phi x else 0

theorem tendsto_endpoint_ratio_nhdsLT_zero
    {f f' : ℝ → ℝ} {h : ℝ}
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ y : ℝ, y < 0 → HasDerivAt f (f' y) y)
    (hfprimeNeg : ∀ y : ℝ, y < 0 → f' y < 0)
    (hfprimeMono : MonotoneOn f' (Iio (0 : ℝ)))
    (hfprimeLimit : Tendsto f' atBot (𝓝 (-1)))
    (hfend : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun x : ℝ ↦ f x / entranceSolutionFromEndpoint f x)
      (𝓝[<] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero' _ _ hfend
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_nonneg (hfpos x hx).le
      (entranceSolutionFromEndpoint_pos hx hfcont hfpos hlimit).le
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_le_self (hfpos x hx).le
      (one_le_entranceSolutionFromEndpoint hx hfcont hfpos hlimit
        hfderiv hfprimeNeg hfprimeMono hfprimeLimit)

theorem endpointEntrance_wronskian
    {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h)) :
    f' x * entranceSolutionFromEndpoint f x -
        f x * entranceSolutionFromEndpointSlope f f' x = -1 := by
  unfold entranceSolutionFromEndpoint entranceSolutionFromEndpointSlope
  field_simp [ne_of_gt (hfpos x hx)]
  ring

theorem hasDerivAt_endpoint_ratio
    {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : HasDerivAt f (f' x) x) :
    HasDerivAt
      (fun y : ℝ ↦ f y / entranceSolutionFromEndpoint f y)
      (-((entranceSolutionFromEndpoint f x) ^ 2)⁻¹) x := by
  have hphi := hasDerivAt_entranceSolutionFromEndpoint
    hx hfcont hfpos hlimit hfderiv
  have hdiv := hfderiv.div hphi
    (ne_of_gt (entranceSolutionFromEndpoint_pos hx hfcont hfpos hlimit))
  convert hdiv using 1
  rw [endpointEntrance_wronskian hx hfcont hfpos hlimit]
  ring

theorem continuousOn_endpointRatioExtension
    {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ y : ℝ, y < 0 → HasDerivAt f (f' y) y)
    (hfprimeNeg : ∀ y : ℝ, y < 0 → f' y < 0)
    (hfprimeMono : MonotoneOn f' (Iio (0 : ℝ)))
    (hfprimeLimit : Tendsto f' atBot (𝓝 (-1)))
    (hfend : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 0)) :
    ContinuousOn
      (endpointRatioExtension f (entranceSolutionFromEndpoint f)) (Icc x 0) := by
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    change Tendsto (endpointRatioExtension f (entranceSolutionFromEndpoint f))
      (nhdsWithin 0 (Icc x 0))
      (𝓝 (endpointRatioExtension f (entranceSolutionFromEndpoint f) 0))
    rw [show endpointRatioExtension f (entranceSolutionFromEndpoint f) 0 = 0 by simp [endpointRatioExtension]]
    have hratio := tendsto_endpoint_ratio_nhdsLT_zero hfcont hfpos hlimit
      hfderiv hfprimeNeg hfprimeMono hfprimeLimit hfend
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Metric.tendsto_nhds] at hratio
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hratio ε hε)
      with ⟨s, hs, hsub⟩
    change {z : ℝ | dist (endpointRatioExtension f (entranceSolutionFromEndpoint f) z) 0 < ε} ∈ nhdsWithin 0 (Icc x 0)
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨s, hs, ?_⟩
    intro z hz
    by_cases hz0 : z = 0
    · subst z; simpa [endpointRatioExtension] using hε
    · have hzneg : z < 0 := lt_of_le_of_ne hz.2.2 hz0
      change dist (if z < 0 then f z / entranceSolutionFromEndpoint f z else 0) 0 < ε
      rw [if_pos hzneg]
      exact hsub ⟨hz.1, hzneg⟩
  · have hyneg : y < 0 := lt_of_le_of_ne hy.2 hy0
    have hfAt : ContinuousAt f y :=
      hfcont.continuousAt (isOpen_Iio.mem_nhds hyneg)
    have hphiAt : ContinuousAt (entranceSolutionFromEndpoint f) y :=
      (hasDerivAt_entranceSolutionFromEndpoint hyneg hfcont hfpos hlimit
        (hfderiv y hyneg)).continuousAt
    have hquot : ContinuousAt
        (fun z : ℝ ↦ f z / entranceSolutionFromEndpoint f z) y :=
      hfAt.div hphiAt
        (ne_of_gt (entranceSolutionFromEndpoint_pos hyneg hfcont hfpos hlimit))
    apply ContinuousAt.continuousWithinAt
    apply hquot.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hyneg] with z hz
    have hzneg : z < 0 := hz
    simp [endpointRatioExtension, hzneg]

/-- The decreasing endpoint solution is represented by the normalized
reduction-of-order solution and its inverse-square integral to the right end. -/
theorem endpoint_reduction_representation
    {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ y : ℝ, y < 0 → HasDerivAt f (f' y) y)
    (hfprimeNeg : ∀ y : ℝ, y < 0 → f' y < 0)
    (hfprimeMono : MonotoneOn f' (Iio (0 : ℝ)))
    (hfprimeLimit : Tendsto f' atBot (𝓝 (-1)))
    (hfend : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 0)) :
    f x = entranceSolutionFromEndpoint f x *
      ∫ y in x..0, ((entranceSolutionFromEndpoint f y) ^ 2)⁻¹ := by
  let phi := entranceSolutionFromEndpoint f
  let r := endpointRatioExtension f phi
  have hrcont : ContinuousOn r (Icc x 0) :=
    continuousOn_endpointRatioExtension hx hfcont hfpos hlimit hfderiv
      hfprimeNeg hfprimeMono hfprimeLimit hfend
  have hderiv : ∀ y ∈ Ioo x 0,
      HasDerivAt (fun z : ℝ ↦ -r z) ((phi y) ^ 2)⁻¹ y := by
    intro y hy
    have hratio := hasDerivAt_endpoint_ratio hy.2 hfcont hfpos hlimit
      (hfderiv y hy.2)
    have heq : (fun z : ℝ ↦ r z) =ᶠ[𝓝 y]
        (fun z : ℝ ↦ f z / phi z) := by
      filter_upwards [Iio_mem_nhds hy.2] with z hz
      have hzneg : z < 0 := hz
      simp [r, endpointRatioExtension, hzneg]
    have hr := hratio.congr_of_eventuallyEq heq
    convert hr.neg using 1 <;> ring
  have hintOn : IntegrableOn (fun y : ℝ ↦ (phi y ^ 2)⁻¹) (Ioc x 0) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hrcont.neg hderiv
      (fun y hy ↦ inv_nonneg.mpr (sq_nonneg _))
  have hint : IntervalIntegrable (fun y : ℝ ↦ (phi y ^ 2)⁻¹) volume x 0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).2 hintOn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.le
    hrcont.neg hderiv hint
  have hrx : r x = f x / phi x := by simp [r, endpointRatioExtension, hx]
  have hrzero : r 0 = 0 := by simp [r, endpointRatioExtension]
  dsimp only [phi] at hint hftc hrx ⊢
  rw [hrzero, hrx] at hftc
  have hphiPos := entranceSolutionFromEndpoint_pos hx hfcont hfpos hlimit
  rw [hftc]
  field_simp [hphiPos.ne']

end

end DerridaRetaux
