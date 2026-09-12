import DerridaRetaux.Rigidity.EndpointEntranceSolution

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

theorem tendsto_inv_endpoint_atBot_zero
    {f : ℝ → ℝ} {h : ℝ}
    (hlimit : Tendsto (fun x : ℝ ↦ f x + x) atBot (𝓝 h)) :
    Tendsto (fun x : ℝ ↦ (f x)⁻¹) atBot (𝓝 0) := by
  have hfTop : Tendsto f atBot atTop := by
    have hsum := hlimit.add_atTop tendsto_neg_atBot_atTop
    convert hsum using 1
    funext x
    ring
  exact tendsto_inv_atTop_zero.comp hfTop

/-- Improper FTC for the reciprocal of a positive decreasing endpoint
solution. -/
theorem integral_Iic_neg_endpointSlope_div_sq
    {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ y : ℝ, y < 0 → HasDerivAt f (f' y) y)
    (hfprimeNeg : ∀ y : ℝ, y < 0 → f' y < 0) :
    IntegrableOn (fun y : ℝ ↦ -f' y / f y ^ 2) (Iic x) ∧
      ∫ y in Iic x, -f' y / f y ^ 2 = (f x)⁻¹ := by
  have hderiv : ∀ y ∈ Iic x,
      HasDerivAt (fun z : ℝ ↦ (f z)⁻¹) (-f' y / f y ^ 2) y := by
    intro y hy
    exact (hfderiv y (hy.trans_lt hx)).inv
      (ne_of_gt (hfpos y (hy.trans_lt hx)))
  have hnonneg : ∀ y ∈ Iio x, 0 ≤ -f' y / f y ^ 2 := by
    intro y hy
    exact div_nonneg (neg_nonneg.mpr (hfprimeNeg y (hy.trans hx)).le)
      (sq_nonneg _)
  have hint : IntegrableOn (fun y : ℝ ↦ -f' y / f y ^ 2) (Iic x) :=
    integrableOn_Iic_deriv_of_nonneg' hderiv hnonneg
      (tendsto_inv_endpoint_atBot_zero hlimit)
  refine ⟨hint, ?_⟩
  have hftc := integral_Iic_of_hasDerivAt_of_tendsto'
    hderiv hint (tendsto_inv_endpoint_atBot_zero hlimit)
  simpa using hftc

/-- Convexity of the endpoint solution makes the reduction-of-order entrance
solution nondecreasing. -/
theorem entranceSolutionFromEndpointSlope_nonneg
    {f f' : ℝ → ℝ} {h x : ℝ}
    (hx : x < 0)
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ y : ℝ, y < 0 → HasDerivAt f (f' y) y)
    (hfprimeNeg : ∀ y : ℝ, y < 0 → f' y < 0)
    (hfprimeMono : MonotoneOn f' (Iio (0 : ℝ))) :
    0 ≤ entranceSolutionFromEndpointSlope f f' x := by
  obtain ⟨hrhsInt, hrhsEq⟩ := integral_Iic_neg_endpointSlope_div_sq
    hx hfpos hlimit hfderiv hfprimeNeg
  have hsqInt : IntegrableOn (fun y : ℝ ↦ ((f y) ^ 2)⁻¹) (Iic x) :=
    integrableOn_inv_sq_endpoint hx hfcont hfpos hlimit
  have hlhsInt : IntegrableOn
      (fun y : ℝ ↦ (-f' x) * ((f y) ^ 2)⁻¹) (Iic x) :=
    hsqInt.const_mul _
  have hcompare :
      ∫ y in Iic x, (-f' x) * ((f y) ^ 2)⁻¹ ≤
        ∫ y in Iic x, -f' y / f y ^ 2 := by
    apply integral_mono_ae hlhsInt hrhsInt
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    have hy0 : y < 0 := hy.trans_lt hx
    have hmono : f' y ≤ f' x := hfprimeMono hy0 hx hy
    have hneg : -f' x ≤ -f' y := neg_le_neg hmono
    have hpow : 0 ≤ (f y ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hneg hpow
  rw [integral_const_mul] at hcompare
  rw [hrhsEq] at hcompare
  unfold entranceSolutionFromEndpointSlope endpointReductionIntegral
  nlinarith [hfprimeNeg x hx]

end

end DerridaRetaux
