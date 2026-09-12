import DerridaRetaux.Rigidity.ConstructedStringMeasureDensity

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

theorem tendsto_endpoint_weighted_entranceSlope_atBot_zero
    {f f' : ℝ → ℝ} {h xi : ℝ}
    (hfcont : ContinuousOn f (Iio (0 : ℝ)))
    (hfpos : ∀ y : ℝ, y < 0 → 0 < f y)
    (hlimit : Tendsto (fun y : ℝ ↦ f y + y) atBot (𝓝 h))
    (hfderiv : ∀ y : ℝ, y < 0 → HasDerivAt f (f' y) y)
    (hfprimeNeg : ∀ y : ℝ, y < 0 → f' y < 0)
    (hfprimeLimit : Tendsto f' atBot (𝓝 (-1))) :
    Tendsto
      (fun y : ℝ ↦ (xi - y) * entranceSolutionFromEndpointSlope f f' y)
      atBot (𝓝 0) := by
  have hphi := tendsto_entranceSolutionFromEndpoint_atBot_one
    hfcont hfpos hlimit hfderiv hfprimeNeg hfprimeLimit
  have hsmall : Tendsto
      (fun y : ℝ ↦ f' y * entranceSolutionFromEndpoint f y + 1)
      atBot (𝓝 0) := by
    convert hfprimeLimit.mul hphi |>.add_const 1 using 1 <;> ring
  have hden := tendsto_endpoint_div_neg_id_atBot hlimit
  have hinvNeg : Tendsto (fun y : ℝ ↦ (-y)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_neg_atBot_atTop
  have hnum : Tendsto (fun y : ℝ ↦ (xi - y) / (-y)) atBot (𝓝 1) := by
    have hxi0 : Tendsto (fun y : ℝ ↦ xi * (-y)⁻¹) atBot (𝓝 0) := by
      convert tendsto_const_nhds.mul hinvNeg using 1 <;> ring
    have hbase := hxi0.add_const 1
    simpa only [zero_add] using hbase.congr' (by
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with y hy
      field_simp [hy.ne]
      ring)
  have hfactor : Tendsto (fun y : ℝ ↦ (xi - y) / f y) atBot (𝓝 1) := by
    have hquot := hnum.div hden (by norm_num)
    have heq :
        (fun y : ℝ ↦ (xi - y) / (-y)) / (fun y : ℝ ↦ f y / (-y)) =ᶠ[atBot]
        (fun y : ℝ ↦ (xi - y) / f y) := by
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with y hy
      exact div_div_div_cancel_right₀ (neg_ne_zero.mpr hy.ne) _ _
    simpa only [one_div, inv_one] using hquot.congr' heq
  have hprod := hfactor.mul hsmall
  have heq :
      (fun y : ℝ ↦ (xi - y) / f y * (f' y * entranceSolutionFromEndpoint f y + 1)) =ᶠ[atBot]
      (fun y : ℝ ↦ (xi - y) * entranceSolutionFromEndpointSlope f f' y) := by
    filter_upwards [eventually_lt_atBot (min 0 xi)] with y hy
    have hy0 : y < 0 := hy.trans_le (min_le_left 0 xi)
    have hyxi : y < xi := hy.trans_le (min_le_right 0 xi)
    unfold entranceSolutionFromEndpointSlope entranceSolutionFromEndpoint
    rw [inv_eq_one_div]
    field_simp [ne_of_gt (hfpos y hy0), (sub_pos.mpr hyxi).ne']
    ring
  simpa only [one_mul] using hprod.congr' heq

/-- A positive normalized solution of `phi'' = c rho phi` satisfies its
entrance Volterra equation against the Lebesgue density `rho`. -/
theorem integral_entranceVolterraKernel_density
    {phi psi rho : ℝ → ℝ} {c xi : ℝ}
    (hc : 0 < c) (hxi : xi < 0)
    (hphiCont : ContinuousOn phi (Iio (0 : ℝ)))
    (hphiPos : ∀ y : ℝ, y < 0 → 0 < phi y)
    (hphiLim : Tendsto phi atBot (𝓝 1))
    (hphiDeriv : ∀ y : ℝ, y < 0 → HasDerivAt phi (psi y) y)
    (hpsiDeriv : ∀ y : ℝ, y < 0 → HasDerivAt psi (c * rho y * phi y) y)
    (hrhoNonneg : ∀ y : ℝ, y < 0 → 0 ≤ rho y)
    (hweighted : Tendsto (fun y : ℝ ↦ (xi - y) * psi y) atBot (𝓝 0)) :
    IntegrableOn (fun y : ℝ ↦ (xi - y) * phi y * rho y) (Iic xi) ∧
      ∫ y in Iic xi, (xi - y) * phi y * rho y = (phi xi - 1) / c := by
  let G : ℝ → ℝ := fun y ↦ ((xi - y) * psi y + phi y - 1) / c
  have hGderiv : ∀ y ∈ Iic xi,
      HasDerivAt G ((xi - y) * phi y * rho y) y := by
    intro y hy
    have hy0 : y < 0 := hy.trans_lt hxi
    have hlin : HasDerivAt (fun z : ℝ ↦ xi - z) (-1) y := by
      simpa only [zero_sub] using (hasDerivAt_const y xi).sub (hasDerivAt_id y)
    have hsum := (hlin.mul (hpsiDeriv y hy0)).add (hphiDeriv y hy0)
    have hscaled := (hsum.sub_const 1).div_const c
    convert hscaled using 1
    field_simp [hc.ne']
    ring
  have hnonneg : ∀ y ∈ Iio xi, 0 ≤ (xi - y) * phi y * rho y := by
    intro y hy
    have hy0 : y < 0 := hy.trans hxi
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hy.le) (hphiPos y hy0).le)
      (hrhoNonneg y hy0)
  have hGlim : Tendsto G atBot (𝓝 0) := by
    have hsum := (hweighted.add hphiLim).sub_const 1
    convert hsum.div_const c using 1 <;> ring
  have hint := integrableOn_Iic_deriv_of_nonneg' hGderiv hnonneg hGlim
  refine ⟨hint, ?_⟩
  have hftc := integral_Iic_of_hasDerivAt_of_tendsto' hGderiv hint hGlim
  simpa [G] using hftc

end

end DerridaRetaux
