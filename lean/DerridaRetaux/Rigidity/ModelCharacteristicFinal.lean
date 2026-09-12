import DerridaRetaux.Rigidity.ModelCharacteristic

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

theorem tendsto_modelReductionRatio_nhdsLT_zero
    {d p : ℝ} (hd : 0 < d) (hp : 0 < p) :
    Tendsto (modelReductionRatio d p) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
  have hnonneg : ∀ᶠ x : ℝ in 𝓝[<] (0 : ℝ), 0 ≤ modelReductionRatio d p x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_nonneg (modelStringEndpointSolution_pos d p hx).le
      (modelStringEntranceSolution_pos hd hp hx).le
  have hupper : ∀ᶠ x : ℝ in 𝓝[<] (0 : ℝ),
      modelReductionRatio d p x ≤ modelStringEndpointSolution d p x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hf := (modelStringEndpointSolution_pos d p hx).le
    have hphi := one_le_modelStringEntranceSolution hd hp hx
    rw [modelReductionRatio]
    exact (div_le_iff₀ (modelStringEntranceSolution_pos hd hp hx)).2
      (by nlinarith)
  exact squeeze_zero' hnonneg hupper
    (tendsto_modelStringEndpointSolution_nhdsLT_zero hd hp)

theorem integral_inv_sq_modelStringEntranceSolution
    {d p xi : ℝ} (hd : 0 < d) (hp : 0 < p) (hxi : xi < 0) :
    ∫ v in xi..0, ((modelStringEntranceSolution d p v) ^ 2)⁻¹ =
      modelReductionRatio d p xi := by
  have hderiv : ∀ x ∈ Ioo xi 0,
      HasDerivAt (fun y : ℝ ↦ -modelReductionRatio d p y)
        (((modelStringEntranceSolution d p x) ^ 2)⁻¹) x := by
    intro x hx
    simpa using (hasDerivAt_modelReductionRatio hd hp hx.2).neg
  have hleft : Tendsto (fun y : ℝ ↦ -modelReductionRatio d p y)
      (𝓝[>] xi) (𝓝 (-modelReductionRatio d p xi)) := by
    exact (hasDerivAt_modelReductionRatio hd hp hxi).continuousAt.neg.tendsto.mono_left
      inf_le_left
  have hright : Tendsto (fun y : ℝ ↦ -modelReductionRatio d p y)
      (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_modelReductionRatio_nhdsLT_zero hd hp).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hxi
    hderiv (intervalIntegrable_inv_sq_modelStringEntranceSolution hd hp hxi)
    hleft hright
  simpa using h

theorem modelString_endpoint_eq_entrance_mul_integral
    {d p xi : ℝ} (hd : 0 < d) (hp : 0 < p) (hxi : xi < 0) :
    modelStringEntranceSolution d p xi *
        ∫ v in xi..0, ((modelStringEntranceSolution d p v) ^ 2)⁻¹ =
      modelStringEndpointSolution d p xi := by
  rw [integral_inv_sq_modelStringEntranceSolution hd hp hxi]
  rw [modelReductionRatio]
  field_simp [(modelStringEntranceSolution_pos hd hp hxi).ne']

/-- The model string has the singular characteristic required by the Kotani
comparison, with value `-d p / 2`. -/
theorem modelEntranceString_hasSingularCharacteristic
    {d p : ℝ} (hd : 0 < d) (hp : 0 < p) :
    HasSingularCharacteristic (modelEntranceString d) (-(p ^ 2 / 4))
      (-d * p / 2) := by
  refine ⟨modelStringEntranceSolution d p,
    modelStringEntranceSolution_isVolterra hd hp, ?_⟩
  change Tendsto
    (fun xi : ℝ ↦ xi + modelStringEntranceSolution d p xi *
      ∫ v in xi..0, ((modelStringEntranceSolution d p v) ^ 2)⁻¹)
    atBot (𝓝 (-d * p / 2))
  apply (tendsto_modelStringEndpointSolution_add_id_atBot hd hp).congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with xi hxi
  rw [modelString_endpoint_eq_entrance_mul_integral hd hp hxi]
  ring

end

end DerridaRetaux
