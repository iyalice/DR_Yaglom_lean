import DerridaRetaux.Analysis.ImproperFTCNonneg
import DerridaRetaux.Rigidity.ModelVolterraIntegral

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

theorem integrableOn_modelVolterraSecond
    {d p xi : ℝ} (hd : 0 < d) (hp : 0 < p) (hxi : xi < 0) :
    IntegrableOn
      (fun x : ℝ ↦ (xi - x) * modelStringEntranceSolutionSecond d p x)
      (Iic xi) volume := by
  apply integrableOn_Iic_deriv_of_nonneg'
    (g := modelVolterraPrimitive d p xi)
  · intro x hx
    exact hasDerivAt_modelVolterraPrimitive hd.ne' hp.ne'
      (lt_of_le_of_lt hx hxi)
  · intro x hx
    exact modelVolterraPrimitive_deriv_nonneg hd hp hx.le hxi
  · exact tendsto_modelVolterraPrimitive_atBot hd.ne' hp.ne'

theorem integral_modelVolterraSecond_Iic
    {d p xi : ℝ} (hd : 0 < d) (hp : 0 < p) (hxi : xi < 0) :
    ∫ x in Iic xi,
        (xi - x) * modelStringEntranceSolutionSecond d p x =
      modelStringEntranceSolution d p xi - 1 := by
  have hderiv : ∀ x ∈ Iic xi,
      HasDerivAt (modelVolterraPrimitive d p xi)
        ((xi - x) * modelStringEntranceSolutionSecond d p x) x := by
    intro x hx
    exact hasDerivAt_modelVolterraPrimitive hd.ne' hp.ne'
      (lt_of_le_of_lt hx hxi)
  have h := integral_Iic_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_modelVolterraSecond hd hp hxi)
    (tendsto_modelVolterraPrimitive_atBot hd.ne' hp.ne')
  simpa [modelVolterraPrimitive] using h

theorem integral_modelStringMass_eq_density
    (d : ℝ) (g : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂modelStringMass d =
      ∫ x in s, g x * modelStringDensity d x := by
  rw [modelStringMass,
    setIntegral_withDensity_eq_setIntegral_toReal_smul
      (measurable_modelStringDensity d).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) g hs]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (modelStringDensity_nonneg d x)]
  simp only [smul_eq_mul]
  ring

theorem integrableOn_modelVolterraKernel_mass
    {d p xi : ℝ} (hd : 0 < d) (hp : 0 < p) (hxi : xi < 0) :
    IntegrableOn
      (fun x : ℝ ↦ (xi - x) * modelStringEntranceSolution d p x)
      (Iic xi) (modelStringMass d) := by
  rw [integrableOn_modelStringMass_iff d _ _ measurableSet_Iic]
  have hscaled :=
    (integrableOn_modelVolterraSecond hd hp hxi).const_mul (4 / p ^ 2)
  refine Integrable.congr hscaled ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  have hx0 : x < 0 := lt_of_le_of_lt hx hxi
  change (4 / p ^ 2) * ((xi - x) * modelStringEntranceSolutionSecond d p x) =
    (xi - x) * modelStringEntranceSolution d p x * modelStringDensity d x
  rw [modelStringEntranceSolution_ode hd.ne' hp.ne' hx0]
  field_simp [hp.ne']
  ring

theorem integral_modelVolterraKernel_mass
    {d p xi : ℝ} (hd : 0 < d) (hp : 0 < p) (hxi : xi < 0) :
    ∫ x in Iic xi,
        (xi - x) * modelStringEntranceSolution d p x ∂modelStringMass d =
      (4 / p ^ 2) * (modelStringEntranceSolution d p xi - 1) := by
  rw [integral_modelStringMass_eq_density d _ measurableSet_Iic]
  calc
    (∫ x in Iic xi,
        (xi - x) * modelStringEntranceSolution d p x * modelStringDensity d x) =
        ∫ x in Iic xi,
          (4 / p ^ 2) *
            ((xi - x) * modelStringEntranceSolutionSecond d p x) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x hx
      have hx0 : x < 0 := lt_of_le_of_lt hx hxi
      change (xi - x) * modelStringEntranceSolution d p x * modelStringDensity d x =
        (4 / p ^ 2) * ((xi - x) * modelStringEntranceSolutionSecond d p x)
      rw [modelStringEntranceSolution_ode hd.ne' hp.ne' hx0]
      field_simp [hp.ne']
      ring
    _ = (4 / p ^ 2) *
        ∫ x in Iic xi,
          (xi - x) * modelStringEntranceSolutionSecond d p x := by
      rw [MeasureTheory.integral_const_mul]
    _ = (4 / p ^ 2) * (modelStringEntranceSolution d p xi - 1) := by
      rw [integral_modelVolterraSecond_Iic hd hp hxi]

/-- The explicit entrance-normalized model solution satisfies the exact Volterra
equation at spectral parameter `-p²/4`. -/
theorem modelStringEntranceSolution_isVolterra
    {d p : ℝ} (hd : 0 < d) (hp : 0 < p) :
    IsEntranceNormalizedVolterraSolution (modelEntranceString d) (-(p ^ 2 / 4))
      (modelStringEntranceSolution d p) := by
  refine ⟨continuousOn_modelStringEntranceSolution hd.ne' hp.ne',
    tendsto_modelStringEntranceSolution_atBot hd.ne' hp.ne', ?_⟩
  intro xi hxi
  rw [modelEntranceString_endpoint] at hxi
  refine ⟨integrableOn_modelVolterraKernel_mass hd hp hxi, ?_⟩
  change modelStringEntranceSolution d p xi =
    1 - -(p ^ 2 / 4) *
      ∫ v in Iic xi, (xi - v) * modelStringEntranceSolution d p v ∂modelStringMass d
  rw [integral_modelVolterraKernel_mass hd hp hxi]
  field_simp [hp.ne']
  ring

end

end DerridaRetaux
