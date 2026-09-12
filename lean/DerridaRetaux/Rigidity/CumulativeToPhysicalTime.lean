import DerridaRetaux.Rigidity.StringAdmissibility
import DerridaRetaux.Rigidity.ModelString

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace DerridaRetaux

noncomputable section

/-- Equality of the constructed and model cumulative strings identifies the
source scale at every positive time. -/
theorem stringY_eq_stringXi_sq_div_of_cumulative_eq_model
    {κ c C d : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (hd : 0 < d)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hcumulative : ∀ x : ℝ,
      stringCumulative (constructedEntranceString κ A2 A3) x =
        stringCumulative (modelEntranceString d) x) :
    ∀ t : ℝ, 0 < t →
      stringY κ A3 t = stringXi κ A2 A3 t ^ 2 / d := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := fun s hs ↦
    (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  let hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  let hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds
  have hreal : ∀ x : ℝ, x < 0 →
      stringXiMassCoordinate κ A2 A3 hmono hbij x =
        modelStringCumulativeReal d x := by
    intro x hx
    have hconstructed := constructed_stringCumulative_of_neg
      hκ hC hA2 hA3 hA3pos (fun s hs ↦ (hbounds s hs).2)
        hmono hbij hx
    have hmodel := model_stringCumulative_of_neg d hx
    have henn : ENNReal.ofReal
          (stringXiMassCoordinate κ A2 A3 hmono hbij x) =
        ENNReal.ofReal (modelStringCumulativeReal d x) := by
      calc
        ENNReal.ofReal (stringXiMassCoordinate κ A2 A3 hmono hbij x) =
            stringCumulative (constructedEntranceString κ A2 A3) x :=
          hconstructed.symm
        _ = stringCumulative (modelEntranceString d) x := hcumulative x
        _ = ENNReal.ofReal (modelStringCumulativeReal d x) := hmodel
    let e := stringXiOrderIso κ A2 A3 hmono hbij
    let s := timeOfNegativeCoordinate e x
    have hs : 0 < s := timeOfNegativeCoordinate_pos e hx
    have hxis : stringXi κ A2 A3 s = x :=
      coordinateOrderIso_timeOfNegativeCoordinate
        (stringXi κ A2 A3) hmono hbij hx
    have hsourceNonneg :
        0 ≤ stringXiMassCoordinate κ A2 A3 hmono hbij x := by
      rw [← hxis, stringXiMassCoordinate_comp_eq κ A2 A3 hmono hbij hs]
      rw [stringMassPrimitive, intervalIntegral.integral_of_le hs.le]
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact (div_pos (hA3pos u hu.1) hκ).le
    have hmodelNonneg : 0 ≤ modelStringCumulativeReal d x :=
      (modelStringCumulativeReal_pos hd.ne' hx).le
    exact (ENNReal.ofReal_eq_ofReal_iff hsourceNonneg hmodelNonneg).mp henn
  intro t ht
  have hA3t : 0 < A3 t := hA3pos t ht
  have hYt : 0 < stringY κ A3 t := stringY_pos hκ hA3t
  have hxit : stringXi κ A2 A3 t < 0 := hbij.1 ht
  have hint := intervalIntegrable_A3_div hκ hC ht hA3 hA3pos
    (fun s hs ↦ (hbounds s hs).2)
  have hcont : ContinuousOn (fun s : ℝ ↦ A3 s / κ) (Ioi 0) := by
    intro s hs
    exact (hA3 s hs).continuousAt.div_const κ |>.continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter (fun s : ℝ ↦ A3 s / κ)
      (𝓝 t) volume := hcont.stronglyMeasurableAtFilter isOpen_Ioi t ht
  have hsource := hasDerivAt_stringXiMassCoordinate hmono hbij ht hκ
    (hA2 t ht) (hA3 t ht) hA3t hint hmeas
  have hmodel := hasDerivAt_modelStringCumulativeReal d hxit.ne
  have hevent :
      stringXiMassCoordinate κ A2 A3 hmono hbij =ᶠ[𝓝 (stringXi κ A2 A3 t)]
        modelStringCumulativeReal d := by
    filter_upwards [Iio_mem_nhds hxit] with x hx
    exact hreal x hx
  have hdensity : (stringY κ A3 t)⁻¹ ^ 2 =
      d ^ 2 / (-stringXi κ A2 A3 t) ^ 4 :=
    (hsource.congr_of_eventuallyEq hevent.symm).unique hmodel
  have hsq : (stringY κ A3 t * d) ^ 2 =
      (stringXi κ A2 A3 t ^ 2) ^ 2 := by
    field_simp [hYt.ne', hxit.ne] at hdensity
    ring_nf at hdensity ⊢
    exact hdensity.symm
  have hlinear : stringY κ A3 t * d = stringXi κ A2 A3 t ^ 2 :=
    (sq_eq_sq₀ (mul_nonneg hYt.le hd.le) (sq_nonneg _)).mp hsq
  exact (eq_div_iff hd.ne').2 hlinear

end

end DerridaRetaux
