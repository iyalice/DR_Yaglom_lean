import DerridaRetaux.Analysis.LaplaceGap
import DerridaRetaux.Analysis.MomentPassage
import DerridaRetaux.Analysis.PositiveConvolutionLaplace

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Zero extension of a half-line density, used to package it as a measure. -/
def halfLineDensityExtension (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then u x else 0

def halfLineDensityMeasure (u : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (halfLineDensityExtension u x))

theorem measurable_halfLineDensityExtension
    (u : ℝ → ℝ) (hu : ContinuousOn u (Ici (0 : ℝ))) :
    Measurable (halfLineDensityExtension u) := by
  have hzero : ContinuousOn (fun _ : ℝ ↦ (0 : ℝ)) (Ici (0 : ℝ))ᶜ :=
    continuous_const.continuousOn
  have hpiece := hu.measurable_piecewise hzero measurableSet_Ici
  simpa only [halfLineDensityExtension, Set.piecewise, mem_Ici] using hpiece

theorem halfLineDensityExtension_nonneg
    (u : ℝ → ℝ) (hu : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x) (x : ℝ) :
    0 ≤ halfLineDensityExtension u x := by
  by_cases hx : 0 ≤ x
  · simp [halfLineDensityExtension, hx, hu x hx]
  · simp [halfLineDensityExtension, hx]

/-- Integration against the packaged density agrees with Lebesgue integration
against `u` on the nonnegative half-line. -/
theorem integral_halfLineDensityMeasure_eq
    (u f : ℝ → ℝ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x) :
    (∫ x in Ici (0 : ℝ), f x ∂halfLineDensityMeasure u) =
      ∫ x in Ici (0 : ℝ), f x * u x := by
  rw [halfLineDensityMeasure,
    setIntegral_withDensity_eq_setIntegral_toReal_smul
      (measurable_halfLineDensityExtension u hucont).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f
      measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
  change (0 : ℝ) ≤ x at hx
  rw [ENNReal.toReal_ofReal
    (halfLineDensityExtension_nonneg u hunonneg x)]
  simp only [smul_eq_mul, halfLineDensityExtension, if_pos hx]
  ring
theorem integrableOn_halfLineDensityMeasure_iff
    (u f : ℝ → ℝ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x) :
    IntegrableOn f (Ici (0 : ℝ)) (halfLineDensityMeasure u) ↔
      IntegrableOn (fun x ↦ f x * u x) (Ici (0 : ℝ)) volume := by
  rw [IntegrableOn, halfLineDensityMeasure, restrict_withDensity measurableSet_Ici]
  have hmeas := (measurable_halfLineDensityExtension u hucont).ennreal_ofReal
  have hfinite : ∀ᵐ x ∂volume.restrict (Ici (0 : ℝ)),
      ENNReal.ofReal (halfLineDensityExtension u x) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff hmeas hfinite]
  apply integrable_congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
  change (0 : ℝ) ≤ x at hx
  rw [ENNReal.toReal_ofReal
    (halfLineDensityExtension_nonneg u hunonneg x)]
  simp only [smul_eq_mul, halfLineDensityExtension, if_pos hx]


theorem positiveHalfLineMoment_halfLineDensityMeasure
    (u : ℝ → ℝ) (r : ℕ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x) :
    positiveHalfLineMoment r (halfLineDensityMeasure u) =
      continuumMoment u r := by
  exact integral_halfLineDensityMeasure_eq u (fun x ↦ x ^ r) hucont hunonneg

theorem integratedLaplaceSecondGap_halfLineDensityMeasure
    (u : ℝ → ℝ) (p : ℝ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x) :
    integratedLaplaceSecondGap (halfLineDensityMeasure u) p =
      ∫ x in Ici (0 : ℝ), laplaceSecondGapIntegrand p x * u x := by
  exact integral_halfLineDensityMeasure_eq u (laplaceSecondGapIntegrand p)
    hucont hunonneg

/-- The integrated density gap is the algebraic quantity `p - A₀ + U` when
the first moment is one. -/
theorem integratedLaplaceSecondGap_eq_momentLaplaceGap
    (u : ℝ → ℝ) (p : ℝ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (hLap : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u x) (Ici 0))
    (hzero : IntegrableOn u (Ici 0))
    (hfirst : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici 0))
    (hA1 : continuumMoment u 1 = 1) :
    integratedLaplaceSecondGap (halfLineDensityMeasure u) p =
      momentLaplaceGap (fun _ ↦ continuumMoment u 0)
        (fun _ q ↦ continuumLaplace u q) 0 p := by
  rw [integratedLaplaceSecondGap_halfLineDensityMeasure u p hucont hunonneg]
  have hpoint : ∀ x : ℝ,
      laplaceSecondGapIntegrand p x * u x =
        (Real.exp (-(p * x)) * u x - u x) + p * (x * u x) := by
    intro x
    unfold laplaceSecondGapIntegrand
    ring
  rw [setIntegral_congr_fun measurableSet_Ici (fun x _ ↦ hpoint x)]
  have hadd := integral_add (hLap.sub hzero) (hfirst.const_mul p)
  have hsub := integral_sub hLap hzero
  have hmul := integral_const_mul (μ := volume.restrict (Ici (0 : ℝ)))
    p (fun x : ℝ ↦ x * u x)
  calc
    (∫ x in Ici (0 : ℝ),
        (Real.exp (-(p * x)) * u x - u x) + p * (x * u x)) =
        (∫ x in Ici (0 : ℝ), Real.exp (-(p * x)) * u x - u x) +
          ∫ x in Ici (0 : ℝ), p * (x * u x) := by
      simpa only [Pi.add_apply, Pi.sub_apply] using hadd
    _ = ((∫ x in Ici (0 : ℝ), Real.exp (-(p * x)) * u x) -
          ∫ x in Ici (0 : ℝ), u x) +
          p * ∫ x in Ici (0 : ℝ), x * u x := by rw [hsub, hmul]
    _ = momentLaplaceGap (fun _ ↦ continuumMoment u 0)
          (fun _ q ↦ continuumLaplace u q) 0 p := by
      unfold momentLaplaceGap continuumLaplace continuumMoment
      rw [show (∫ x in Ici (0 : ℝ), x * u x) = 1 by
        simpa only [continuumMoment, pow_one] using hA1]
      ring


theorem positiveHalfLineThirdMomentTail_halfLineDensityMeasure
    (u : ℝ → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x) :
    positiveHalfLineThirdMomentTail (halfLineDensityMeasure u) delta =
      ∫ x in Ioi delta, x ^ 3 * u x := by
  unfold positiveHalfLineThirdMomentTail halfLineDensityMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      (measurable_halfLineDensityExtension u hucont).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)
      (fun x : ℝ ↦ x ^ 3) measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hdelta.trans hx.le
  rw [ENNReal.toReal_ofReal
    (halfLineDensityExtension_nonneg u hunonneg x)]
  simp only [smul_eq_mul, halfLineDensityExtension, if_pos hx0]
  ring
end

end DerridaRetaux
