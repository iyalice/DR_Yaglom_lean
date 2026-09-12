import DerridaRetaux.Rigidity.EntranceStringBase
import DerridaRetaux.Rigidity.StringCoordinates
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# The entrance string carried by the manuscript coordinates

This file turns the coordinate identities in `StringCoordinates` into an
actual measure-valued string.  The construction is deliberately separate from
the Volterra problem: no existence or uniqueness statement for the canonical
solution is used here.

Positive time carries density `A₃(t) / κ`, and is pushed forward by the
coordinate `ξ(t)`.  Both functions are extended by zero off positive time only
to make the pushforward globally measurable.  Since `ξ(t) < 0` for `t > 0`,
the resulting measure is supported on the negative half-line and may have
infinite mass as the endpoint zero is approached.
-/

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal Interval

/-- The positive-time mass rate, extended by zero off `(0,∞)`. -/
def positiveTimeMassRate (κ : ℝ) (A3 : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 < t then A3 t / κ else 0

/-- The source coordinate, extended by zero off `(0,∞)`. -/
def positiveTimeCoordinate
    (κ : ℝ) (A2 A3 : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 < t then stringXi κ A2 A3 t else 0

/-- The time-side measure whose density is the reciprocal of `Y`. -/
def stringTimeMeasure (κ : ℝ) (A3 : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun t ↦ ENNReal.ofReal (positiveTimeMassRate κ A3 t)

/-- The Stieltjes measure obtained by pushing positive time through `ξ`. -/
def constructedStringMass
    (κ : ℝ) (A2 A3 : ℝ → ℝ) : Measure ℝ :=
  Measure.map (positiveTimeCoordinate κ A2 A3) (stringTimeMeasure κ A3)

/-- The manuscript string, with finite right endpoint zero. -/
def constructedEntranceString
    (κ : ℝ) (A2 A3 : ℝ → ℝ) : EntranceString where
  mass := constructedStringMass κ A2 A3
  endpoint := 0

@[simp] theorem constructedEntranceString_endpoint
    (κ : ℝ) (A2 A3 : ℝ → ℝ) :
    (constructedEntranceString κ A2 A3).endpoint = 0 :=
  rfl

theorem continuousOn_stringXi_Ioi
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hA2 : ∀ t : ℝ, 0 < t →
      HasDerivAt A2 (A0 t * A2 t - 1) t)
    (hA3 : ∀ t : ℝ, 0 < t →
      HasDerivAt A3 (A0 t * A3 t) t)
    (hA3pos : ∀ t : ℝ, 0 < t → 0 < A3 t) :
    ContinuousOn (stringXi κ A2 A3) (Ioi 0) := by
  intro t ht
  exact (hasDerivAt_stringXi κ A0 A2 A3 (hA2 t ht) (hA3 t ht)
    (ne_of_gt (hA3pos t ht))).continuousAt.continuousWithinAt

theorem measurable_positiveTimeCoordinate
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hA2 : ∀ t : ℝ, 0 < t →
      HasDerivAt A2 (A0 t * A2 t - 1) t)
    (hA3 : ∀ t : ℝ, 0 < t →
      HasDerivAt A3 (A0 t * A3 t) t)
    (hA3pos : ∀ t : ℝ, 0 < t → 0 < A3 t) :
    Measurable (positiveTimeCoordinate κ A2 A3) := by
  have hzero : ContinuousOn (fun _ : ℝ ↦ (0 : ℝ)) (Ioi 0)ᶜ :=
    continuous_const.continuousOn
  have hpiece :=
    (continuousOn_stringXi_Ioi (κ := κ) hA2 hA3 hA3pos).measurable_piecewise
      hzero measurableSet_Ioi
  simpa only [positiveTimeCoordinate, Set.piecewise, mem_Ioi] using hpiece

theorem measurable_positiveTimeMassRate
    {κ : ℝ} {A0 A3 : ℝ → ℝ}
    (hA3 : ∀ t : ℝ, 0 < t →
      HasDerivAt A3 (A0 t * A3 t) t) :
    Measurable (positiveTimeMassRate κ A3) := by
  have hcont : ContinuousOn (fun t : ℝ ↦ A3 t / κ) (Ioi 0) := by
    intro t ht
    exact (hA3 t ht).continuousAt.div_const κ |>.continuousWithinAt
  have hzero : ContinuousOn (fun _ : ℝ ↦ (0 : ℝ)) (Ioi 0)ᶜ :=
    continuous_const.continuousOn
  have hpiece := hcont.measurable_piecewise hzero measurableSet_Ioi
  simpa only [positiveTimeMassRate, Set.piecewise, mem_Ioi] using hpiece

theorem measurable_positiveTimeDensity
    {κ : ℝ} {A0 A3 : ℝ → ℝ}
    (hA3 : ∀ t : ℝ, 0 < t →
      HasDerivAt A3 (A0 t * A3 t) t) :
    Measurable (fun t ↦ ENNReal.ofReal (positiveTimeMassRate κ A3 t)) :=
  (measurable_positiveTimeMassRate hA3).ennreal_ofReal

@[simp] theorem positiveTimeCoordinate_of_pos
    (κ : ℝ) (A2 A3 : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    positiveTimeCoordinate κ A2 A3 t = stringXi κ A2 A3 t := by
  simp [positiveTimeCoordinate, ht]

@[simp] theorem positiveTimeMassRate_of_pos
    (κ : ℝ) (A3 : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    positiveTimeMassRate κ A3 t = A3 t / κ := by
  simp [positiveTimeMassRate, ht]

theorem positiveTimeCoordinate_preimage_Iic
    {κ : ℝ} {A2 A3 : ℝ → ℝ}
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {t : ℝ} (ht : 0 < t) :
    positiveTimeCoordinate κ A2 A3 ⁻¹' Iic (stringXi κ A2 A3 t) =
      Ioc 0 t := by
  ext s
  by_cases hs : 0 < s
  · simp only [mem_preimage, mem_Iic, mem_Ioc]
    rw [positiveTimeCoordinate_of_pos κ A2 A3 hs]
    simpa only [hs, true_and] using hmono.le_iff_le hs ht
  · have hxit : stringXi κ A2 A3 t < 0 := hbij.1 ht
    simp [positiveTimeCoordinate, hs, hxit.not_le]

/-- The quadratic moment bound supplies all finite-time integrability needed
for the measure construction. -/
theorem intervalIntegrable_A3_div
    {κ C t : ℝ} {A0 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (ht : 0 < t)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hbounds : ∀ s : ℝ, 0 < s →
      A3 s ≤ C * s ^ 2) :
    IntervalIntegrable (fun s ↦ A3 s / κ) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hcont : ContinuousOn (fun s : ℝ ↦ A3 s / κ) (Ioc 0 t) := by
    intro s hs
    exact (hA3 s hs.1).continuousAt.div_const κ |>.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun s : ℝ ↦ A3 s / κ)
      (volume.restrict (Ioc 0 t)) :=
    (hcont.aemeasurable measurableSet_Ioc).aestronglyMeasurable
  have hconst : Integrable (fun _ : ℝ ↦ (C / κ) * t ^ 2)
      (volume.restrict (Ioc 0 t)) := by
    exact integrableOn_const.2 (.inr (by simp))
  apply hconst.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsκ : 0 ≤ A3 s / κ := by
    exact (div_pos (hA3pos s hs.1) hκ).le
  rw [Real.norm_eq_abs, abs_of_nonneg hsκ]
  calc
    A3 s / κ ≤ (C * s ^ 2) / κ :=
      (div_le_div_iff_of_pos_right hκ).2 (hbounds s hs.1)
    _ = (C / κ) * s ^ 2 := by ring
    _ ≤ (C / κ) * t ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hs.1.le hs.2 2)
        (div_nonneg hC.le hκ.le)

/-- The time-side measure of `(0,t]` is exactly the manuscript mass
primitive, embedded into `ENNReal`. -/
theorem stringTimeMeasure_Ioc
    {κ C t : ℝ} {A0 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (ht : 0 < t)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hupper : ∀ s : ℝ, 0 < s → A3 s ≤ C * s ^ 2) :
    stringTimeMeasure κ A3 (Ioc 0 t) =
      ENNReal.ofReal (stringMassPrimitive κ A3 t) := by
  have hint := intervalIntegrable_A3_div hκ hC ht hA3 hA3pos hupper
  have hintIoc : IntegrableOn (fun s ↦ A3 s / κ) (Ioc 0 t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).1 hint
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 t)]
      (fun s ↦ A3 s / κ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (div_pos (hA3pos s hs.1) hκ).le
  rw [stringTimeMeasure, withDensity_apply _ measurableSet_Ioc]
  calc
    (∫⁻ s in Ioc 0 t,
        ENNReal.ofReal (positiveTimeMassRate κ A3 s) ∂volume) =
        ∫⁻ s in Ioc 0 t, ENNReal.ofReal (A3 s / κ) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [positiveTimeMassRate_of_pos κ A3 hs.1]
    _ = ENNReal.ofReal (∫ s in Ioc 0 t, A3 s / κ ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hintIoc hnonneg).symm
    _ = ENNReal.ofReal (stringMassPrimitive κ A3 t) := by
      rw [stringMassPrimitive, intervalIntegral.integral_of_le ht.le]

/-- Exact cumulative identity at every positive-time coordinate. -/
theorem constructedStringMass_Iic_coordinate
    {κ C t : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hupper : ∀ s : ℝ, 0 < s → A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    constructedStringMass κ A2 A3 (Iic (stringXi κ A2 A3 t)) =
      ENNReal.ofReal (stringMassPrimitive κ A3 t) := by
  rw [constructedStringMass,
    Measure.map_apply (measurable_positiveTimeCoordinate hA2 hA3 hA3pos)
      measurableSet_Iic,
    positiveTimeCoordinate_preimage_Iic hmono hbij ht]
  exact stringTimeMeasure_Ioc hκ hC ht hA3 hA3pos hupper

/-- The `EntranceString` cumulative specializes the preceding measure
identity without changing its value. -/
theorem constructed_stringCumulative_coordinate
    {κ C t : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hupper : ∀ s : ℝ, 0 < s → A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    stringCumulative (constructedEntranceString κ A2 A3)
        (stringXi κ A2 A3 t) =
      ENNReal.ofReal (stringMassPrimitive κ A3 t) := by
  exact constructedStringMass_Iic_coordinate hκ hC ht hA2 hA3
    hA3pos hupper hmono hbij

/-- The cumulative identity transported through the inverse coordinate, for
an arbitrary negative spatial point. -/
theorem constructed_stringCumulative_of_neg
    {κ C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hupper : ∀ s : ℝ, 0 < s → A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {x : ℝ} (hx : x < 0) :
    stringCumulative (constructedEntranceString κ A2 A3) x =
      ENNReal.ofReal (stringXiMassCoordinate κ A2 A3 hmono hbij x) := by
  let e := stringXiOrderIso κ A2 A3 hmono hbij
  let t := timeOfNegativeCoordinate e x
  have ht : 0 < t := timeOfNegativeCoordinate_pos e hx
  have hxit : stringXi κ A2 A3 t = x := by
    exact coordinateOrderIso_timeOfNegativeCoordinate
      (stringXi κ A2 A3) hmono hbij hx
  calc
    stringCumulative (constructedEntranceString κ A2 A3) x =
        stringCumulative (constructedEntranceString κ A2 A3)
          (stringXi κ A2 A3 t) := by rw [hxit]
    _ = ENNReal.ofReal (stringMassPrimitive κ A3 t) :=
      constructed_stringCumulative_coordinate hκ hC ht hA2 hA3
        hA3pos hupper hmono hbij
    _ = ENNReal.ofReal
        (stringXiMassCoordinate κ A2 A3 hmono hbij
          (stringXi κ A2 A3 t)) := by
      rw [stringXiMassCoordinate_comp_eq κ A2 A3 hmono hbij ht]
    _ = ENNReal.ofReal
        (stringXiMassCoordinate κ A2 A3 hmono hbij x) := by
      rw [hxit]

/-- Every measure cumulative is monotone; in particular the constructed
cumulative has the Stieltjes monotonicity required by the manuscript. -/
theorem monotone_constructed_stringCumulative
    (κ : ℝ) (A2 A3 : ℝ → ℝ) :
    Monotone (stringCumulative (constructedEntranceString κ A2 A3)) := by
  intro x y hxy
  exact measure_mono (Iic_subset_Iic.2 hxy)

theorem continuousAt_stringMassPrimitive_of_pos
    {κ C t : ℝ} {A0 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C) (ht : 0 < t)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hupper : ∀ s : ℝ, 0 < s → A3 s ≤ C * s ^ 2) :
    ContinuousAt (stringMassPrimitive κ A3) t := by
  have hint := intervalIntegrable_A3_div hκ hC ht hA3 hA3pos hupper
  have hcont : ContinuousOn (fun s : ℝ ↦ A3 s / κ) (Ioi 0) := by
    intro s hs
    exact (hA3 s hs).continuousAt.div_const κ |>.continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter (fun s : ℝ ↦ A3 s / κ)
      (𝓝 t) volume :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioi t ht
  exact (hasDerivAt_stringMassPrimitive hint hmeas
    (hA3 t ht).continuousAt).continuousAt

/-- Below the singular endpoint the actual `ENNReal` cumulative is continuous,
hence in particular right-continuous. -/
theorem continuousAt_constructed_stringCumulative_of_neg
    {κ C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hupper : ∀ s : ℝ, 0 < s → A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {x : ℝ} (hx : x < 0) :
    ContinuousAt
      (stringCumulative (constructedEntranceString κ A2 A3)) x := by
  have ht : 0 < timeOfNegativeCoordinate
      (stringXiOrderIso κ A2 A3 hmono hbij) x :=
    timeOfNegativeCoordinate_pos
      (stringXiOrderIso κ A2 A3 hmono hbij) hx
  have htime : ContinuousAt
      (timeOfNegativeCoordinate (stringXiOrderIso κ A2 A3 hmono hbij)) x :=
    continuousAt_timeOfNegativeCoordinate
      (stringXiOrderIso κ A2 A3 hmono hbij) hx
  have hmass : ContinuousAt (stringMassPrimitive κ A3)
      (timeOfNegativeCoordinate
        (stringXiOrderIso κ A2 A3 hmono hbij) x) :=
    continuousAt_stringMassPrimitive_of_pos hκ hC ht hA3 hA3pos hupper
  have hreal : ContinuousAt
      (stringXiMassCoordinate κ A2 A3 hmono hbij) x := by
    change ContinuousAt
      (fun y ↦ stringMassPrimitive κ A3
        (timeOfNegativeCoordinate
          (stringXiOrderIso κ A2 A3 hmono hbij) y)) x
    exact hmass.comp' htime
  have henn : ContinuousAt
      (fun y ↦ ENNReal.ofReal
        (stringXiMassCoordinate κ A2 A3 hmono hbij y)) x :=
    ENNReal.continuous_ofReal.continuousAt.comp' hreal
  apply henn.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact constructed_stringCumulative_of_neg hκ hC hA2 hA3
    hA3pos hupper hmono hbij hy

theorem positiveTimeCoordinate_preimage_Ioi_zero
    {κ : ℝ} {A2 A3 : ℝ → ℝ}
    (hmaps : MapsTo (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    positiveTimeCoordinate κ A2 A3 ⁻¹' Ioi 0 = ∅ := by
  ext t
  by_cases ht : 0 < t
  · have hxi : stringXi κ A2 A3 t < 0 := hmaps ht
    simp [positiveTimeCoordinate, ht, hxi.not_lt]
  · simp [positiveTimeCoordinate, ht]

/-- The constructed string has no mass strictly above its endpoint. -/
theorem constructedStringMass_Ioi_zero
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hmaps : MapsTo (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    constructedStringMass κ A2 A3 (Ioi 0) = 0 := by
  rw [constructedStringMass,
    Measure.map_apply (measurable_positiveTimeCoordinate hA2 hA3 hA3pos)
      measurableSet_Ioi,
    positiveTimeCoordinate_preimage_Ioi_zero hmaps]
  simp

/-- Finite mass on every closed half-line strictly below the endpoint. -/
theorem constructedStringMass_Iic_lt_top_of_neg
    {κ C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hupper : ∀ s : ℝ, 0 < s → A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {b : ℝ} (hb : b < 0) :
    constructedStringMass κ A2 A3 (Iic b) < ⊤ := by
  change stringCumulative (constructedEntranceString κ A2 A3) b < ⊤
  rw [constructed_stringCumulative_of_neg hκ hC hA2 hA3 hA3pos
    hupper hmono hbij hb]
  exact ENNReal.ofReal_lt_top

/-- A fixed negative half-line already has positive mass, so the string is
not the zero measure. -/
theorem constructedStringMass_Iic_coordinate_pos
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    0 < constructedStringMass κ A2 A3
      (Iic (stringXi κ A2 A3 1)) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hint := intervalIntegrable_A3_div hκ hC zero_lt_one hA3
    hA3pos fun s hs ↦ (hbounds s hs).2
  have hlower := (stringMassPrimitive_two_sided hκ zero_lt_one hint hbounds).1
  have hprimitive : 0 < stringMassPrimitive κ A3 1 := by
    have hcoef : 0 < c / κ := div_pos hc hκ
    have : 0 < (c / κ) * ((1 : ℝ) ^ 3 / 3) := by positivity
    exact this.trans_le hlower
  rw [constructedStringMass_Iic_coordinate hκ hC zero_lt_one hA2 hA3
    hA3pos (fun s hs ↦ (hbounds s hs).2) hmono hbij]
  exact ENNReal.ofReal_pos.2 hprimitive

theorem constructedStringMass_ne_zero
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    constructedStringMass κ A2 A3 ≠ 0 := by
  intro hzero
  have hpos := constructedStringMass_Iic_coordinate_pos hκ hc hC
    hA2 hA3 hbounds hmono hbij
  rw [hzero] at hpos
  simp at hpos

/-- Cubic growth of the cumulative mass along time. -/
theorem tendsto_stringMassPrimitive_atTop
    {κ c C : ℝ} {A0 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    Tendsto (stringMassPrimitive κ A3) atTop atTop := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hcoef : 0 < (c / κ) / 3 := div_pos (div_pos hc hκ) (by norm_num)
  have hpow : Tendsto (fun t : ℝ ↦ t ^ 3) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hbase : Tendsto (fun t : ℝ ↦ (c / κ) * (t ^ 3 / 3))
      atTop atTop := by
    convert tendsto_const_nhds.pos_mul_atTop hcoef hpow using 1
    ext t
    ring
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hint := intervalIntegrable_A3_div hκ hC ht hA3 hA3pos
    fun s hs ↦ (hbounds s hs).2
  exact (stringMassPrimitive_two_sided hκ ht hint hbounds).1

/-- The inverse coordinate tends to infinite time as the spatial coordinate
approaches zero from below. -/
theorem tendsto_timeOfNegativeCoordinate_nhdsLT_zero_atTop
    {κ : ℝ} {A2 A3 : ℝ → ℝ}
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    Tendsto
      (timeOfNegativeCoordinate
        (stringXiOrderIso κ A2 A3 hmono hbij))
      (𝓝[<] (0 : ℝ)) atTop := by
  rw [tendsto_atTop]
  intro a
  let t : ℝ := max (a + 1) 1
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hat : a < t := by
    exact lt_of_lt_of_le (lt_add_one a) (le_max_left _ _)
  have hxit : stringXi κ A2 A3 t < 0 := hbij.1 ht
  have hnear : Ioi (stringXi κ A2 A3 t) ∈ 𝓝[<] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hxit)
  filter_upwards [hnear, self_mem_nhdsWithin] with x htx hx
  have htime : 0 < timeOfNegativeCoordinate
      (stringXiOrderIso κ A2 A3 hmono hbij) x :=
    timeOfNegativeCoordinate_pos _ hx
  have hrecover : stringXi κ A2 A3
      (timeOfNegativeCoordinate
        (stringXiOrderIso κ A2 A3 hmono hbij) x) = x :=
    coordinateOrderIso_timeOfNegativeCoordinate
      (stringXi κ A2 A3) hmono hbij hx
  have hle : t ≤ timeOfNegativeCoordinate
      (stringXiOrderIso κ A2 A3 hmono hbij) x := by
    apply (hmono.le_iff_le ht htime).1
    rw [hrecover]
    exact htx.le
  exact hat.le.trans hle

/-- Honest endpoint divergence: in the topology of `ENNReal`, finite
cumulatives converge to the point `⊤`. -/
theorem tendsto_constructed_stringCumulative_nhds_top
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    Tendsto (stringCumulative (constructedEntranceString κ A2 A3))
      (𝓝[<] (0 : ℝ)) (𝓝 ⊤) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have htime :=
    tendsto_timeOfNegativeCoordinate_nhdsLT_zero_atTop hmono hbij
  have hmass := tendsto_stringMassPrimitive_atTop hκ hc hC hA3 hbounds
  have htarget : Tendsto
      (fun x ↦ ENNReal.ofReal
        (stringMassPrimitive κ A3
          (timeOfNegativeCoordinate
            (stringXiOrderIso κ A2 A3 hmono hbij) x)))
      (𝓝[<] (0 : ℝ)) (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_atTop.comp (hmass.comp htime)
  apply htarget.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa only [stringXiMassCoordinate, stringMassCoordinate] using
    (constructed_stringCumulative_of_neg hκ hC hA2 hA3 hA3pos
      (fun s hs ↦ (hbounds s hs).2) hmono hbij hx).symm

/-- Time-side domination for the first entrance moment. -/
theorem integrableOn_firstMoment_timePullback
    {κ c C t : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    IntegrableOn
      (fun s ↦ (A3 s / κ) * (-stringXi κ A2 A3 s))
      (Ioc 0 t) volume := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hcont : ContinuousOn
      (fun s ↦ (A3 s / κ) * (-stringXi κ A2 A3 s))
      (Ioc 0 t) := by
    intro s hs
    have hrate := (hA3 s hs.1).continuousAt.div_const κ
    have hxi := (hasDerivAt_stringXi κ A0 A2 A3
      (hA2 s hs.1) (hA3 s hs.1) (ne_of_gt (hA3pos s hs.1))).continuousAt
    exact (hrate.mul hxi.neg).continuousWithinAt
  have hmeas : AEStronglyMeasurable
      (fun s ↦ (A3 s / κ) * (-stringXi κ A2 A3 s))
      (volume.restrict (Ioc 0 t)) :=
    (hcont.aemeasurable measurableSet_Ioc).aestronglyMeasurable
  have hconst : Integrable (fun _ : ℝ ↦ (C / c) * t)
      (volume.restrict (Ioc 0 t)) := by
    exact integrableOn_const.2 (.inr (by simp))
  apply hconst.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hratePos : 0 < A3 s / κ := div_pos (hA3pos s hs.1) hκ
  have hrateUpper : A3 s / κ ≤ (C * s ^ 2) / κ :=
    (div_le_div_iff_of_pos_right hκ).2 (hbounds s hs.1).2
  have hxi := neg_stringXi_two_sided hκ hc hC hs.1 hA2 hA3
    hprodTop hbounds
  have hxiPos : 0 < -stringXi κ A2 A3 s := by
    exact (mul_pos (div_pos hκ hC) (inv_pos.2 hs.1)).trans_le hxi.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hratePos.le hxiPos.le)]
  calc
    (A3 s / κ) * (-stringXi κ A2 A3 s) ≤
        ((C * s ^ 2) / κ) * ((κ / c) * s⁻¹) :=
      mul_le_mul hrateUpper hxi.2 hxiPos.le
        (div_nonneg (mul_nonneg hC.le (sq_nonneg s)) hκ.le)
    _ = (C / c) * s := by
      field_simp [ne_of_gt hκ, ne_of_gt hc, ne_of_gt hs.1]
      ring
    _ ≤ (C / c) * t :=
      mul_le_mul_of_nonneg_left hs.2 (div_nonneg hC.le hc.le)

/-- First entrance-moment integrability at a point of the coordinate image. -/
theorem hasFirstEntranceMomentAt_coordinate
    {κ c C t : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    HasFirstEntranceMomentAt (constructedEntranceString κ A2 A3)
      (stringXi κ A2 A3 t) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hcoordMeas :=
    measurable_positiveTimeCoordinate (κ := κ) hA2 hA3 hA3pos
  rw [HasFirstEntranceMomentAt, IntegrableOn, constructedEntranceString,
    constructedStringMass,
    Measure.restrict_map hcoordMeas measurableSet_Iic,
    positiveTimeCoordinate_preimage_Iic hmono hbij ht]
  rw [integrable_map_measure continuous_abs.aestronglyMeasurable
    hcoordMeas.aemeasurable]
  rw [stringTimeMeasure, restrict_withDensity measurableSet_Ioc]
  apply (integrable_withDensity_iff_integrable_smul₀'
    (measurable_positiveTimeDensity hA3).aemeasurable.restrict
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
  have hpull := integrableOn_firstMoment_timePullback (t := t) hκ hc hC
    hA2 hA3 hprodTop hbounds
  apply hpull.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hrateNonneg : 0 ≤ A3 s / κ :=
    (div_pos (hA3pos s hs.1) hκ).le
  have hxiNeg : stringXi κ A2 A3 s < 0 := hbij.1 hs.1
  simp only [Function.comp_apply, positiveTimeCoordinate_of_pos κ A2 A3 hs.1,
    positiveTimeMassRate_of_pos κ A3 hs.1,
    ENNReal.toReal_ofReal hrateNonneg, smul_eq_mul]
  rw [abs_of_neg hxiNeg]

/-- The first entrance moment is finite below every negative spatial point. -/
theorem hasFirstEntranceMomentAt_of_neg
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {b : ℝ} (hb : b < 0) :
    HasFirstEntranceMomentAt (constructedEntranceString κ A2 A3) b := by
  let e := stringXiOrderIso κ A2 A3 hmono hbij
  let t := timeOfNegativeCoordinate e b
  have ht : 0 < t := timeOfNegativeCoordinate_pos e hb
  have hxit : stringXi κ A2 A3 t = b :=
    coordinateOrderIso_timeOfNegativeCoordinate
      (stringXi κ A2 A3) hmono hbij hb
  rw [← hxit]
  exact hasFirstEntranceMomentAt_coordinate hκ hc hC ht hA2 hA3
    hprodTop hbounds hmono hbij

/-- Time-side domination for the second entrance moment. -/
theorem integrableOn_secondMoment_timePullback
    {κ c C t : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    IntegrableOn
      (fun s ↦ (A3 s / κ) * (stringXi κ A2 A3 s) ^ 2)
      (Ioc 0 t) volume := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hcont : ContinuousOn
      (fun s ↦ (A3 s / κ) * (stringXi κ A2 A3 s) ^ 2)
      (Ioc 0 t) := by
    intro s hs
    have hrate := (hA3 s hs.1).continuousAt.div_const κ
    have hxi := (hasDerivAt_stringXi κ A0 A2 A3
      (hA2 s hs.1) (hA3 s hs.1) (ne_of_gt (hA3pos s hs.1))).continuousAt
    exact (hrate.mul (hxi.pow 2)).continuousWithinAt
  have hmeas : AEStronglyMeasurable
      (fun s ↦ (A3 s / κ) * (stringXi κ A2 A3 s) ^ 2)
      (volume.restrict (Ioc 0 t)) :=
    (hcont.aemeasurable measurableSet_Ioc).aestronglyMeasurable
  have hconst : Integrable (fun _ : ℝ ↦ C * κ / c ^ 2)
      (volume.restrict (Ioc 0 t)) := by
    exact integrableOn_const.2 (.inr (by simp))
  apply hconst.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hratePos : 0 < A3 s / κ := div_pos (hA3pos s hs.1) hκ
  have hrateUpper : A3 s / κ ≤ (C * s ^ 2) / κ :=
    (div_le_div_iff_of_pos_right hκ).2 (hbounds s hs.1).2
  have hxi := neg_stringXi_two_sided hκ hc hC hs.1 hA2 hA3
    hprodTop hbounds
  have hxiPos : 0 < -stringXi κ A2 A3 s := by
    exact (mul_pos (div_pos hκ hC) (inv_pos.2 hs.1)).trans_le hxi.1
  have hxiSq : (-stringXi κ A2 A3 s) ^ 2 ≤
      ((κ / c) * s⁻¹) ^ 2 :=
    pow_le_pow_left₀ hxiPos.le hxi.2 2
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hratePos.le (sq_nonneg _))]
  calc
    (A3 s / κ) * (stringXi κ A2 A3 s) ^ 2 =
        (A3 s / κ) * (-stringXi κ A2 A3 s) ^ 2 := by ring
    _ ≤ ((C * s ^ 2) / κ) * (((κ / c) * s⁻¹) ^ 2) :=
      mul_le_mul hrateUpper hxiSq (sq_nonneg _)
        (div_nonneg (mul_nonneg hC.le (sq_nonneg s)) hκ.le)
    _ = C * κ / c ^ 2 := by
      field_simp [ne_of_gt hκ, ne_of_gt hc, ne_of_gt hs.1]
      ring

/-- Second entrance-moment integrability at a point of the coordinate image. -/
theorem hasSecondEntranceMomentAt_coordinate
    {κ c C t : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C) (ht : 0 < t)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    HasSecondEntranceMomentAt (constructedEntranceString κ A2 A3)
      (stringXi κ A2 A3 t) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hcoordMeas :=
    measurable_positiveTimeCoordinate (κ := κ) hA2 hA3 hA3pos
  rw [HasSecondEntranceMomentAt, IntegrableOn, constructedEntranceString,
    constructedStringMass,
    Measure.restrict_map hcoordMeas measurableSet_Iic,
    positiveTimeCoordinate_preimage_Iic hmono hbij ht]
  have hsquare : AEStronglyMeasurable (fun x : ℝ ↦ x ^ 2)
      (Measure.map (positiveTimeCoordinate κ A2 A3)
        ((stringTimeMeasure κ A3).restrict (Ioc 0 t))) :=
    (continuous_id.pow 2).aestronglyMeasurable
  rw [integrable_map_measure hsquare hcoordMeas.aemeasurable]
  rw [stringTimeMeasure, restrict_withDensity measurableSet_Ioc]
  apply (integrable_withDensity_iff_integrable_smul₀'
    (measurable_positiveTimeDensity hA3).aemeasurable.restrict
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
  have hpull := integrableOn_secondMoment_timePullback (t := t)
    hκ hc hC hA2 hA3 hprodTop hbounds
  apply hpull.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hrateNonneg : 0 ≤ A3 s / κ :=
    (div_pos (hA3pos s hs.1) hκ).le
  simp only [Function.comp_apply, positiveTimeCoordinate_of_pos κ A2 A3 hs.1,
    positiveTimeMassRate_of_pos κ A3 hs.1,
    ENNReal.toReal_ofReal hrateNonneg, smul_eq_mul]

/-- The second entrance moment is finite below every negative spatial point. -/
theorem hasSecondEntranceMomentAt_of_neg
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {b : ℝ} (hb : b < 0) :
    HasSecondEntranceMomentAt (constructedEntranceString κ A2 A3) b := by
  let e := stringXiOrderIso κ A2 A3 hmono hbij
  let t := timeOfNegativeCoordinate e b
  have ht : 0 < t := timeOfNegativeCoordinate_pos e hb
  have hxit : stringXi κ A2 A3 t = b :=
    coordinateOrderIso_timeOfNegativeCoordinate
      (stringXi κ A2 A3) hmono hbij hb
  rw [← hxit]
  exact hasSecondEntranceMomentAt_coordinate hκ hc hC ht hA2 hA3
    hprodTop hbounds hmono hbij

theorem positiveTimeCoordinate_preimage_Ici_zero
    {κ : ℝ} {A2 A3 : ℝ → ℝ}
    (hmaps : MapsTo (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    positiveTimeCoordinate κ A2 A3 ⁻¹' Ici 0 = Iic 0 := by
  ext t
  by_cases ht : 0 < t
  · have hxi : stringXi κ A2 A3 t < 0 := hmaps ht
    simp [positiveTimeCoordinate, ht, hxi.not_le]
  · simp [positiveTimeCoordinate, ht, le_of_not_gt ht]

/-- Zero extension off positive time contributes no artificial atom. -/
theorem stringTimeMeasure_Iic_zero
    (κ : ℝ) (A3 : ℝ → ℝ) :
    stringTimeMeasure κ A3 (Iic 0) = 0 := by
  rw [stringTimeMeasure, withDensity_apply _ measurableSet_Iic]
  calc
    (∫⁻ t in Iic (0 : ℝ),
        ENNReal.ofReal (positiveTimeMassRate κ A3 t) ∂volume) =
        ∫⁻ _t in Iic (0 : ℝ), (0 : ENNReal) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      change t ≤ 0 at ht
      simp [positiveTimeMassRate, not_lt_of_ge ht]
    _ = 0 := by simp

/-- In fact there is no mass at or above the endpoint. -/
theorem constructedStringMass_Ici_zero
    {κ : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s)
    (hmaps : MapsTo (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    constructedStringMass κ A2 A3 (Ici 0) = 0 := by
  rw [constructedStringMass,
    Measure.map_apply
      (measurable_positiveTimeCoordinate (κ := κ) hA2 hA3 hA3pos)
      measurableSet_Ici,
    positiveTimeCoordinate_preimage_Ici_zero hmaps,
    stringTimeMeasure_Iic_zero]

/-- At the endpoint the cumulative equals infinite total mass. -/
theorem constructed_stringCumulative_zero_eq_top
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0)) :
    stringCumulative (constructedEntranceString κ A2 A3) 0 = ⊤ := by
  have hlim := tendsto_constructed_stringCumulative_nhds_top
    hκ hc hC hA2 hA3 hbounds hmono hbij
  apply top_unique
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact monotone_constructed_stringCumulative κ A2 A3 hx.le

/-- The manuscript's explicit infinite extension for every `x ≥ 0`. -/
theorem constructed_stringCumulative_of_nonneg
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2)
    (hmono : StrictMonoOn (stringXi κ A2 A3) (Ioi 0))
    (hbij : BijOn (stringXi κ A2 A3) (Ioi 0) (Iio 0))
    {x : ℝ} (hx : 0 ≤ x) :
    stringCumulative (constructedEntranceString κ A2 A3) x = ⊤ := by
  apply top_unique
  rw [← constructed_stringCumulative_zero_eq_top hκ hc hC hA2 hA3
    hbounds hmono hbij]
  exact monotone_constructed_stringCumulative κ A2 A3 hx

/-- Source-facing closure of the admissibility predicate. -/
theorem constructedEntranceString_isEntranceType
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    IsEntranceType (constructedEntranceString κ A2 A3) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  have hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds
  refine ⟨constructedStringMass_ne_zero hκ hc hC hA2 hA3 hbounds
      hmono hbij, ?_, ?_, ?_⟩
  · intro b hb
    exact constructedStringMass_Iic_lt_top_of_neg hκ hC hA2 hA3
      hA3pos (fun s hs ↦ (hbounds s hs).2) hmono hbij hb
  · exact constructedStringMass_Ioi_zero hA2 hA3 hA3pos hbij.1
  · refine ⟨stringXi κ A2 A3 1,
      hbij.1 (by norm_num : (1 : ℝ) ∈ Ioi 0), ?_, ?_⟩
    · exact constructedStringMass_Iic_coordinate_pos hκ hc hC hA2 hA3
        hbounds hmono hbij
    · exact hasFirstEntranceMomentAt_coordinate hκ hc hC zero_lt_one
        hA2 hA3 hprodTop hbounds hmono hbij

/-- Source-facing closure of the stronger second entrance moment. -/
theorem constructedEntranceString_hasSecondEntranceMoment
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    HasSecondEntranceMoment (constructedEntranceString κ A2 A3) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  have hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds
  intro b hb
  exact hasSecondEntranceMomentAt_of_neg hκ hc hC hA2 hA3 hprodTop
    hbounds hmono hbij hb

/-- The endpoint package: endpoint zero and left convergence to the topological
point `⊤`. -/
theorem constructedEntranceString_correctRightEnd
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    (constructedEntranceString κ A2 A3).endpoint = 0 ∧
      Tendsto (stringCumulative (constructedEntranceString κ A2 A3))
        (𝓝[<] (0 : ℝ)) (𝓝 ⊤) := by
  have hA3pos : ∀ s : ℝ, 0 < s → 0 < A3 s := by
    intro s hs
    exact (mul_pos hc (sq_pos_of_pos hs)).trans_le (hbounds s hs).1
  have hmono := strictMonoOn_stringXi hκ hA2 hA3 hA3pos
  have hbij := stringXi_bijOn hκ hc hC hA2 hA3 hprodTop hbounds
  exact ⟨rfl, tendsto_constructed_stringCumulative_nhds_top
    hκ hc hC hA2 hA3 hbounds hmono hbij⟩

/-- The constructed entrance string has the manuscript's divergent right endpoint. -/
theorem constructedEntranceString_hasRightEnd_zero
    {κ c C : ℝ} {A0 A2 A3 : ℝ → ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 < C)
    (hA2 : ∀ s : ℝ, 0 < s →
      HasDerivAt A2 (A0 s * A2 s - 1) s)
    (hA3 : ∀ s : ℝ, 0 < s →
      HasDerivAt A3 (A0 s * A3 s) s)
    (hprodTop : Tendsto (stringA2Y κ A2 A3) atTop (𝓝 0))
    (hbounds : ∀ s : ℝ, 0 < s →
      c * s ^ 2 ≤ A3 s ∧ A3 s ≤ C * s ^ 2) :
    HasRightEnd (constructedEntranceString κ A2 A3) 0 := by
  simpa [HasRightEnd, NoRightBoundaryAmbiguity] using
    constructedEntranceString_correctRightEnd hκ hc hC hA2 hA3 hprodTop hbounds

end

end DerridaRetaux
