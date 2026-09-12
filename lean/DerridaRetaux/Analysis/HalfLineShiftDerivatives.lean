import DerridaRetaux.Analysis.HalfLineShiftMoments
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- Right differentiation of a moment tail at the half-line endpoint. -/
theorem hasDerivWithinAt_halfLineTailMoment_zero
    (u : ℝ → ℝ) (r : ℕ)
    (hu : ContinuousOn (fun x : ℝ ↦ x ^ r * u x) (Ici 0)) :
    HasDerivWithinAt (halfLineTailMoment u r)
      (-(0 ^ r * u 0)) (Ici 0) 0 := by
  have hint : IntervalIntegrable (fun x : ℝ ↦ x ^ r * u x) volume 0 0 := by simp
  have hmeas : StronglyMeasurableAtFilter (fun x : ℝ ↦ x ^ r * u x)
      (𝓝[>] (0 : ℝ)) volume :=
    (hu.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin
      measurableSet_Ioi 0
  have hcont : ContinuousWithinAt (fun x : ℝ ↦ x ^ r * u x) (Ioi 0) 0 :=
    (hu 0 (by simp)).mono Ioi_subset_Ici_self
  have hI := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Ici (0 : ℝ)) (t := Ioi (0 : ℝ)) hint hmeas hcont
  simpa only [halfLineTailMoment, neg_eq_zero, zero_sub] using
    (hasDerivWithinAt_const (x := (0 : ℝ)) (s := Ici (0 : ℝ))
      (continuumMoment u r)).sub hI

/-- Right derivative at zero of the translated mass. -/
theorem hasDerivWithinAt_shiftedHalfLineMoment_zero
    (u : ℝ → ℝ) (hucont : ContinuousOn u (Ici 0))
    (h0 : IntegrableOn u (Ici 0)) :
    HasDerivWithinAt (shiftedHalfLineMoment u 0) (-u 0) (Ici 0) 0 := by
  have hc : ContinuousOn (fun x : ℝ ↦ x ^ 0 * u x) (Ici 0) := by simpa using hucont
  have ht := hasDerivWithinAt_halfLineTailMoment_zero u 0 hc
  have ht' : HasDerivWithinAt (halfLineTailMoment u 0) (-u 0) (Ici 0) 0 := by
    simpa using ht
  apply ht'.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact shiftedHalfLineMoment_zero u hh h0
  · simp [shiftedHalfLineMoment, halfLineTailMoment, continuumMoment]

/-- Right derivative at zero of the translated second moment. -/
theorem hasDerivWithinAt_shiftedHalfLineMoment_two
    (u : ℝ → ℝ) (hucont : ContinuousOn u (Ici 0))
    (h0 : IntegrableOn u (Ici 0))
    (h1 : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici 0))
    (h2 : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0)) :
    HasDerivWithinAt (shiftedHalfLineMoment u 2)
      (-2 * continuumMoment u 1) (Ici 0) 0 := by
  have hc0 : ContinuousOn (fun x : ℝ ↦ x ^ 0 * u x) (Ici 0) := by simpa using hucont
  have hc1 : ContinuousOn (fun x : ℝ ↦ x ^ 1 * u x) (Ici 0) :=
    (continuousOn_id.pow 1).mul hucont
  have hc2 : ContinuousOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0) :=
    (continuousOn_id.pow 2).mul hucont
  have ht0 := hasDerivWithinAt_halfLineTailMoment_zero u 0 hc0
  have ht1 := hasDerivWithinAt_halfLineTailMoment_zero u 1 hc1
  have ht2 := hasDerivWithinAt_halfLineTailMoment_zero u 2 hc2
  have hformula : HasDerivWithinAt
      (fun h ↦ halfLineTailMoment u 2 h -
        2 * h * halfLineTailMoment u 1 h +
          h ^ 2 * halfLineTailMoment u 0 h)
      (-2 * continuumMoment u 1) (Ici 0) 0 := by
    convert (ht2.sub ((((hasDerivAt_const 0 2).mul (hasDerivAt_id 0)).hasDerivWithinAt).mul ht1)).add
      (((hasDerivAt_id 0).pow 2).hasDerivWithinAt.mul ht0) using 1 <;>
      simp [halfLineTailMoment] <;> ring
  apply hformula.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact shiftedHalfLineMoment_two u hh h0 h1 h2
  · simp [shiftedHalfLineMoment, halfLineTailMoment, continuumMoment]

/-- Right derivative at zero of the translated third moment. -/
theorem hasDerivWithinAt_shiftedHalfLineMoment_three
    (u : ℝ → ℝ) (hucont : ContinuousOn u (Ici 0))
    (h0 : IntegrableOn u (Ici 0))
    (h1 : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici 0))
    (h2 : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0))
    (h3 : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u x) (Ici 0)) :
    HasDerivWithinAt (shiftedHalfLineMoment u 3)
      (-3 * continuumMoment u 2) (Ici 0) 0 := by
  have hc0 : ContinuousOn (fun x : ℝ ↦ x ^ 0 * u x) (Ici 0) := by simpa using hucont
  have hc1 : ContinuousOn (fun x : ℝ ↦ x ^ 1 * u x) (Ici 0) :=
    (continuousOn_id.pow 1).mul hucont
  have hc2 : ContinuousOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0) :=
    (continuousOn_id.pow 2).mul hucont
  have hc3 : ContinuousOn (fun x : ℝ ↦ x ^ 3 * u x) (Ici 0) :=
    (continuousOn_id.pow 3).mul hucont
  have ht0 := hasDerivWithinAt_halfLineTailMoment_zero u 0 hc0
  have ht1 := hasDerivWithinAt_halfLineTailMoment_zero u 1 hc1
  have ht2 := hasDerivWithinAt_halfLineTailMoment_zero u 2 hc2
  have ht3 := hasDerivWithinAt_halfLineTailMoment_zero u 3 hc3
  have hformula : HasDerivWithinAt
      (fun h ↦ halfLineTailMoment u 3 h -
        3 * h * halfLineTailMoment u 2 h +
          3 * h ^ 2 * halfLineTailMoment u 1 h -
            h ^ 3 * halfLineTailMoment u 0 h)
      (-3 * continuumMoment u 2) (Ici 0) 0 := by
    convert (((ht3.sub ((((hasDerivAt_const 0 3).mul (hasDerivAt_id 0)).hasDerivWithinAt).mul ht2)).add
      ((((hasDerivAt_const 0 3).mul ((hasDerivAt_id 0).pow 2)).hasDerivWithinAt).mul ht1)).sub
        (((hasDerivAt_id 0).pow 3).hasDerivWithinAt.mul ht0)) using 1 <;>
      simp [halfLineTailMoment] <;> ring
  apply hformula.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact shiftedHalfLineMoment_three u hh h0 h1 h2 h3
  · simp [shiftedHalfLineMoment, halfLineTailMoment, continuumMoment]

end

end DerridaRetaux
