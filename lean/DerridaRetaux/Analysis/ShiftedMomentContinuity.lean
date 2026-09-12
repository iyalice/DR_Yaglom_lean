import DerridaRetaux.Analysis.HalfLineShiftMoments
import DerridaRetaux.Analysis.LocalShiftIntegralContinuity
import DerridaRetaux.Analysis.PositiveConvolutionMomentIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- A moving tail moment is continuous at zero cutoff along the forward
Duhamel triangle, provided the corresponding full moment is time-continuous. -/
theorem continuousWithinAt_halfLineTailMoment
    (v : ℝ → ℝ → ℝ) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1))
    (hB : ContinuousOn (fun s : ℝ ↦ continuumMoment (v s) r)
      (Icc t (t + 1))) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ halfLineTailMoment (v z.2) r
        (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let D : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
  let timeClamp : ℝ → ℝ := closedIntervalClamp t (t + 1)
  let B : ℝ → ℝ := fun s ↦ continuumMoment (v s) r
  let Bext : ℝ → ℝ := fun s ↦ B (timeClamp s)
  have htime : t ≤ t + 1 := by linarith
  have hBext : Continuous Bext := by
    exact hB.comp_continuous
      (continuous_closedIntervalClamp t (t + 1))
      (fun s ↦ closedIntervalClamp_mem htime)
  have hshort := continuousWithinAt_shortMomentIntegral v r t ht hv
  have hmodel : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ Bext z.2 -
        ∫ y in (0 : ℝ)..(t + z.1 - z.2), y ^ r * v z.2 y)
      D (0, t) :=
    (hBext.comp continuous_snd).continuousAt.continuousWithinAt.sub hshort
  apply hmodel.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (Metric.ball_mem_nhds (0, t) zero_lt_one)] with z hz hzd
    have hhlt : z.1 < 1 := by
      change dist z (0, t) < 1 at hzd
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero,
        max_lt_iff] at hzd
      exact lt_of_le_of_lt (le_abs_self z.1) hzd.1
    have hsbox : z.2 ∈ Icc t (t + 1) :=
      ⟨hz.2.1, by linarith [hz.2.2]⟩
    simp only [halfLineTailMoment, Bext, B,
      timeClamp, closedIntervalClamp_eq_self hsbox]
  · simp only [Prod.snd, Prod.fst, add_zero, sub_self,
      intervalIntegral.integral_same, sub_zero, halfLineTailMoment,
      Bext, B, timeClamp]
    rw [closedIntervalClamp_eq_self
      (show t ∈ Icc t (t + 1) by constructor <;> linarith)]

/-- Continuity of the shifted mass at zero along the forward Duhamel
triangle. -/
theorem continuousWithinAt_shiftedHalfLineMoment_zero
    (v : ℝ → ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1))
    (hB0 : ContinuousOn (fun s : ℝ ↦ continuumMoment (v s) 0)
      (Icc t (t + 1)))
    (hint0 : ∀ s : ℝ, t ≤ s → IntegrableOn (v s) (Ici 0)) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ shiftedHalfLineMoment (v z.2) 0
        (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let D : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
  have htail := continuousWithinAt_halfLineTailMoment v 0 t ht hv hB0
  apply htail.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact shiftedHalfLineMoment_zero (v z.2) (by linarith [hz.2.2])
      (hint0 z.2 hz.2.1)
  · simp [shiftedHalfLineMoment, halfLineTailMoment, continuumMoment]

/-- Continuity of the shifted second moment at zero along the forward
Duhamel triangle. -/
theorem continuousWithinAt_shiftedHalfLineMoment_two
    (v : ℝ → ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1))
    (hB : ∀ k : ℕ, k ≤ 2 → ContinuousOn
      (fun s : ℝ ↦ continuumMoment (v s) k) (Icc t (t + 1)))
    (hint : ∀ s : ℝ, t ≤ s → ∀ k : ℕ, k ≤ 2 →
      IntegrableOn (fun x : ℝ ↦ x ^ k * v s x) (Ici 0)) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ shiftedHalfLineMoment (v z.2) 2
        (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let D : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
  let a : ℝ × ℝ → ℝ := fun z ↦ t + z.1 - z.2
  have ha : Continuous a := by fun_prop
  have htail0 := continuousWithinAt_halfLineTailMoment v 0 t ht hv (hB 0 (by norm_num))
  have htail1 := continuousWithinAt_halfLineTailMoment v 1 t ht hv (hB 1 (by norm_num))
  have htail2 := continuousWithinAt_halfLineTailMoment v 2 t ht hv (hB 2 (by norm_num))
  have hmodel : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ halfLineTailMoment (v z.2) 2 (a z) -
        2 * a z * halfLineTailMoment (v z.2) 1 (a z) +
          a z ^ 2 * halfLineTailMoment (v z.2) 0 (a z)) D (0, t) := by
    have haW : ContinuousWithinAt a D (0, t) := ha.continuousAt.continuousWithinAt
    exact (htail2.sub ((continuousWithinAt_const.mul haW).mul htail1)).add
      ((haW.pow 2).mul htail0)
  apply hmodel.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have ha0 : 0 ≤ a z := by dsimp only [a]; linarith [hz.2.2]
    simpa only [a] using shiftedHalfLineMoment_two (v z.2) ha0
      (by simpa using hint z.2 hz.2.1 0 (by norm_num))
      (by simpa using hint z.2 hz.2.1 1 (by norm_num))
      (hint z.2 hz.2.1 2 (by norm_num))
  · simp [a, shiftedHalfLineMoment, halfLineTailMoment, continuumMoment]

/-- Continuity of the shifted third moment at zero along the forward Duhamel
triangle. -/
theorem continuousWithinAt_shiftedHalfLineMoment_three
    (v : ℝ → ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1))
    (hB : ∀ k : ℕ, k ≤ 3 → ContinuousOn
      (fun s : ℝ ↦ continuumMoment (v s) k) (Icc t (t + 1)))
    (hint : ∀ s : ℝ, t ≤ s → ∀ k : ℕ, k ≤ 3 →
      IntegrableOn (fun x : ℝ ↦ x ^ k * v s x) (Ici 0)) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ shiftedHalfLineMoment (v z.2) 3
        (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let D : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
  let a : ℝ × ℝ → ℝ := fun z ↦ t + z.1 - z.2
  have ha : Continuous a := by fun_prop
  have htail0 := continuousWithinAt_halfLineTailMoment v 0 t ht hv (hB 0 (by norm_num))
  have htail1 := continuousWithinAt_halfLineTailMoment v 1 t ht hv (hB 1 (by norm_num))
  have htail2 := continuousWithinAt_halfLineTailMoment v 2 t ht hv (hB 2 (by norm_num))
  have htail3 := continuousWithinAt_halfLineTailMoment v 3 t ht hv (hB 3 (by norm_num))
  have hmodel : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ halfLineTailMoment (v z.2) 3 (a z) -
        3 * a z * halfLineTailMoment (v z.2) 2 (a z) +
          3 * a z ^ 2 * halfLineTailMoment (v z.2) 1 (a z) -
            a z ^ 3 * halfLineTailMoment (v z.2) 0 (a z)) D (0, t) := by
    have haW : ContinuousWithinAt a D (0, t) := ha.continuousAt.continuousWithinAt
    exact ((htail3.sub ((continuousWithinAt_const.mul haW).mul htail2)).add
      (((continuousWithinAt_const.mul (haW.pow 2))).mul htail1)).sub
        ((haW.pow 3).mul htail0)
  apply hmodel.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have ha0 : 0 ≤ a z := by dsimp only [a]; linarith [hz.2.2]
    simpa only [a] using shiftedHalfLineMoment_three (v z.2) ha0
      (by simpa using hint z.2 hz.2.1 0 (by norm_num))
      (by simpa using hint z.2 hz.2.1 1 (by norm_num))
      (hint z.2 hz.2.1 2 (by norm_num))
      (hint z.2 hz.2.1 3 (by norm_num))
  · simp [a, shiftedHalfLineMoment, halfLineTailMoment, continuumMoment]

end

end DerridaRetaux
