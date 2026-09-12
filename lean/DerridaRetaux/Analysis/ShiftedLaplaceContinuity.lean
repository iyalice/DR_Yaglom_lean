import DerridaRetaux.Analysis.HalfLineShiftLaplace
import DerridaRetaux.Analysis.LocalShiftIntegralContinuity
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Continuity of a shifted half-line Laplace transform at zero cutoff along
the forward Duhamel triangle. -/
theorem continuousWithinAt_shiftedHalfLineLaplace
    (v : ℝ → ℝ → ℝ) (p t : ℝ) (ht : 0 < t)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1))
    (hB : ContinuousOn (fun s : ℝ ↦ continuumLaplace (v s) p)
      (Icc t (t + 1)))
    (hLap : ∀ s : ℝ, t ≤ s → IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * v s x) (Ici 0)) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ shiftedHalfLineLaplace (v z.2) p
        (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let D : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
  let a : ℝ × ℝ → ℝ := fun z ↦ t + z.1 - z.2
  let w : ℝ → ℝ → ℝ := fun s y ↦ Real.exp (-(p * y)) * v s y
  have hw : ContinuousOn (Function.uncurry w)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1) := by
    dsimp only [w, Function.uncurry_apply_pair]
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_snd).neg).continuousOn).mul hv
  have hshortRaw := continuousWithinAt_shortMomentIntegral w 0 t ht hw
  have hshort : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ ∫ y in (0 : ℝ)..a z,
        Real.exp (-(p * y)) * v z.2 y) D (0, t) := by
    simpa only [w, a, pow_zero, one_mul] using hshortRaw
  let timeClamp : ℝ → ℝ := closedIntervalClamp t (t + 1)
  let Bext : ℝ → ℝ := fun s ↦ continuumLaplace (v (timeClamp s)) p
  have htime : t ≤ t + 1 := by linarith
  have hBext : Continuous Bext := by
    exact hB.comp_continuous
      (continuous_closedIntervalClamp t (t + 1))
      (fun s ↦ closedIntervalClamp_mem htime)
  have ha : Continuous a := by fun_prop
  have hmodel : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ Real.exp (p * a z) *
        (Bext z.2 - ∫ y in (0 : ℝ)..a z,
          Real.exp (-(p * y)) * v z.2 y)) D (0, t) := by
    exact ((Real.continuous_exp.comp
      (continuous_const.mul ha)).continuousAt.continuousWithinAt).mul
        ((hBext.comp continuous_snd).continuousAt.continuousWithinAt.sub hshort)
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
    have ha0 : 0 ≤ a z := by dsimp only [a]; linarith [hz.2.2]
    rw [show Bext z.2 = continuumLaplace (v z.2) p by
      simp only [Bext, timeClamp, closedIntervalClamp_eq_self hsbox]]
    simpa only [a] using shiftedHalfLineLaplace_eq
      (v z.2) p ha0 (hLap z.2 hz.2.1)
  · simp [a, Bext, timeClamp, shiftedHalfLineLaplace, continuumLaplace,
      closedIntervalClamp_eq_self
        (show t ∈ Icc t (t + 1) by constructor <;> linarith)]

end

end DerridaRetaux
