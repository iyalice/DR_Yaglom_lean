import DerridaRetaux.Analysis.ConvolutionContinuityOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- A variable short-interval moment is continuous at the collapsed endpoint
from the triangular region used by a forward Duhamel integral. -/
theorem continuousWithinAt_shortMomentIntegral
    (v : ℝ → ℝ → ℝ) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (hv : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦
        ∫ y in (0 : ℝ)..(t + z.1 - z.2), y ^ r * v z.2 y)
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let timeClamp : ℝ → ℝ := closedIntervalClamp (t / 2) (t + 1)
  let spaceClamp : ℝ → ℝ := closedIntervalClamp 0 1
  let V : ℝ → ℝ → ℝ := fun s x ↦ v (timeClamp s) (spaceClamp x)
  have htime : t / 2 ≤ t + 1 := by linarith
  have hmap : Continuous (fun p : ℝ × ℝ ↦
      (timeClamp p.1, spaceClamp p.2)) := by
    exact ((continuous_closedIntervalClamp (t / 2) (t + 1)).comp
      continuous_fst).prodMk
        ((continuous_closedIntervalClamp 0 1).comp continuous_snd)
  have hmaps : ∀ p : ℝ × ℝ,
      (timeClamp p.1, spaceClamp p.2) ∈
        Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1 := by
    intro p
    exact ⟨closedIntervalClamp_mem htime,
      closedIntervalClamp_mem (by norm_num)⟩
  have hV : Continuous (Function.uncurry V) := by
    exact hv.comp_continuous hmap hmaps
  let f : (ℝ × ℝ) → ℝ → ℝ := fun z y ↦ y ^ r * V z.2 y
  have hf : Continuous (Function.uncurry f) := by
    dsimp only [f, Function.uncurry_apply_pair]
    have hleft : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ q.2 ^ r) :=
      continuous_snd.pow r
    have hright : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ V q.1.2 q.2) := by
      exact hV.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    exact hleft.mul hright
  have ha : Continuous (fun z : ℝ × ℝ ↦ t + z.1 - z.2) := by
    fun_prop
  have hJ : Continuous (fun z : ℝ × ℝ ↦
      ∫ y in (0 : ℝ)..(t + z.1 - z.2), y ^ r * V z.2 y) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) hf ha
  apply hJ.continuousAt.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0, t) zero_lt_one)] with z hz hzd
    have hhlt : z.1 < 1 := by
      have habs : |z.1| < 1 := by
        change dist z (0, t) < 1 at hzd
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero,
          max_lt_iff] at hzd
        exact hzd.1
      exact lt_of_le_of_lt (le_abs_self z.1) habs
    have hsbox : z.2 ∈ Icc (t / 2) (t + 1) := by
      exact ⟨by linarith [ht, hz.2.1], by linarith [hz.2.2]⟩
    have ha0 : 0 ≤ t + z.1 - z.2 := by linarith [hz.2.2]
    have ha1 : t + z.1 - z.2 ≤ 1 := by linarith [hz.2.1]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le ha0] at hy
    have hybox : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans ha1⟩
    simp only [V, timeClamp, spaceClamp,
      closedIntervalClamp_eq_self hsbox,
      closedIntervalClamp_eq_self hybox]
  · simp

end

end DerridaRetaux
