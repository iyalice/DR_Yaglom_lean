import DerridaRetaux.Analysis.TimeRiemannLimit
import DerridaRetaux.Analysis.ConvolutionContinuityOn
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- A floor-window time Riemann sum needs continuity only on one fixed compact
neighborhood of the integration interval. -/
theorem gridTimeLeftRiemannSum_along_scale_tendsto_of_continuousOn_neighborhood
    (f : ℝ → ℝ) (scale : ℕ → ℕ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hscale : Tendsto scale atTop atTop)
    (hf : ContinuousOn f (Icc (a / 2) b)) :
    Tendsto (fun n : ℕ ↦ gridTimeLeftRiemannSum f (scale n) a b)
      atTop (nhds (∫ t in a..b, f t)) := by
  let g : ℝ → ℝ := fun s ↦ f (closedIntervalClamp (a / 2) b s)
  have hcdb : a / 2 ≤ b := by linarith
  have hg : Continuous g := by
    apply continuous_iff_continuousOn_univ.mpr
    apply hf.comp (continuous_closedIntervalClamp (a / 2) b).continuousOn
    intro s _hs
    exact closedIntervalClamp_mem hcdb
  have hglobal := gridTimeLeftRiemannSum_along_scale_tendsto
    g hg scale hscale a b ha hab
  have hintegral : (∫ t in a..b, g t) = ∫ t in a..b, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact congrArg f (closedIntervalClamp_eq_self
      ⟨(by linarith [ht.1]), (by linarith [ht.2])⟩)
  rw [hintegral] at hglobal
  apply hglobal.congr'
  have hinv : Tendsto (fun n : ℕ ↦ (scale n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      tendsto_inverse_atTop_nhds_zero_nat.comp hscale
  have hinvSmall : ∀ᶠ n : ℕ in atTop, (scale n : ℝ)⁻¹ < a / 2 :=
    hinv (Iio_mem_nhds (half_pos ha))
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge := hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  filter_upwards [hinvSmall, hscalePos] with n hninv hnpos
  rw [gridTimeLeftRiemannSum, gridTimeLeftRiemannSum]
  apply Finset.sum_congr rfl
  intro s hs
  congr 2
  apply congrArg f
  apply closedIntervalClamp_eq_self
  have hNreal : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hnpos
  have hfloorA := gridIndex_div_floor_bounds (scale n) a hnpos ha.le
  have hfloorB := gridIndex_div_floor_bounds (scale n) b hnpos (ha.le.trans hab)
  have hsBounds := Finset.mem_Ico.mp hs
  have hsLower : a / 2 ≤ (s : ℝ) / (scale n : ℝ) := by
    have hfloorLower : a - (scale n : ℝ)⁻¹ <
        (gridIndex (scale n) a : ℝ) / (scale n : ℝ) := by
      linarith [hfloorA.2]
    have hmono : (gridIndex (scale n) a : ℝ) / (scale n : ℝ) ≤
        (s : ℝ) / (scale n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsBounds.1) hNreal.le
    linarith
  have hsUpper : (s : ℝ) / (scale n : ℝ) ≤ b := by
    have hmono : (s : ℝ) / (scale n : ℝ) ≤
        (gridIndex (scale n) b : ℝ) / (scale n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsBounds.2.le) hNreal.le
    linarith [hfloorB.1]
  exact ⟨hsLower, hsUpper⟩

end

end DerridaRetaux
