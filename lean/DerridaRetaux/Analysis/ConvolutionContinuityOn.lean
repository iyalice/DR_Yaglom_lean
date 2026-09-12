import DerridaRetaux.Analysis.ConvolutionContinuity
import Mathlib.Tactic

set_option autoImplicit false

open Set MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Clamp a real coordinate to a closed interval. -/
def closedIntervalClamp (a b x : ℝ) : ℝ := max a (min b x)

theorem continuous_closedIntervalClamp (a b : ℝ) :
    Continuous (closedIntervalClamp a b) := by
  exact continuous_const.max (continuous_const.min continuous_id)

theorem closedIntervalClamp_eq_self {a b x : ℝ} (hx : x ∈ Icc a b) :
    closedIntervalClamp a b x = x := by
  simp only [closedIntervalClamp, min_eq_right hx.2, max_eq_right hx.1]

theorem closedIntervalClamp_mem {a b x : ℝ} (hab : a ≤ b) :
    closedIntervalClamp a b x ∈ Icc a b := by
  constructor
  · exact le_max_left _ _
  · exact max_le hab (min_le_left _ _)

/-- Joint continuity of half-line self-convolution on a compact rectangle
requires only joint continuity of the density on that rectangle. -/
theorem continuousOn_positiveSelfConvolution_uncurry
    (u : ℝ → ℝ → ℝ) (eta T R : ℝ)
    (hetaT : eta ≤ T) (hR : 0 ≤ R)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc eta T ×ˢ Icc (0 : ℝ) R)) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦ positiveSelfConvolution (u p.1) p.2)
      (Icc eta T ×ˢ Icc (0 : ℝ) R) := by
  let clampMap : ℝ × ℝ → ℝ × ℝ := fun p ↦
    (closedIntervalClamp eta T p.1, closedIntervalClamp 0 R p.2)
  let U : ℝ → ℝ → ℝ := fun t x ↦ u (clampMap (t, x)).1 (clampMap (t, x)).2
  have hclamp : Continuous clampMap := by
    exact (continuous_closedIntervalClamp eta T).comp continuous_fst |>.prodMk
      ((continuous_closedIntervalClamp 0 R).comp continuous_snd)
  have hmaps : MapsTo clampMap univ
      (Icc eta T ×ˢ Icc (0 : ℝ) R) := by
    intro p _hp
    exact ⟨closedIntervalClamp_mem hetaT, closedIntervalClamp_mem hR⟩
  have hU : Continuous (Function.uncurry U) := by
    apply continuous_iff_continuousOn_univ.mpr
    simpa only [U, clampMap, Function.uncurry_apply_pair,
      Function.comp_apply] using hu.comp hclamp.continuousOn hmaps
  have hconvU := continuous_positiveSelfConvolution_uncurry U hU
  apply hconvU.continuousOn.congr
  intro p hp
  have ht : closedIntervalClamp eta T p.1 = p.1 :=
    closedIntervalClamp_eq_self hp.1
  have hx : closedIntervalClamp 0 R p.2 = p.2 :=
    closedIntervalClamp_eq_self hp.2
  change positiveSelfConvolution (u p.1) p.2 =
    positiveSelfConvolution (U p.1) p.2
  rw [positiveSelfConvolution, positiveSelfConvolution]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hp.2.1] at hy
  have hyBox : y ∈ Icc (0 : ℝ) R :=
    ⟨hy.1, hy.2.trans hp.2.2⟩
  have hxyBox : p.2 - y ∈ Icc (0 : ℝ) R :=
    ⟨sub_nonneg.mpr hy.2,
      (sub_le_self p.2 hy.1).trans hp.2.2⟩
  simp only [U, clampMap, ht,
    closedIntervalClamp_eq_self hyBox,
    closedIntervalClamp_eq_self hxyBox]

end

end DerridaRetaux
