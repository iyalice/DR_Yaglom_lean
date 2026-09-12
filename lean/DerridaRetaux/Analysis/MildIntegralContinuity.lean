import DerridaRetaux.Analysis.ConvolutionContinuityOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- On a bounded positive-time window, the spatially shifted convolution
integral occurring in the mild equation is continuous up to `x = 0`. -/
theorem continuousOn_shiftedConvolutionTimeIntegral
    (u : ℝ → ℝ → ℝ) (t₀ t R : ℝ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hR : t + 1 ≤ R)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc t₀ t ×ˢ Icc (0 : ℝ) R)) :
    ContinuousOn
      (fun x ↦ ∫ s in t₀..t, (1 / 2 : ℝ) *
        positiveSelfConvolution (u s) (x + t - s))
      (Icc (0 : ℝ) 1) := by
  let K : Set (ℝ × ℝ) := Icc t₀ t ×ˢ Icc (0 : ℝ) R
  let H : ℝ × ℝ → ℝ := fun p ↦ positiveSelfConvolution (u p.1) p.2
  have hH : ContinuousOn H K := by
    simpa only [H, K] using
      continuousOn_positiveSelfConvolution_uncurry u t₀ t R ht (by linarith) hu
  let clampMap : ℝ × ℝ → ℝ × ℝ := fun p ↦
    (closedIntervalClamp t₀ t p.1, closedIntervalClamp 0 R p.2)
  let Hc : ℝ × ℝ → ℝ := fun p ↦ H (clampMap p)
  have hclamp : Continuous clampMap := by
    exact (continuous_closedIntervalClamp t₀ t).comp continuous_fst |>.prodMk
      ((continuous_closedIntervalClamp 0 R).comp continuous_snd)
  have hmaps : MapsTo clampMap univ K := by
    intro p _hp
    exact ⟨closedIntervalClamp_mem ht, closedIntervalClamp_mem (by linarith)⟩
  have hHc : Continuous Hc := by
    apply continuous_iff_continuousOn_univ.mpr
    simpa only [Hc, Function.comp_apply] using
      hH.comp hclamp.continuousOn hmaps
  let F : ℝ → ℝ → ℝ := fun x s ↦ (1 / 2 : ℝ) * Hc (s, x + t - s)
  have hF : Continuous (Function.uncurry F) := by
    have hp : Continuous (fun p : ℝ × ℝ ↦ (p.2, p.1 + t - p.2)) :=
      continuous_snd.prodMk (continuous_fst.add continuous_const |>.sub continuous_snd)
    simpa only [F, Function.uncurry_apply_pair] using
      continuous_const.mul (hHc.comp hp)
  have hKcompact : IsCompact K := by
    exact isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hH
  have hF_meas : ∀ x, AEStronglyMeasurable (F x)
      (volume.restrict (uIoc t₀ t)) := by
    intro x
    exact ((hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hbound : ∀ x, ∀ᵐ s ∂volume, s ∈ uIoc t₀ t → ‖F x s‖ ≤ |(1 / 2 : ℝ)| * C := by
    intro x
    filter_upwards [] with s hs
    have hclampMem : clampMap (s, x + t - s) ∈ K := hmaps trivial
    have hHC : ‖Hc (s, x + t - s)‖ ≤ C := by
      exact hC _ hclampMem
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hHC (abs_nonneg _)
  have hboundInt : IntervalIntegrable (fun _s : ℝ ↦ |(1 / 2 : ℝ)| * C)
      volume t₀ t := intervalIntegrable_const
  have hFcont : ∀ᵐ s ∂volume, s ∈ uIoc t₀ t →
      Continuous (fun x ↦ F x s) := by
    filter_upwards [] with s _hs
    simpa only [F, Function.uncurry_apply_pair] using
      hF.comp (continuous_id.prodMk continuous_const)
  have hIntegral : Continuous
      (fun x ↦ ∫ s in t₀..t, F x s) :=
    intervalIntegral.continuous_of_dominated_interval hF_meas hbound hboundInt hFcont
  apply hIntegral.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  have hsTime : s ∈ Icc t₀ t := ⟨hs.1, hs.2⟩
  have hspace : x + t - s ∈ Icc (0 : ℝ) R := by
    constructor
    · linarith [hx.1, hs.2]
    · linarith [hx.2, hs.1, hR]
  have hpK : (s, x + t - s) ∈ K := ⟨hsTime, hspace⟩
  have hclampEq : clampMap (s, x + t - s) = (s, x + t - s) := by
    apply Prod.ext
    · exact closedIntervalClamp_eq_self hsTime
    · exact closedIntervalClamp_eq_self hspace
  simp only [F, Hc, H]
  rw [hclampEq]

end

end DerridaRetaux
