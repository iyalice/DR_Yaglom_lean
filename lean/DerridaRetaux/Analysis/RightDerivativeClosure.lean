import DerridaRetaux.Analysis.ConvolutionContinuityOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Translate a right derivative of the increment map back to the original
time coordinate. -/
theorem hasDerivWithinAt_Ici_of_increment
    (f : ℝ → ℝ) {t d : ℝ}
    (h : HasDerivWithinAt (fun q : ℝ ↦ f (t + q)) d (Ici 0) 0) :
    HasDerivWithinAt f d (Ici t) t := by
  let shift : ℝ → ℝ := fun x ↦ x - t
  have hshift : HasDerivWithinAt shift 1 (Ici t) t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have hmap : MapsTo shift (Ici t) (Ici (0 : ℝ)) := by
    intro x hx
    change t ≤ x at hx
    exact sub_nonneg.mpr hx
  have hc := h.comp_of_eq t hshift hmap (by simp [shift])
  convert hc using 1 <;> simp [shift, Function.comp_def]

/-- A continuous field of right derivatives on the open positive half-line
is the ordinary derivative field. -/
theorem hasDerivAt_of_continuous_rightDeriv
    (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hf' : ContinuousOn f' (Ioi (0 : ℝ)))
    (hright : ∀ x : ℝ, 0 < x →
      HasDerivWithinAt f (f' x) (Ici x) x)
    {t : ℝ} (ht : 0 < t) : HasDerivAt f (f' t) t := by
  let a : ℝ := t / 2
  let b : ℝ := t + 1
  have ha0 : 0 < a := half_pos ht
  have hat : a < t := by dsimp only [a]; linarith
  have htb : t < b := by dsimp only [b]; linarith
  have hab : a ≤ b := hat.le.trans htb.le
  have hfI : ContinuousOn f (Icc a b) :=
    hf.mono fun _ hx ↦ ha0.trans_le hx.1
  have hf'I : ContinuousOn f' (Icc a b) :=
    hf'.mono fun _ hx ↦ ha0.trans_le hx.1
  let clamp : ℝ → ℝ := closedIntervalClamp a b
  let fp : ℝ → ℝ := fun x ↦ f' (clamp x)
  have hfp : Continuous fp := by
    exact hf'I.comp_continuous (continuous_closedIntervalClamp a b)
      (fun x ↦ closedIntervalClamp_mem hab)
  let primitive : ℝ → ℝ := fun x ↦ f a + ∫ s in a..x, fp s
  have hprimitive : ∀ x : ℝ, HasDerivAt primitive (fp x) x := by
    intro x
    exact (intervalIntegral.integral_hasDerivAt_right
      (hfp.intervalIntegrable a x)
      (hfp.stronglyMeasurableAtFilter volume (𝓝 x))
      hfp.continuousAt).const_add (f a)
  have hpeq : ∀ x : ℝ, x ∈ Icc a b → f x = primitive x := by
    apply eq_of_has_deriv_right_eq (f' := f') (g := primitive)
    · intro x hx
      exact hright x (ha0.trans_le hx.1)
    · intro x hx
      have hclamp : clamp x = x :=
        closedIntervalClamp_eq_self ⟨hx.1, hx.2.le⟩
      simpa only [fp, hclamp, one_mul] using
        (hprimitive x).hasDerivWithinAt
    · exact hfI
    · exact (continuous_const.add (intervalIntegral.continuous_primitive
        (μ := volume) (fun c d ↦ hfp.intervalIntegrable c d) a)).continuousOn
    · simp [primitive]
  have hevent : f =ᶠ[𝓝 t] primitive := by
    filter_upwards [Ioo_mem_nhds hat htb] with x hx
    exact hpeq x ⟨hx.1.le, hx.2.le⟩
  have hclampT : clamp t = t :=
    closedIntervalClamp_eq_self ⟨hat.le, htb.le⟩
  have hpderiv : HasDerivAt primitive (f' t) t := by
    simpa only [fp, hclampT] using hprimitive t
  exact hpderiv.congr_of_eventuallyEq hevent

end

end DerridaRetaux
