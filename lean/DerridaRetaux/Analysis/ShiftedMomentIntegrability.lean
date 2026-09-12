import DerridaRetaux.Analysis.HalfLineShiftMoments
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- A nonnegative shift preserves integrability of a nonnegative weighted
half-line moment. -/
theorem integrableOn_shifted_pow_mul
    (v : ℝ → ℝ) (r : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (hvcont : ContinuousOn v (Ici (0 : ℝ)))
    (hvnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ v x)
    (hint : IntegrableOn (fun x : ℝ ↦ x ^ r * v x) (Ici 0)) :
    IntegrableOn (fun x : ℝ ↦ x ^ r * v (x + h)) (Ici 0) := by
  let weighted : ℝ → ℝ := fun y ↦ y ^ r * v y
  let extended : ℝ → ℝ := (Ici (0 : ℝ)).indicator weighted
  have hext : Integrable extended volume := by
    exact hint.integrable_indicator measurableSet_Ici
  have hdom : Integrable (fun x : ℝ ↦ extended (x + h)) volume :=
    hext.comp_add_right h
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ x ^ r * v (x + h))
      (volume.restrict (Ici (0 : ℝ))) := by
    have hc : ContinuousOn (fun x : ℝ ↦ x ^ r * v (x + h)) (Ici 0) := by
      exact (continuousOn_id.pow r).mul
        (hvcont.comp (continuous_id.add continuous_const).continuousOn
          (fun x hx ↦ show (0 : ℝ) ≤ x + h from add_nonneg (show (0 : ℝ) ≤ x from hx) hh))
    exact hc.aestronglyMeasurable measurableSet_Ici
  apply (hdom.integrableOn.mono' hmeas)
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
  have hx0 : 0 ≤ x := hx
  have hxh0 : 0 ≤ x + h := by linarith
  have hv0 := hvnonneg (x + h) hxh0
  have hpow := pow_le_pow_left₀ hx0 (by linarith : x ≤ x + h) r
  dsimp only [extended, weighted]
  rw [indicator_of_mem (show x + h ∈ Ici (0 : ℝ) from hxh0)]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg hx0 r) hv0)]
  exact mul_le_mul_of_nonneg_right hpow hv0

end

end DerridaRetaux
