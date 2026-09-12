import DerridaRetaux.Analysis.ContinuumMomentUniformContinuity
import Mathlib.Tactic

set_option autoImplicit false

open Set MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Beyond a cutoff at least one, every nonnegative moment tail of order at
most three is bounded by the third-moment tail. -/
theorem lowerMomentTail_le_thirdMomentTail
    (u : ℝ → ℝ) (r : ℕ) (R : ℝ) (hr : r ≤ 3) (hR : 1 ≤ R)
    (hu : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (hintr : IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici 0))
    (hint3 : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u x) (Ici 0)) :
    (∫ x in Ioi R, x ^ r * u x) ≤
      ∫ x in Ioi R, x ^ 3 * u x := by
  have hsub : Ioi R ⊆ Ici (0 : ℝ) := by
    intro x hx
    exact (show (0 : ℝ) ≤ x from zero_le_one.trans (hR.trans hx.le))
  apply setIntegral_mono_on (hintr.mono_set hsub) (hint3.mono_set hsub)
    measurableSet_Ioi
  intro x hx
  have hx1 : 1 ≤ x := hR.trans hx.le
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx1 hr)
    (hu x (zero_le_one.trans hx1))

end

end DerridaRetaux
