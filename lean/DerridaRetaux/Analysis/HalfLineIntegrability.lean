import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- A nonnegative continuous function on the half-line is integrable when its
integrals over all initial compact intervals share a finite upper bound. -/
theorem integrableOn_Ici_of_intervalIntegral_bounded
    (f : ℝ → ℝ) (C : ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hbound : ∀ R : ℕ, ∫ x in (0 : ℝ)..(R : ℝ), f x ≤ C) :
    IntegrableOn f (Ici (0 : ℝ)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop)
    (μ := volume) (f := f) C 0 (b := fun R : ℕ ↦ (R : ℝ))
  · intro R
    have hcont : ContinuousOn f (uIcc (0 : ℝ) (R : ℝ)) := by
      rw [uIcc_of_le (Nat.cast_nonneg R)]
      exact hf.mono fun _ hx ↦ hx.1
    have hint : IntervalIntegrable f volume 0 (R : ℝ) := hcont.intervalIntegrable
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg R)).1 hint
  · exact tendsto_natCast_atTop_atTop
  · exact Eventually.of_forall fun R ↦ by
      have heq : (∫ x in (0 : ℝ)..(R : ℝ), ‖f x‖) =
          ∫ x in (0 : ℝ)..(R : ℝ), f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ‖f x‖ = f x
        rw [uIcc_of_le (Nat.cast_nonneg R)] at hx
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x hx.1)]
      rw [heq]
      exact hbound R

end

end DerridaRetaux
