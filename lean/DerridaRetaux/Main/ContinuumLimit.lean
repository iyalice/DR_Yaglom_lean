import DerridaRetaux.Main.ContinuumMomentBounds
import DerridaRetaux.Main.ContinuumThirdTail
import DerridaRetaux.Main.ContinuumMild

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Proposition `prop:limit`: moment bounds, the quantitative third-moment tail, and the mild
equation for an arbitrary locally uniform subsequential limit. -/
theorem subsequentialLimitProperties
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, 0 < t →
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 ≤ C / t ∧
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 1 = 1 ∧
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ≤ C * t ∧
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ≤ C * t ^ 2) ∧
      (∀ t delta : ℝ, 0 < t → 0 < delta →
        (∫ x in Ioi delta, x ^ 3 * gluedExhaustionLimit g t x) ≤
          C * t ^ 3 / delta) ∧
      ∀ t₀ t x : ℝ, 0 < t₀ → t₀ < t → 0 ≤ x →
        gluedExhaustionLimit g t x =
          gluedExhaustionLimit g t₀ (x + t - t₀) +
            ∫ s in t₀..t, (1 / 2 : ℝ) * positiveSelfConvolution
              (fun y ↦ gluedExhaustionLimit g s y) (x + t - s) := by
  obtain ⟨C₁, hC₁, hmom⟩ := subsequentialMoment_bounds m data phi g hphi hlim
  obtain ⟨C₂, hC₂, htail⟩ := subsequentialThirdMomentTail m data phi g hphi hlim
  let C : ℝ := max C₁ C₂
  have hC : 0 < C := hC₁.trans_le (le_max_left C₁ C₂)
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · intro t ht
    have h := hmom t ht
    refine ⟨h.1.trans ?_, h.2.1, h.2.2.1.trans ?_, h.2.2.2.trans ?_⟩
    · exact div_le_div_of_nonneg_right (le_max_left C₁ C₂) ht.le
    · exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) ht.le
    · exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (sq_nonneg t)
  · intro t delta ht hdelta
    exact (htail t delta ht hdelta).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (pow_nonneg ht.le 3))
        hdelta.le)
  · intro t₀ t x ht₀ htt hx
    exact subsequentialMildEquation m data.law data.arity data.critical data.third
      data.notBinaryFixedPoint phi g hphi hlim t₀ t x ht₀ htt.le hx

end

end DerridaRetaux.FixedArity
