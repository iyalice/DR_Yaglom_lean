import DerridaRetaux.ExternalSignatures
import DerridaRetaux.Sharpness.PowerTail
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-!
# Stable-product input parameters for the explicit sharpness law

The Chen--Shi theorem remains an explicit external fact.  This file proves all
of its hypotheses internally for the power-tail law constructed in
`Sharpness.PowerTail`.
-/

/-- The original-coordinate power tail has the exact positive stable-tail
The constant required by H3. -/
theorem sharpOriginalLaw_stableTail_tendsto
    (m : ℕ) (alpha : ℝ) (hm : 2 ≤ m) (halpha : 2 < alpha) :
    Tendsto
      (fun k : ℕ ↦ sharpOriginalLaw m alpha hm halpha k *
        (m : ℝ) ^ k * Real.rpow (k : ℝ) alpha)
      atTop
      (𝓝 (sharpNormalizingConstant m alpha * sharpTailConstant m alpha)) := by
  apply (tendsto_add_atTop_iff_nat 2).mp
  apply Tendsto.congr'
    (Eventually.of_forall fun k : ℕ ↦ ?_)
    tendsto_const_nhds
  rw [sharpOriginalLaw_tail]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hpow : (m : ℝ)⁻¹ ^ (k + 2) * (m : ℝ) ^ (k + 2) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hm0, one_pow]
  have hkpos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
  have hrpow :
      Real.rpow ((k + 2 : ℕ) : ℝ) (-alpha) *
          Real.rpow ((k + 2 : ℕ) : ℝ) alpha = 1 := by
    calc
      Real.rpow ((k + 2 : ℕ) : ℝ) (-alpha) *
          Real.rpow ((k + 2 : ℕ) : ℝ) alpha =
          Real.rpow ((k + 2 : ℕ) : ℝ) (-alpha + alpha) :=
        (Real.rpow_add hkpos (-alpha) alpha).symm
      _ = 1 := by simp
  symm
  calc
    sharpNormalizingConstant m alpha * (m : ℝ)⁻¹ ^ (k + 2) *
          sharpTailConstant m alpha * Real.rpow (k + 2 : ℝ) (-alpha) *
          (m : ℝ) ^ (k + 2) * Real.rpow ((k + 2 : ℕ) : ℝ) alpha =
        (sharpNormalizingConstant m alpha * sharpTailConstant m alpha) *
          ((m : ℝ)⁻¹ ^ (k + 2) * (m : ℝ) ^ (k + 2)) *
          (Real.rpow ((k + 2 : ℕ) : ℝ) (-alpha) *
            Real.rpow ((k + 2 : ℕ) : ℝ) alpha) := by
      push_cast
      ring
    _ = sharpNormalizingConstant m alpha * sharpTailConstant m alpha := by
      rw [hpow, hrpow]
      ring

/-- The stable-tail constant for the source's explicit exponent is positive. -/
theorem sharpnessStableTailConstant_pos
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) :
    0 < sharpNormalizingConstant m (sharpPowerExponent r) *
      sharpTailConstant m (sharpPowerExponent r) := by
  exact mul_pos
    (sharpNormalizingConstant_pos m (sharpPowerExponent r) hm
      (by linarith [three_lt_sharpPowerExponent r hr₀]))
    (sharpTailConstant_pos m (sharpPowerExponent r) hm
      (by linarith [three_lt_sharpPowerExponent r hr₀]))

/-- Source-shaped package of every internally checked H3 hypothesis. -/
theorem sharpnessPowerLaw_stableProduct_parameters
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3) :
    let alpha := sharpPowerExponent r
    let c₀ := sharpNormalizingConstant m alpha * sharpTailConstant m alpha
    (2 < alpha ∧ alpha < 4) ∧
      0 < c₀ ∧
      Critical m (sharpnessPowerLaw m r hm hr₀ hr₃) ∧
      Tendsto
        (fun k : ℕ ↦ sharpnessPowerLaw m r hm hr₀ hr₃ k *
          (m : ℝ) ^ k * Real.rpow (k : ℝ) alpha)
        atTop (𝓝 c₀) := by
  dsimp only
  refine ⟨⟨?_, sharpPowerExponent_lt_four r hr₃⟩,
    sharpnessStableTailConstant_pos m r hm hr₀,
    sharpnessPowerLaw_critical m r hm hr₀ hr₃, ?_⟩
  · linarith [three_lt_sharpPowerExponent r hr₀]
  · unfold sharpnessPowerLaw
    exact sharpOriginalLaw_stableTail_tendsto
      m (sharpPowerExponent r) hm
        (by linarith [three_lt_sharpPowerExponent r hr₀])

/-- Supplying exactly H3 yields its two-sided product estimate for the explicit
law; the external fact is not hidden in a record or imported axiom. -/
theorem sharpnessPowerLaw_product_bounds
    (m : ℕ) (r : ℝ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r) (hr₃ : r < 3)
    (hStable : ChenShiStableProductFact
      m (sharpnessPowerLaw m r hm hr₀ hr₃) (sharpPowerExponent r)
        (sharpNormalizingConstant m (sharpPowerExponent r) *
          sharpTailConstant m (sharpPowerExponent r)) hm
        (by
          exact ⟨by linarith [three_lt_sharpPowerExponent r hr₀],
            sharpPowerExponent_lt_four r hr₃⟩)
        (sharpnessStableTailConstant_pos m r hm hr₀)
        (sharpnessPowerLaw_critical m r hm hr₀ hr₃)
        (sharpOriginalLaw_stableTail_tendsto
          m (sharpPowerExponent r) hm
            (by linarith [three_lt_sharpPowerExponent r hr₀]))) :
    ∃ c₁ c₂ : ℝ,
      0 < c₁ ∧ c₁ ≤ c₂ ∧
        ∀ n : ℕ, 1 ≤ n →
          c₁ * Real.rpow (n : ℝ) (sharpPowerExponent r - 2) ≤
              criticalProduct m (sharpnessPowerLaw m r hm hr₀ hr₃) n ∧
            criticalProduct m (sharpnessPowerLaw m r hm hr₀ hr₃) n ≤
              c₂ * Real.rpow (n : ℝ) (sharpPowerExponent r - 2) :=
  hStable

end

end DerridaRetaux
