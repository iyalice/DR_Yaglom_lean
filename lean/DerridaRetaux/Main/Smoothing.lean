import DerridaRetaux.HumanInputs
import DerridaRetaux.Analysis.TemporalSmoothing
import DerridaRetaux.Analysis.TruncatedSmoothingBounds
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux.FixedArity

noncomputable section

/-!
# Source-facing smoothing estimates

This module combines the concrete truncated density decomposition with the temporal
Duhamel estimate.  Its only nonstandard inputs are the two frozen H1 facts.
-/

/-- The harmless additive constant in the gradient logarithm can be absorbed into
`log (n + 2)` uniformly over all generations. -/
private theorem one_add_log_profileScale_le_log_succ_succ (n : ℕ) :
    1 + Real.log (profileScale n) ≤
      (1 + (Real.log 2)⁻¹) * Real.log ((n + 2 : ℕ) : ℝ) := by
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwo : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log ((n + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) htwo
  have hscaleLe : profileScale n ≤ ((n + 2 : ℕ) : ℝ) := by
    dsimp [profileScale]
    exact_mod_cast (show n + 1 ≤ n + 2 by omega)
  have hlogScaleLe :
      Real.log (profileScale n) ≤ Real.log ((n + 2 : ℕ) : ℝ) :=
    Real.log_le_log (profileScale_pos n) hscaleLe
  have hone : 1 ≤ (Real.log 2)⁻¹ * Real.log ((n + 2 : ℕ) : ℝ) := by
    calc
      1 = (Real.log 2)⁻¹ * Real.log 2 := by
        field_simp [ne_of_gt hlogTwoPos]
      _ ≤ (Real.log 2)⁻¹ * Real.log ((n + 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogTwoLe (inv_nonneg.mpr hlogTwoPos.le)
  calc
    1 + Real.log (profileScale n) ≤
        (Real.log 2)⁻¹ * Real.log ((n + 2 : ℕ) : ℝ) +
          Real.log ((n + 2 : ℕ) : ℝ) := add_le_add hone hlogScaleLe
    _ = (1 + (Real.log 2)⁻¹) * Real.log ((n + 2 : ℕ) : ℝ) := by ring

/-- The logarithmic factor occurring in the spatial and temporal moduli is
nonnegative on the source range `1 ≤ h ≤ L_n`. -/
private theorem smoothingLogFactor_nonneg
    (n h : ℕ) (hh : 1 ≤ h) (hhL : h ≤ n + 1) :
    0 ≤ (h : ℝ) / profileScale n ^ 3 *
      (1 + Real.log (profileScale n / (h : ℝ))) := by
  have hhPos : (0 : ℝ) < (h : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hh
  have hratio : 1 ≤ profileScale n / (h : ℝ) := by
    apply (le_div_iff₀ hhPos).2
    simpa only [one_mul, profileScale] using
      (show ((h : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast hhL)
  exact mul_nonneg
    (div_nonneg (Nat.cast_nonneg h) (pow_nonneg (profileScale_pos n).le 3))
    (by linarith [Real.log_nonneg hratio])

/-- Equation `eq:twoparameter`, obtained from the actual `I+V` split.  The
factor two in the abstract early contribution is absorbed into the displayed
positive constant. -/
theorem smoothingTwoParameter
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n a h : ℕ, 1 ≤ h → a ≤ n / 2 →
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n) -
          (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
        (C / profileScale n ^ 3 *
          (((a + 1 : ℕ) : ℝ) + (h : ℝ) *
            (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ))))) := by
  have hnonconstant : ¬ IsDirac p₀ := by
    intro hdirac
    exact hnotBinaryFixedPoint
      (critical_isDirac_eq_binary m p₀ hm hcrit hdirac)
  have hExcess :=
    HumanInputs.cdhls_excess_upper m p₀ hm hcrit hthird hnonconstant
  have hProduct :=
    HumanInputs.cdhls_product_upper m p₀ hm hcrit hnonconstant
  rcases truncatedSmoothingSplit_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨C₀, hC₀, _hSup, hsplit⟩
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro n a h _hh ha
  rcases hsplit n a ha with ⟨early, late, hrho, hearly, hlate⟩
  have hraw := weightedSupThree_twoParameter_log_of_split
    n a h C₀ (positiveTiltedDensity m (orbit m p₀ n)) early late
      hrho hearly hlate
  apply weightedSupThree_mono (profileScale n) _ _ _ hraw
  have han : a ≤ n := ha.trans (Nat.div_le_self n 2)
  have hratio : 1 ≤ profileScale n / ((a + 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((a + 1 : ℕ) : ℝ))).2
    simpa only [one_mul, profileScale] using
      (show (((a + 1 : ℕ) : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by
        exact_mod_cast Nat.succ_le_succ han)
  let H : ℝ := (h : ℝ) *
    (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ)))
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact mul_nonneg (Nat.cast_nonneg h) (by linarith [Real.log_nonneg hratio])
  have hnum :
      C₀ * (2 * ((a + 1 : ℕ) : ℝ) + H) ≤
        (2 * C₀) * (((a + 1 : ℕ) : ℝ) + H) := by
    nlinarith [mul_nonneg hC₀.le hH]
  calc
    C₀ / profileScale n ^ 3 *
          (2 * ((a + 1 : ℕ) : ℝ) +
            (h : ℝ) *
              (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ)))) =
        (C₀ * (2 * ((a + 1 : ℕ) : ℝ) + H)) / profileScale n ^ 3 := by
      dsimp only [H]
      ring
    _ ≤ ((2 * C₀) * (((a + 1 : ℕ) : ℝ) + H)) /
          profileScale n ^ 3 :=
      div_le_div_of_nonneg_right hnum (pow_nonneg (profileScale_pos n).le 3)
    _ = 2 * C₀ / profileScale n ^ 3 *
          (((a + 1 : ℕ) : ℝ) +
            (h : ℝ) *
              (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ)))) := by
      dsimp only [H]
      ring

/-- Proposition `prop:smoothing`, with `eq:sup`, `eq:gradient`, `eq:spmod`,
and `eq:timemod` sharing one positive constant.  In particular, the gradient
bound has the source's literal `C * log (n + 2) / L_n^3` form. -/
theorem smoothing
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n))
        (C / profileScale n ^ 2)) ∧
      (∀ n : ℕ, WeightedSupThreeLE (profileScale n)
        (discreteDerivative (positiveTiltedDensity m (orbit m p₀ n)))
        (C * Real.log ((n + 2 : ℕ) : ℝ) / profileScale n ^ 3)) ∧
      (∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
        WeightedSupThreeLE (profileScale n)
          (positiveTiltedDensity m (orbit m p₀ n) -
            (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
          (C * (h : ℝ) / profileScale n ^ 3 *
            (1 + Real.log (profileScale n / (h : ℝ))))) ∧
      ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
        SupLE
          (positiveTiltedDensity m (orbit m p₀ (n + h)) -
            positiveTiltedDensity m (orbit m p₀ n))
          (C * (h : ℝ) / profileScale n ^ 3 *
            (1 + Real.log (profileScale n / (h : ℝ)))) := by
  have hnonconstant : ¬ IsDirac p₀ := by
    intro hdirac
    exact hnotBinaryFixedPoint
      (critical_isDirac_eq_binary m p₀ hm hcrit hdirac)
  have hExcess :=
    HumanInputs.cdhls_excess_upper m p₀ hm hcrit hthird hnonconstant
  have hProduct :=
    HumanInputs.cdhls_product_upper m p₀ hm hcrit hnonconstant
  rcases truncatedSmoothingSplit_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨C₀, hC₀, hSup, _hsplit⟩
  rcases positiveTiltedDensity_spatialSmoothing_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨Cₛ, hCₛ, hSpatial, hGradient⟩
  rcases positiveTiltedDensity_temporalModulus_of_H1_and_spatial
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct
      C₀ (5 * Cₛ) (by positivity) hSup hSpatial with
    ⟨Cₜ, hCₜ, hTemporal⟩
  let K : ℝ := 1 + (Real.log 2)⁻¹
  let C : ℝ := C₀ + 5 * Cₛ * K + Cₜ
  have hK : 1 ≤ K := by
    dsimp only [K]
    linarith [inv_pos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hmidNonneg : 0 ≤ 5 * Cₛ * K := by positivity
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hSupCoeff : C₀ ≤ C := by
    dsimp only [C]
    linarith [hmidNonneg, hCₜ.le]
  have hSpatialCoeff : 5 * Cₛ ≤ C := by
    have hfiveNonneg : 0 ≤ 5 * Cₛ := mul_nonneg (by norm_num) hCₛ.le
    have hfive : 5 * Cₛ ≤ 5 * Cₛ * K := by
      calc
        5 * Cₛ = (5 * Cₛ) * 1 := by ring
        _ ≤ (5 * Cₛ) * K := mul_le_mul_of_nonneg_left hK hfiveNonneg
    dsimp only [C]
    linarith [hfive, hC₀.le, hCₜ.le]
  have hGradientCoeff : 5 * Cₛ * K ≤ C := by
    dsimp only [C]
    linarith [hC₀.le, hCₜ.le]
  have hTemporalCoeff : Cₜ ≤ C := by
    dsimp only [C]
    linarith [hC₀.le, hmidNonneg]
  refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
  · intro n
    apply weightedSupThree_mono (profileScale n)
      (C₀ / profileScale n ^ 2) (C / profileScale n ^ 2) _ (hSup n)
    exact div_le_div_of_nonneg_right hSupCoeff
      (pow_nonneg (profileScale_pos n).le 2)
  · intro n
    apply weightedSupThree_mono (profileScale n)
      (5 * Cₛ / profileScale n ^ 3 * (1 + Real.log (profileScale n)))
      (C * Real.log ((n + 2 : ℕ) : ℝ) / profileScale n ^ 3) _
      (hGradient n)
    have hlogAbsorb := one_add_log_profileScale_le_log_succ_succ n
    have hlogNonneg : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ n + 2 by omega)
    have hnum :
        5 * Cₛ * (1 + Real.log (profileScale n)) ≤
          C * Real.log ((n + 2 : ℕ) : ℝ) := by
      calc
        5 * Cₛ * (1 + Real.log (profileScale n)) ≤
            5 * Cₛ *
              ((1 + (Real.log 2)⁻¹) * Real.log ((n + 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogAbsorb (by positivity)
        _ = 5 * Cₛ * K * Real.log ((n + 2 : ℕ) : ℝ) := by
          dsimp only [K]
          ring
        _ ≤ C * Real.log ((n + 2 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hGradientCoeff hlogNonneg
    calc
      5 * Cₛ / profileScale n ^ 3 * (1 + Real.log (profileScale n)) =
          (5 * Cₛ * (1 + Real.log (profileScale n))) / profileScale n ^ 3 := by
        ring
      _ ≤ (C * Real.log ((n + 2 : ℕ) : ℝ)) / profileScale n ^ 3 :=
        div_le_div_of_nonneg_right hnum (pow_nonneg (profileScale_pos n).le 3)
  · intro n h hh hhL
    apply weightedSupThree_mono (profileScale n)
      (5 * Cₛ * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ))))
      (C * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ)))) _
      (hSpatial n h hh hhL)
    have hfactor := smoothingLogFactor_nonneg n h hh hhL
    calc
      5 * Cₛ * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) =
        (5 * Cₛ) * ((h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ)))) := by ring
      _ ≤ C * ((h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ)))) :=
        mul_le_mul_of_nonneg_right hSpatialCoeff hfactor
      _ = C * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) := by ring
  · intro n h hh hhL
    intro j
    apply (hTemporal n h hh hhL j).trans
    have hfactor := smoothingLogFactor_nonneg n h hh hhL
    calc
      Cₜ * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) =
        Cₜ * ((h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ)))) := by ring
      _ ≤ C * ((h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ)))) :=
        mul_le_mul_of_nonneg_right hTemporalCoeff hfactor
      _ = C * (h : ℝ) / profileScale n ^ 3 *
          (1 + Real.log (profileScale n / (h : ℝ))) := by ring

end

end DerridaRetaux.FixedArity
