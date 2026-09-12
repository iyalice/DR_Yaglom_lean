import DerridaRetaux.Analysis.SmoothingBounds
import DerridaRetaux.Analysis.SpatialTelescoping
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Arithmetic layer of logarithmic smoothing

This file isolates the deterministic finite-sum, spatial-telescoping, and parameter-
optimization steps behind `eq:lateQ`, `eq:twoparameter`, `eq:spmod`, and `eq:gradient`.
It deliberately does not define the manuscript's `Q`, `V`, or orbit-level splitting.
Instead, the unavailable early-amplitude and late-derivative estimates occur as explicit
hypotheses of the final bridge.
-/

/-- A shifted finite harmonic sum is a difference of harmonic numbers. -/
theorem sum_Ico_inv_nat_succ_eq_harmonic_difference
    (a n : ℕ) (han : a ≤ n) :
    ∑ s ∈ Finset.Ico a n, (((s + 1 : ℕ) : ℝ))⁻¹ =
      (harmonic n : ℝ) - (harmonic a : ℝ) := by
  rw [Finset.sum_Ico_eq_sub _ han]
  simp only [harmonic, Rat.cast_sub, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- The exact logarithmic estimate used for late-time remainder sums. -/
theorem sum_Ico_inv_nat_succ_le_one_add_log_ratio
    (a n : ℕ) (han : a ≤ n) :
    ∑ s ∈ Finset.Ico a n, (((s + 1 : ℕ) : ℝ))⁻¹ ≤
      1 + Real.log (((n + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) := by
  rw [sum_Ico_inv_nat_succ_eq_harmonic_difference a n han]
  by_cases hn : n = 0
  · have ha : a = 0 := Nat.eq_zero_of_le_zero (hn ▸ han)
    subst a
    subst n
    norm_num
  · have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hupper : (harmonic n : ℝ) ≤ 1 + Real.log (n : ℝ) :=
      harmonic_le_one_add_log n
    have hlower : Real.log ((a + 1 : ℕ) : ℝ) ≤ (harmonic a : ℝ) :=
      log_add_one_le_harmonic a
    have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hnOne
    have hnSuccPos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have haSuccNe : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hnSuccNe : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hlog : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log hnPos
      exact_mod_cast Nat.le_succ n
    rw [Real.log_div hnSuccNe haSuccNe]
    linarith

/-- A bounded sequence and any of its left shifts differ by at most twice the
same weighted bound. -/
theorem weightedSupThree_sub_shiftLeft_iterate_of_bound
    (L A : ℝ) (h : ℕ) (hL : 0 < L) (f : Seq)
    (hf : WeightedSupThreeLE L f A) :
    WeightedSupThreeLE L (f - (shiftLeft^[h]) f) (2 * A) := by
  have hshift : WeightedSupThreeLE L ((shiftLeft^[h]) f) A :=
    weightedSupThree_shiftLeft_iterate L A h hL f hf
  intro j
  have hweight : 0 ≤ cubicWeight L j := cubicWeight_nonneg L hL j
  calc
    cubicWeight L j * |(f - (shiftLeft^[h]) f) j| =
        cubicWeight L j * |f j - (shiftLeft^[h]) f j| := by rfl
    _ ≤ cubicWeight L j * (|f j| + |(shiftLeft^[h]) f j|) := by
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) hweight
    _ = cubicWeight L j * |f j| +
        cubicWeight L j * |(shiftLeft^[h]) f j| := by ring
    _ ≤ A + A := add_le_add (hf j) (hshift j)
    _ = 2 * A := by ring

/-- An explicit early/late split converts an early amplitude estimate and a late
derivative estimate into the manuscript's two-parameter spatial estimate. -/
theorem weightedSupThree_twoParameter_of_split
    (L A D : ℝ) (h : ℕ) (hL : 0 < L) (rho early late : Seq)
    (hsplit : rho = early + late)
    (hearly : WeightedSupThreeLE L early A)
    (hlate : WeightedSupThreeLE L (discreteDerivative late) D) :
    WeightedSupThreeLE L (rho - (shiftLeft^[h]) rho)
      (2 * A + (h : ℝ) * D) := by
  have hearlyDiff :=
    weightedSupThree_sub_shiftLeft_iterate_of_bound L A h hL early hearly
  have hlateDiff :=
    weightedSupThree_sub_shiftLeft_iterate L D h hL late hlate
  have hdecomp :
      rho - (shiftLeft^[h]) rho =
        (early - (shiftLeft^[h]) early) +
          (late - (shiftLeft^[h]) late) := by
    rw [hsplit]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, shiftLeft_iterate_apply]
    ring
  rw [hdecomp]
  exact weightedSupThree_add L (2 * A) ((h : ℝ) * D) hL
    (early - (shiftLeft^[h]) early) (late - (shiftLeft^[h]) late)
    hearlyDiff hlateDiff

/-- Source-scaled form of the two-parameter estimate.  The hypotheses are exactly
the earlier transported-amplitude and late-derivative bounds; no spatial modulus
is assumed. -/
theorem weightedSupThree_twoParameter_log_of_split
    (n a h : ℕ) (C : ℝ) (rho early late : Seq)
    (hsplit : rho = early + late)
    (hearly : WeightedSupThreeLE (profileScale n) early
      (C / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ)))
    (hlate : WeightedSupThreeLE (profileScale n) (discreteDerivative late)
      (C / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ))))) :
    WeightedSupThreeLE (profileScale n) (rho - (shiftLeft^[h]) rho)
      (C / profileScale n ^ 3 *
        (2 * ((a + 1 : ℕ) : ℝ) +
          (h : ℝ) *
            (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ))))) := by
  have hbound := weightedSupThree_twoParameter_of_split
    (profileScale n)
    (C / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ))
    (C / profileScale n ^ 3 *
      (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ))))
    h (profileScale_pos n) rho early late hsplit hearly hlate
  convert hbound using 1
  ring

/-- Choosing the splitting time `a=h` in the low-shift regime converts the
two-parameter coefficient into `h * (1 + log (L_n / h))`. -/
theorem twoParameter_at_shift_le_log_modulus
    (n h : ℕ) (C : ℝ) (hC : 0 ≤ C) (hh : 1 ≤ h) (hsmall : h ≤ n / 2) :
    C / profileScale n ^ 3 *
        (2 * ((h + 1 : ℕ) : ℝ) +
          (h : ℝ) *
            (1 + Real.log (profileScale n / ((h + 1 : ℕ) : ℝ)))) ≤
      5 * C * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ))) := by
  have hhPos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hh
  have hhSuccPos : (0 : ℝ) < ((h + 1 : ℕ) : ℝ) := by positivity
  have hLPos : 0 < profileScale n := profileScale_pos n
  have hhn : h ≤ n := hsmall.trans (Nat.div_le_self n 2)
  have hhL : (h : ℝ) ≤ profileScale n := by
    dsimp [profileScale]
    exact_mod_cast hhn.trans (Nat.le_succ n)
  have hratioOne : 1 ≤ profileScale n / (h : ℝ) := by
    exact (le_div_iff₀ hhPos).2 (by simpa using hhL)
  have hratioPos : 0 < profileScale n / (h : ℝ) := div_pos hLPos hhPos
  have hratioSuccPos : 0 < profileScale n / ((h + 1 : ℕ) : ℝ) :=
    div_pos hLPos hhSuccPos
  have hratioMono :
      profileScale n / ((h + 1 : ℕ) : ℝ) ≤
        profileScale n / (h : ℝ) := by
    apply (div_le_div_iff₀ hhSuccPos hhPos).2
    have hhCast : (h : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ h
    exact mul_le_mul_of_nonneg_left hhCast hLPos.le
  have hlogNonneg : 0 ≤ Real.log (profileScale n / (h : ℝ)) :=
    Real.log_nonneg hratioOne
  have hlogMono :
      Real.log (profileScale n / ((h + 1 : ℕ) : ℝ)) ≤
        Real.log (profileScale n / (h : ℝ)) :=
    Real.log_le_log hratioSuccPos hratioMono
  have hearly : 2 * ((h + 1 : ℕ) : ℝ) ≤ 4 * (h : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hhOne : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    nlinarith
  have hlate :
      (h : ℝ) *
          (1 + Real.log (profileScale n / ((h + 1 : ℕ) : ℝ))) ≤
        (h : ℝ) * (1 + Real.log (profileScale n / (h : ℝ))) :=
    mul_le_mul_of_nonneg_left (add_le_add_left hlogMono 1) hhPos.le
  have hinner :
      2 * ((h + 1 : ℕ) : ℝ) +
          (h : ℝ) *
            (1 + Real.log (profileScale n / ((h + 1 : ℕ) : ℝ))) ≤
        5 * (h : ℝ) *
          (1 + Real.log (profileScale n / (h : ℝ))) := by
    calc
      2 * ((h + 1 : ℕ) : ℝ) +
            (h : ℝ) *
              (1 + Real.log (profileScale n / ((h + 1 : ℕ) : ℝ))) ≤
          4 * (h : ℝ) +
            (h : ℝ) * (1 + Real.log (profileScale n / (h : ℝ))) :=
        add_le_add hearly hlate
      _ ≤ 4 * (h : ℝ) *
            (1 + Real.log (profileScale n / (h : ℝ))) +
          (h : ℝ) * (1 + Real.log (profileScale n / (h : ℝ))) := by
        have hfour : 0 ≤ 4 * (h : ℝ) := by positivity
        have hprod :
            0 ≤ 4 * (h : ℝ) * Real.log (profileScale n / (h : ℝ)) :=
          mul_nonneg hfour hlogNonneg
        nlinarith
      _ = 5 * (h : ℝ) *
          (1 + Real.log (profileScale n / (h : ℝ))) := by ring
  have hfactor : 0 ≤ C / profileScale n ^ 3 := by positivity
  calc
    C / profileScale n ^ 3 *
        (2 * ((h + 1 : ℕ) : ℝ) +
          (h : ℝ) *
            (1 + Real.log (profileScale n / ((h + 1 : ℕ) : ℝ)))) ≤
      C / profileScale n ^ 3 *
        (5 * (h : ℝ) *
          (1 + Real.log (profileScale n / (h : ℝ)))) :=
      mul_le_mul_of_nonneg_left hinner hfactor
    _ = 5 * C * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ))) := by ring

/-- Low spatial shifts: the choice `a=h` yields the logarithmic modulus directly
from the explicit early/late estimates. -/
theorem weightedSupThree_lowShift_log_modulus_of_split
    (n h : ℕ) (C : ℝ) (hC : 0 ≤ C) (hh : 1 ≤ h) (hsmall : h ≤ n / 2)
    (rho early late : Seq) (hsplit : rho = early + late)
    (hearly : WeightedSupThreeLE (profileScale n) early
      (C / profileScale n ^ 3 * ((h + 1 : ℕ) : ℝ)))
    (hlate : WeightedSupThreeLE (profileScale n) (discreteDerivative late)
      (C / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / ((h + 1 : ℕ) : ℝ))))) :
    WeightedSupThreeLE (profileScale n) (rho - (shiftLeft^[h]) rho)
      (5 * C * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ)))) := by
  have htwo := weightedSupThree_twoParameter_log_of_split
    n h h C rho early late hsplit hearly hlate
  exact weightedSupThree_mono (profileScale n) _ _ _ htwo
    (twoParameter_at_shift_le_log_modulus n h C hC hh hsmall)

/-- In the high-shift regime, the crude `L_n⁻²` amplitude bound is already
strong enough for the same logarithmic modulus. -/
theorem weightedSupThree_highShift_log_modulus_of_bound
    (n h : ℕ) (C : ℝ) (hC : 0 ≤ C) (hhigh : n / 2 < h)
    (hhL : h ≤ n + 1) (rho : Seq)
    (hrho : WeightedSupThreeLE (profileScale n) rho
      (C / profileScale n ^ 2)) :
    WeightedSupThreeLE (profileScale n) (rho - (shiftLeft^[h]) rho)
      (5 * C * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ)))) := by
  have hh : 1 ≤ h := by omega
  have hhPos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hh
  have hLPos : 0 < profileScale n := profileScale_pos n
  have hhLReal : (h : ℝ) ≤ profileScale n := by
    simpa only [profileScale] using (show ((h : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by
      exact_mod_cast hhL)
  have hLTwoH : profileScale n ≤ 2 * (h : ℝ) := by
    dsimp [profileScale]
    exact_mod_cast (show n + 1 ≤ 2 * h by omega)
  have hratioOne : 1 ≤ profileScale n / (h : ℝ) :=
    (le_div_iff₀ hhPos).2 (by simpa using hhLReal)
  have hlogNonneg : 0 ≤ Real.log (profileScale n / (h : ℝ)) :=
    Real.log_nonneg hratioOne
  have hcrude :=
    weightedSupThree_sub_shiftLeft_iterate_of_bound
      (profileScale n) (C / profileScale n ^ 2) h hLPos rho hrho
  apply weightedSupThree_mono (profileScale n) _ _ _ hcrude
  have hCL : 0 ≤ 2 * C := by positivity
  have hnum : 2 * C * profileScale n ≤ 4 * C * (h : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hLTwoH hCL]
  have hdenPos : 0 < profileScale n ^ 3 := pow_pos hLPos 3
  calc
    2 * (C / profileScale n ^ 2) =
        (2 * C * profileScale n) / profileScale n ^ 3 := by
      field_simp
      ring
    _ ≤ (4 * C * (h : ℝ)) / profileScale n ^ 3 :=
      (div_le_div_iff_of_pos_right hdenPos).2 hnum
    _ ≤ (5 * C * (h : ℝ)) / profileScale n ^ 3 := by
      apply div_le_div_of_nonneg_right _ hdenPos.le
      nlinarith
    _ ≤ 5 * C * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ))) := by
      have hcoef : 0 ≤ 5 * C * (h : ℝ) / profileScale n ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left
        (show 1 ≤ 1 + Real.log (profileScale n / (h : ℝ)) by linarith) hcoef]

/-- Abstract source-shaped spatial modulus.  The low-shift branch consumes only
the earlier split, early amplitude, and late derivative estimates; the high-shift
branch consumes only the crude pointwise bound. -/
theorem weightedSupThree_log_modulus_of_early_late
    (n h : ℕ) (C : ℝ) (hC : 0 ≤ C) (hh : 1 ≤ h) (hhL : h ≤ n + 1)
    (rho : Seq)
    (hrho : WeightedSupThreeLE (profileScale n) rho
      (C / profileScale n ^ 2))
    (hsplit : ∀ a : ℕ, a ≤ n / 2 →
      ∃ early late : Seq, rho = early + late ∧
        WeightedSupThreeLE (profileScale n) early
          (C / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ)) ∧
        WeightedSupThreeLE (profileScale n) (discreteDerivative late)
          (C / profileScale n ^ 3 *
            (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ))))) :
    WeightedSupThreeLE (profileScale n) (rho - (shiftLeft^[h]) rho)
      (5 * C * (h : ℝ) / profileScale n ^ 3 *
        (1 + Real.log (profileScale n / (h : ℝ)))) := by
  by_cases hsmall : h ≤ n / 2
  · rcases hsplit h hsmall with ⟨early, late, hdecomp, hearly, hlate⟩
    exact weightedSupThree_lowShift_log_modulus_of_split
      n h C hC hh hsmall rho early late hdecomp hearly hlate
  · exact weightedSupThree_highShift_log_modulus_of_bound
      n h C hC (Nat.lt_of_not_ge hsmall) hhL rho hrho

/-- The `h=1` specialization recovers the source-shaped logarithmic gradient
bound from the same non-circular early/late inputs. -/
theorem weightedSupThree_gradient_of_early_late
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (rho : Seq)
    (hrho : WeightedSupThreeLE (profileScale n) rho
      (C / profileScale n ^ 2))
    (hsplit : ∀ a : ℕ, a ≤ n / 2 →
      ∃ early late : Seq, rho = early + late ∧
        WeightedSupThreeLE (profileScale n) early
          (C / profileScale n ^ 3 * ((a + 1 : ℕ) : ℝ)) ∧
        WeightedSupThreeLE (profileScale n) (discreteDerivative late)
          (C / profileScale n ^ 3 *
            (1 + Real.log (profileScale n / ((a + 1 : ℕ) : ℝ))))) :
    WeightedSupThreeLE (profileScale n) (discreteDerivative rho)
      (5 * C / profileScale n ^ 3 * (1 + Real.log (profileScale n))) := by
  have hmod := weightedSupThree_log_modulus_of_early_late
    n 1 C hC (by omega) (by omega) rho hrho hsplit
  simpa [discreteDerivative, shiftLeft] using hmod

end

end DerridaRetaux
