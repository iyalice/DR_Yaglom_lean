import DerridaRetaux.Analysis.SmoothingBounds
import Mathlib.Tactic

/-!
# Orbit-instantiated bounds for the smoothing remainder

This file combines the deterministic estimates in `SmoothingBounds` with the
critical-orbit convolution bounds.  The weighted-mass estimate and the pointwise
estimate `eq:sup` remain explicit theorem parameters.  The conclusions below are
only the algebraic/norm layer of `eq:REbounds`, not the full smoothing proposition.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- The explicit finite-sum witness obtained for the weighted-supremum norm of `E_s`. -/
def densityEOrbitSupMajorant (m s : ℕ) (A B : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 3 (m + 1),
    (Nat.choose m r : ℝ) *
      (((1 + (r - 2) : ℕ) : ℝ) ^ 3 *
        ((B / ((s + 1 : ℕ) : ℝ) ^ 2) *
          (A / ((s + 1 : ℕ) : ℝ)) ^ (r - 1)))

/-- The explicit finite-sum witness obtained for the weighted-`l1` norm of `E_s`. -/
def densityEOrbitL1Majorant (m s : ℕ) (A : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 3 (m + 1),
    (Nat.choose m r : ℝ) *
      (((1 + (r - 2) : ℕ) : ℝ) ^ 3 *
        (A / ((s + 1 : ℕ) : ℝ)) ^ r)

/-- Generation-independent numerator for the order-four bound on `E_s`. -/
def densityEOrbitSupConstant (m : ℕ) (A B : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 3 (m + 1),
    (Nat.choose m r : ℝ) *
      (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * (B * A ^ (r - 1)))

/-- Generation-independent numerator for the order-three weighted-`l1` bound on `E_s`. -/
def densityEOrbitL1Constant (m : ℕ) (A : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 3 (m + 1),
    (Nat.choose m r : ℝ) *
      (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * A ^ r)

/-- An explicit generation-independent numerator for the coarse order-four `R_s` bound. -/
def densityROrbitSupConstant (m : ℕ) (A B : ℝ) : ℝ :=
  let D : ℝ := (Nat.choose m 2 : ℝ)
  let CE := densityEOrbitSupConstant m A B
  let CE1 := densityEOrbitL1Constant m A
  2 * B ^ 2 +
    2 * D * B * A ^ 2 +
    2 * D * B ^ 2 * A +
    D ^ 2 * B * A ^ 3 +
    2 * ((B + D * B * A) * CE1) +
    CE * CE1

/-- The direct six-term majorant obtained after substituting the orbit bounds into `R_s`. -/
def densityROrbitSupMajorant (m s : ℕ) (A B : ℝ) : ℝ :=
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  let D : ℝ := (Nat.choose m 2 : ℝ)
  let ESup := densityEOrbitSupMajorant m s A B
  let EL1 := densityEOrbitL1Majorant m s A
  2 * 1 ^ 2 * (B / L ^ 2) * (B / L ^ 2) +
    2 * 1 * D * ((B / L ^ 2) * (A / L) ^ 2) +
    2 * 1 * D * (B / L ^ 2) * ((B / L ^ 2) * (A / L)) +
    D ^ 2 * ((B / L ^ 2) * (A / L) ^ 3) +
    2 * ((1 * (B / L ^ 2) + D * ((B / L ^ 2) * (A / L))) * EL1) +
    ESup * EL1

/-- The explicit source majorants are nonnegative for nonnegative input constants. -/
theorem densityEOrbitMajorants_nonneg
    (m s : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ densityEOrbitSupMajorant m s A B ∧
      0 ≤ densityEOrbitL1Majorant m s A := by
  constructor
  · apply Finset.sum_nonneg
    intro r hr
    positivity
  · apply Finset.sum_nonneg
    intro r hr
    positivity

/-- The generation-independent numerators are nonnegative. -/
theorem densityEOrbitConstants_nonneg
    (m : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ densityEOrbitSupConstant m A B ∧
      0 ≤ densityEOrbitL1Constant m A := by
  constructor <;> apply Finset.sum_nonneg <;> intro r hr <;> positivity

/-- Increasing a positive denominator exponent decreases a nonnegative quotient. -/
theorem div_pow_le_div_pow_of_exponent_le
    (X L : ℝ) (a b : ℕ) (hX : 0 ≤ X) (hL : 1 ≤ L) (hab : a ≤ b) :
    X / L ^ b ≤ X / L ^ a :=
  div_le_div_of_nonneg_left hX (pow_pos (lt_of_lt_of_le zero_lt_one hL) a)
    (pow_le_pow_right₀ hL hab)

/-- Algebraic normalization of the convolution-power witness. -/
theorem convolutionOrbitRatio_eq (A B L : ℝ) (r : ℕ) :
    (B / L ^ 2) * (A / L) ^ r = (B * A ^ r) / L ^ (r + 2) := by
  simp only [div_pow, div_eq_mul_inv, inv_pow, pow_add]
  ring

/-- The displayed higher-order source majorants have the exact orders used in
`eq:REbounds`. -/
theorem densityEOrbitMajorants_scale
    (m s : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    densityEOrbitSupMajorant m s A B ≤
        densityEOrbitSupConstant m A B / ((s + 1 : ℕ) : ℝ) ^ 4 ∧
      densityEOrbitL1Majorant m s A ≤
        densityEOrbitL1Constant m A / ((s + 1 : ℕ) : ℝ) ^ 3 := by
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  have hScale : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hScale
  constructor
  · rw [densityEOrbitSupMajorant, densityEOrbitSupConstant]
    calc
      ∑ r ∈ Finset.Ico 3 (m + 1),
          (Nat.choose m r : ℝ) *
            (((1 + (r - 2) : ℕ) : ℝ) ^ 3 *
              ((B / L ^ 2) * (A / L) ^ (r - 1))) ≤
          ∑ r ∈ Finset.Ico 3 (m + 1),
            (Nat.choose m r : ℝ) *
              (((1 + (r - 2) : ℕ) : ℝ) ^ 3 *
                ((B * A ^ (r - 1)) / L ^ 4)) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrLower : 3 ≤ r := (Finset.mem_Ico.mp hr).1
        have hpow := div_pow_le_div_pow_of_exponent_le
          (A ^ (r - 1)) L 2 (r - 1) (pow_nonneg hA _) hScale (by omega)
        have hratio :
            (B / L ^ 2) * (A / L) ^ (r - 1) ≤
              (B * A ^ (r - 1)) / L ^ 4 := by
          rw [div_pow]
          calc
            (B / L ^ 2) * (A ^ (r - 1) / L ^ (r - 1)) ≤
                (B / L ^ 2) * (A ^ (r - 1) / L ^ 2) :=
              mul_le_mul_of_nonneg_left hpow (div_nonneg hB (sq_nonneg L))
            _ = (B * A ^ (r - 1)) / L ^ 4 := by
              simp only [div_eq_mul_inv, inv_pow]
              ring
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hratio (pow_nonneg (by positivity) 3))
          (by positivity)
      _ = (∑ r ∈ Finset.Ico 3 (m + 1),
            (Nat.choose m r : ℝ) *
              (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * (B * A ^ (r - 1)))) /
          L ^ 4 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r hr
        simp only [div_eq_mul_inv, inv_pow]
        ring
  · rw [densityEOrbitL1Majorant, densityEOrbitL1Constant]
    calc
      ∑ r ∈ Finset.Ico 3 (m + 1),
          (Nat.choose m r : ℝ) *
            (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * (A / L) ^ r) ≤
          ∑ r ∈ Finset.Ico 3 (m + 1),
            (Nat.choose m r : ℝ) *
              (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * (A ^ r / L ^ 3)) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrLower : 3 ≤ r := (Finset.mem_Ico.mp hr).1
        have hpow := div_pow_le_div_pow_of_exponent_le
          (A ^ r) L 3 r (pow_nonneg hA _) hScale hrLower
        rw [div_pow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (pow_nonneg (by positivity) 3))
          (by positivity)
      _ = (∑ r ∈ Finset.Ico 3 (m + 1),
            (Nat.choose m r : ℝ) *
              (((1 + (r - 2) : ℕ) : ℝ) ^ 3 * A ^ r)) / L ^ 3 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r hr
        simp only [div_eq_mul_inv, inv_pow]
        ring

/-- Every density coefficient is nonnegative and bounded by its binomial coefficient.
The bound uses only criticality and `m ≥ 2`; it is uniform in the law. -/
theorem densityCoeff_nonneg_and_le_choose
    (m r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    0 ≤ densityCoeff m r p ∧ densityCoeff m r p ≤ (Nat.choose m r : ℝ) := by
  have hmOne : 1 ≤ m := by omega
  have hx0 : 0 ≤ zeroTilt m p := normalizedTilt_nonneg m p hmOne hcrit 0
  have hx1 : zeroTilt m p ≤ 1 := zeroTilt_le_one m p hmOne hcrit
  have hbase : (1 : ℝ) ≤ (m : ℝ) - 1 := by
    exact_mod_cast (show 1 ≤ m - 1 by omega)
  have hdenom :
      1 ≤ tiltDenom m p * ((m : ℝ) - 1) ^ (r - 1) :=
    one_le_mul_of_one_le_of_one_le (tiltDenom_one_le m p hmOne hcrit)
      (one_le_pow₀ hbase)
  have hchoose : 0 ≤ (Nat.choose m r : ℝ) := by positivity
  have hpow0 : 0 ≤ zeroTilt m p ^ (m - r) := pow_nonneg hx0 _
  have hpow1 : zeroTilt m p ^ (m - r) ≤ 1 := pow_le_one₀ hx0 hx1
  have hnum0 : 0 ≤ (Nat.choose m r : ℝ) * zeroTilt m p ^ (m - r) :=
    mul_nonneg hchoose hpow0
  have hnumLe :
      (Nat.choose m r : ℝ) * zeroTilt m p ^ (m - r) ≤ (Nat.choose m r : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow1 hchoose
  constructor
  · rw [densityCoeff]
    exact div_nonneg hnum0 (zero_le_one.trans hdenom)
  · rw [densityCoeff]
    exact (div_le_self hnum0 hdenom).trans hnumLe

/-- Absolute-value form of the uniform binomial density-coefficient bound. -/
theorem abs_densityCoeff_le_choose
    (m r : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    |densityCoeff m r p| ≤ (Nat.choose m r : ℝ) := by
  rw [abs_of_nonneg (densityCoeff_nonneg_and_le_choose m r p hm hcrit).1]
  exact (densityCoeff_nonneg_and_le_choose m r p hm hcrit).2

/-- The pointwise input `eq:sup` gives the required boundary coefficient bound. -/
theorem abs_densityBeta_orbit_le_of_pointwise
    (m : ℕ) (p₀ : ProbabilityMass) (B : ℝ)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) (s : ℕ) :
    |densityBeta m p₀ s| ≤ B / ((s + 1 : ℕ) : ℝ) ^ 2 := by
  have hs := hSup s 0
  simpa [densityBeta, cubicWeight] using hs

/-- The transport and quadratic coefficients have the uniform bounds needed by `R_s`. -/
theorem smoothing_coefficients_orbit_bounds
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀) (s : ℕ) :
    |transportCoeff m (orbit m p₀ s)| ≤ 1 ∧
      |densityD m p₀ s| ≤ (Nat.choose m 2 : ℝ) := by
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  constructor
  · rw [abs_of_nonneg (transportCoeff_nonneg m (orbit m p₀ s) (by omega) hscrit)]
    exact transportCoeff_le_one m (orbit m p₀ s) (by omega) hscrit
  · simpa only [densityD] using
      abs_densityCoeff_le_choose m 2 (orbit m p₀ s) hm hscrit

/-- Orbit-instantiated finite-sum weighted-supremum bound for the higher-order source
`E_s`.  Its convolution bounds are derived from the explicit weighted-mass and
`eq:sup` assumptions. -/
theorem densityE_orbit_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) (s : ℕ) :
    WeightedSupThreeLE ((s + 1 : ℕ) : ℝ) (densityE m p₀ s)
      (densityEOrbitSupMajorant m s A B) := by
  have hpowers := weightedConvolutionPowers_orbit_bounds
    m p₀ hm hcrit hthird A B hA hB hL1 hSup
  have hScale : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  apply densityE_weightedSup_bound m p₀ s ((s + 1 : ℕ) : ℝ) hScale
    (fun r ↦ (Nat.choose m r : ℝ))
    (fun r ↦ (B / ((s + 1 : ℕ) : ℝ) ^ 2) *
      (A / ((s + 1 : ℕ) : ℝ)) ^ (r - 1))
  · intro r hr
    positivity
  · intro r hr
    exact abs_densityCoeff_le_choose m r (orbit m p₀ s) hm
      (orbit_critical m p₀ (by omega) hcrit s)
  · intro r hr
    have hrLower : 3 ≤ r := (Finset.mem_Ico.mp hr).1
    simpa only [show r - 1 + 1 = r by omega] using (hpowers s (r - 1)).2

/-- Orbit-instantiated finite-sum weighted-`l1` bound for `E_s`. -/
theorem densityE_orbit_weightedL1_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) (s : ℕ) :
    weightedL1Three ((s + 1 : ℕ) : ℝ) (densityE m p₀ s) ≤
      densityEOrbitL1Majorant m s A := by
  have hpowers := weightedConvolutionPowers_orbit_bounds
    m p₀ hm hcrit hthird A B hA hB hL1 hSup
  have hbaseSum := weightedAbs_positiveTiltedDensity_orbit_summable
    m p₀ hm hcrit hthird s
  have hScale : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  apply densityE_weightedL1_bound m p₀ s ((s + 1 : ℕ) : ℝ) hScale
    (fun r ↦ (Nat.choose m r : ℝ))
    (fun r ↦ (A / ((s + 1 : ℕ) : ℝ)) ^ r)
  · intro r hr
    positivity
  · intro r hr
    exact abs_densityCoeff_le_choose m r (orbit m p₀ s) hm
      (orbit_critical m p₀ (by omega) hcrit s)
  · intro r hr
    exact weightedAbs_convPow_summable ((s + 1 : ℕ) : ℝ) hScale _ hbaseSum r
  · intro r hr
    exact (hpowers s r).1

/-- Source-shaped order-four weighted-supremum estimate for `E_s`. -/
theorem densityE_orbit_weightedSup_order_four
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) (s : ℕ) :
    WeightedSupThreeLE ((s + 1 : ℕ) : ℝ) (densityE m p₀ s)
      (densityEOrbitSupConstant m A B / ((s + 1 : ℕ) : ℝ) ^ 4) := by
  apply weightedSupThree_mono ((s + 1 : ℕ) : ℝ)
    (densityEOrbitSupMajorant m s A B) _ (densityE m p₀ s)
  · exact densityE_orbit_weightedSup_bound
      m p₀ hm hcrit hthird A B hA hB hL1 hSup s
  · exact (densityEOrbitMajorants_scale m s A B hA hB).1

/-- Source-shaped order-three weighted-`l1` estimate for `E_s`. -/
theorem densityE_orbit_weightedL1_order_three
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) (s : ℕ) :
    weightedL1Three ((s + 1 : ℕ) : ℝ) (densityE m p₀ s) ≤
      densityEOrbitL1Constant m A / ((s + 1 : ℕ) : ℝ) ^ 3 := by
  exact (densityE_orbit_weightedL1_bound
    m p₀ hm hcrit hthird A B hA hB hL1 hSup s).trans
      (densityEOrbitMajorants_scale m s A B hA hB).2

/-- The higher-order source is weighted-summable on every finite critical generation. -/
theorem densityE_orbit_weightedAbs_summable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀) (s : ℕ) :
    Summable (weightedAbs ((s + 1 : ℕ) : ℝ) (densityE m p₀ s)) := by
  have hbaseSum := weightedAbs_positiveTiltedDensity_orbit_summable
    m p₀ hm hcrit hthird s
  have hScale : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  apply densityE_weightedAbs_summable m p₀ s ((s + 1 : ℕ) : ℝ) hScale
  intro r hr
  exact weightedAbs_convPow_summable ((s + 1 : ℕ) : ℝ) hScale _ hbaseSum r

/-- Complete orbit-instantiated six-term weighted-supremum estimate for `R_s`.
Every convolution-power input is supplied by `weightedConvolutionPowers_orbit_bounds`;
the only asymptotic hypotheses are the displayed weighted-mass and `eq:sup` bounds. -/
theorem densityR_orbit_weightedSup_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) (s : ℕ) :
    WeightedSupThreeLE ((s + 1 : ℕ) : ℝ) (densityR m p₀ s)
      (densityROrbitSupMajorant m s A B) := by
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  let D : ℝ := (Nat.choose m 2 : ℝ)
  let RhoSup : ℝ := B / L ^ 2
  let BSup : ℝ := (B / L ^ 2) * (A / L)
  let ConvThreeSup : ℝ := (B / L ^ 2) * (A / L) ^ 2
  let ConvFourSup : ℝ := (B / L ^ 2) * (A / L) ^ 3
  let ESup : ℝ := densityEOrbitSupMajorant m s A B
  let EL1 : ℝ := densityEOrbitL1Majorant m s A
  have hScale : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have hpowers := weightedConvolutionPowers_orbit_bounds
    m p₀ hm hcrit hthird A B hA hB hL1 hSup
  have hcoeff := smoothing_coefficients_orbit_bounds m p₀ hm hcrit s
  have hbeta := abs_densityBeta_orbit_le_of_pointwise m p₀ B hSup s
  have hrho : WeightedSupThreeLE L
      (positiveTiltedDensity m (orbit m p₀ s)) RhoSup := by
    simpa only [L, RhoSup] using hSup s
  have hBconv : WeightedSupThreeLE L (densityB m p₀ s) BSup := by
    simpa [L, BSup, densityB, convPow_two_eq] using (hpowers s 1).2
  have hthree : WeightedSupThreeLE L
      (convPow 3 (positiveTiltedDensity m (orbit m p₀ s))) ConvThreeSup := by
    simpa only [L, ConvThreeSup] using (hpowers s 2).2
  have hfour : WeightedSupThreeLE L
      (convPow 4 (positiveTiltedDensity m (orbit m p₀ s))) ConvFourSup := by
    simpa only [L, ConvFourSup] using (hpowers s 3).2
  have hE : WeightedSupThreeLE L (densityE m p₀ s) ESup := by
    simpa only [L, ESup] using
      densityE_orbit_weightedSup_bound m p₀ hm hcrit hthird A B hA hB hL1 hSup s
  have hESum : Summable (weightedAbs L (densityE m p₀ s)) := by
    simpa only [L] using densityE_orbit_weightedAbs_summable m p₀ hm hcrit hthird s
  have hEL1Bound : weightedL1Three L (densityE m p₀ s) ≤ EL1 := by
    simpa only [L, EL1] using
      densityE_orbit_weightedL1_bound m p₀ hm hcrit hthird A B hA hB hL1 hSup s
  have hENonneg := densityEOrbitMajorants_nonneg m s A B hA hB
  have hresult := densityR_weightedSup_bound_of_component_bounds
    m p₀ s L hScale 1 D RhoSup RhoSup BSup ConvThreeSup ConvFourSup ESup EL1
    zero_le_one (by dsimp only [D]; positivity)
    (by dsimp only [RhoSup, L]; positivity)
    (by dsimp only [BSup, L]; positivity)
    (by dsimp only [ConvThreeSup, L]; positivity)
    (by dsimp only [ConvFourSup, L]; positivity)
    (by simpa only [ESup] using hENonneg.1)
    hcoeff.1 hcoeff.2 (by simpa only [RhoSup, L] using hbeta)
    hrho hBconv hthree hfour hE hESum hEL1Bound
  simpa only [densityROrbitSupMajorant, L, D, RhoSup, BSup, ConvThreeSup,
    ConvFourSup, ESup, EL1] using hresult

/-- The complete six-term remainder has the source order `L_s⁻⁴`, with an explicit
generation-independent numerator.  This remains conditional precisely on the displayed
weighted-mass and `eq:sup` inputs. -/
theorem densityR_orbit_weightedSup_order_four
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ n)) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) (s : ℕ) :
    WeightedSupThreeLE ((s + 1 : ℕ) : ℝ) (densityR m p₀ s)
      (densityROrbitSupConstant m A B / ((s + 1 : ℕ) : ℝ) ^ 4) := by
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  let D : ℝ := (Nat.choose m 2 : ℝ)
  let CE : ℝ := densityEOrbitSupConstant m A B
  let CE1 : ℝ := densityEOrbitL1Constant m A
  let RhoSup : ℝ := B / L ^ 2
  let BSup : ℝ := (B * A) / L ^ 2
  let ConvThreeSup : ℝ := (B * A ^ 2) / L ^ 4
  let ConvFourSup : ℝ := (B * A ^ 3) / L ^ 4
  let ESup : ℝ := CE / L ^ 2
  let EL1 : ℝ := CE1 / L ^ 2
  have hScale : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have hconstants := densityEOrbitConstants_nonneg m A B hA hB
  have hCE : 0 ≤ CE := by simpa only [CE] using hconstants.1
  have hCE1 : 0 ≤ CE1 := by simpa only [CE1] using hconstants.2
  have hpowers := weightedConvolutionPowers_orbit_bounds
    m p₀ hm hcrit hthird A B hA hB hL1 hSup
  have hcoeff := smoothing_coefficients_orbit_bounds m p₀ hm hcrit s
  have hbeta := abs_densityBeta_orbit_le_of_pointwise m p₀ B hSup s
  have hrho : WeightedSupThreeLE L
      (positiveTiltedDensity m (orbit m p₀ s)) RhoSup := by
    simpa only [L, RhoSup] using hSup s
  have hBexact : WeightedSupThreeLE L (densityB m p₀ s)
      ((B / L ^ 2) * (A / L)) := by
    simpa [L, densityB, convPow_two_eq] using (hpowers s 1).2
  have hBconv : WeightedSupThreeLE L (densityB m p₀ s) BSup := by
    apply weightedSupThree_mono L ((B / L ^ 2) * (A / L)) BSup _ hBexact
    dsimp only [BSup]
    calc
      (B / L ^ 2) * (A / L) = (B * A) / L ^ 3 := by
        simpa using convolutionOrbitRatio_eq A B L 1
      _ ≤ (B * A) / L ^ 2 :=
        div_pow_le_div_pow_of_exponent_le (B * A) L 2 3
          (mul_nonneg hB hA) hScale (by omega)
  have hthree : WeightedSupThreeLE L
      (convPow 3 (positiveTiltedDensity m (orbit m p₀ s))) ConvThreeSup := by
    simpa [L, ConvThreeSup, convolutionOrbitRatio_eq] using (hpowers s 2).2
  have hfourExact : WeightedSupThreeLE L
      (convPow 4 (positiveTiltedDensity m (orbit m p₀ s)))
      ((B * A ^ 3) / L ^ 5) := by
    simpa [L, convolutionOrbitRatio_eq] using (hpowers s 3).2
  have hfour : WeightedSupThreeLE L
      (convPow 4 (positiveTiltedDensity m (orbit m p₀ s))) ConvFourSup := by
    apply weightedSupThree_mono L ((B * A ^ 3) / L ^ 5) ConvFourSup _ hfourExact
    dsimp only [ConvFourSup]
    exact div_pow_le_div_pow_of_exponent_le (B * A ^ 3) L 4 5
      (mul_nonneg hB (pow_nonneg hA _)) hScale (by omega)
  have hEfour : WeightedSupThreeLE L (densityE m p₀ s) (CE / L ^ 4) := by
    simpa only [L, CE] using
      densityE_orbit_weightedSup_order_four
        m p₀ hm hcrit hthird A B hA hB hL1 hSup s
  have hE : WeightedSupThreeLE L (densityE m p₀ s) ESup := by
    apply weightedSupThree_mono L (CE / L ^ 4) ESup _ hEfour
    dsimp only [ESup]
    exact div_pow_le_div_pow_of_exponent_le CE L 2 4 hCE hScale (by omega)
  have hESum : Summable (weightedAbs L (densityE m p₀ s)) := by
    simpa only [L] using densityE_orbit_weightedAbs_summable m p₀ hm hcrit hthird s
  have hEL1three : weightedL1Three L (densityE m p₀ s) ≤ CE1 / L ^ 3 := by
    simpa only [L, CE1] using
      densityE_orbit_weightedL1_order_three
        m p₀ hm hcrit hthird A B hA hB hL1 hSup s
  have hEL1Bound : weightedL1Three L (densityE m p₀ s) ≤ EL1 := by
    exact hEL1three.trans (by
      dsimp only [EL1]
      exact div_pow_le_div_pow_of_exponent_le CE1 L 2 3 hCE1 hScale (by omega))
  have hresult := densityR_weightedSup_bound_of_component_bounds
    m p₀ s L hScale 1 D RhoSup RhoSup BSup ConvThreeSup ConvFourSup ESup EL1
    zero_le_one (by dsimp only [D]; positivity)
    (by dsimp only [RhoSup]; positivity)
    (by dsimp only [BSup]; positivity)
    (by dsimp only [ConvThreeSup]; positivity)
    (by dsimp only [ConvFourSup]; positivity)
    (by dsimp only [ESup]; positivity)
    hcoeff.1 hcoeff.2 (by simpa only [L, RhoSup] using hbeta)
    hrho hBconv hthree hfour hE hESum hEL1Bound
  have hfinal : WeightedSupThreeLE L (densityR m p₀ s)
      (densityROrbitSupConstant m A B / L ^ 4) := by
    apply weightedSupThree_mono L _ _ _ hresult
    dsimp only [RhoSup, BSup, ConvThreeSup, ConvFourSup, ESup, EL1,
      densityROrbitSupConstant, D, CE, CE1]
    simp only [div_eq_mul_inv, inv_pow]
    ring_nf
    exact le_rfl
  simpa only [L] using hfinal

/-- Source-facing `eq:REbounds` package from the two approved H1 inputs and the
still-explicit pointwise estimate `eq:sup`.  This theorem supplies only `E_s` and
`R_s` norm bounds; it does not assert the gradient, modulus, or profile conclusions. -/
theorem smoothingRemainders_orbit_of_H1_and_pointwise
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant)
    (B : ℝ) (hB : 0 ≤ B)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ,
      WeightedSupThreeLE ((s + 1 : ℕ) : ℝ) (densityE m p₀ s)
          (densityEOrbitSupConstant m A B / ((s + 1 : ℕ) : ℝ) ^ 4) ∧
        weightedL1Three ((s + 1 : ℕ) : ℝ) (densityE m p₀ s) ≤
          densityEOrbitL1Constant m A / ((s + 1 : ℕ) : ℝ) ^ 3 ∧
        WeightedSupThreeLE ((s + 1 : ℕ) : ℝ) (densityR m p₀ s)
          (densityROrbitSupConstant m A B / ((s + 1 : ℕ) : ℝ) ^ 4) := by
  rcases weightedL1Three_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with ⟨A, hA, hL1⟩
  refine ⟨A, hA, fun s ↦ ⟨?_, ?_, ?_⟩⟩
  · exact densityE_orbit_weightedSup_order_four
      m p₀ hm hcrit hthird A B hA.le hB hL1 hSup s
  · exact densityE_orbit_weightedL1_order_three
      m p₀ hm hcrit hthird A B hA.le hB hL1 hSup s
  · exact densityR_orbit_weightedSup_order_four
      m p₀ hm hcrit hthird A B hA.le hB hL1 hSup s

end

end DerridaRetaux
