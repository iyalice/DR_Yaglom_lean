import DerridaRetaux.Analysis.ReadoutBounds
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators
open Asymptotics
open Filter

namespace DerridaRetaux

/-!
# Conditional geometric approximation and total variation

This file isolates the normalization calculation in source `U17` and `eq:tv`.
All quotients by the readout normalization are used only after an explicit proof
that the normalization is positive.
-/

noncomputable section

/-- The geometric target on shifted positive indices: index `j` represents `X = j + 1`. -/
def shiftedGeometricMass (m : ℕ) : Seq :=
  fun j ↦ ((m : ℝ) - 1) * ((m : ℝ) ^ (j + 1))⁻¹

/-- Normalize a density using its geometrically weighted readout. -/
def normalizedReadoutMass (m : ℕ) (f : Seq) (a : ℝ) : Seq :=
  fun j ↦ ((m : ℝ) ^ (j + 1))⁻¹ * f j / a

/-- Unbundled `ℓ¹` distance for summable real mass functions. -/
def discreteL1Distance (u v : Seq) : ℝ :=
  ∑' j : ℕ, |u j - v j|

/-- Conventional total variation for discrete mass functions: one half of `ℓ¹`. -/
def discreteTotalVariation (u v : Seq) : ℝ :=
  (1 / 2 : ℝ) * discreteL1Distance u v

/-- The manuscript's `ℓ¹` normalization error for a generic readout density. -/
def normalizedReadoutL1Error (m : ℕ) (f : Seq) (a : ℝ) : ℝ :=
  discreteL1Distance (normalizedReadoutMass m f a) (shiftedGeometricMass m)

/-- The conditional original-law mass on shifted positive indices. -/
def conditionalPositiveMass (p : ProbabilityMass) : Seq :=
  fun j ↦ p (j + 1) / survival p

/-- The manuscript's conditional `ℓ¹` error from `eq:tv`. -/
def conditionalPositiveL1Error (m : ℕ) (p : ProbabilityMass) : ℝ :=
  discreteL1Distance (conditionalPositiveMass p) (shiftedGeometricMass m)

/-- Conventional total variation for the two conditional distributions in `eq:tv`. -/
def conditionalPositiveTotalVariation (m : ℕ) (p : ProbabilityMass) : ℝ :=
  discreteTotalVariation (conditionalPositiveMass p) (shiftedGeometricMass m)

/-- Every discrete `ℓ¹` distance is nonnegative. -/
theorem discreteL1Distance_nonneg (u v : Seq) : 0 ≤ discreteL1Distance u v := by
  exact tsum_nonneg fun j ↦ abs_nonneg (u j - v j)

/-- Nonnegativity of the manuscript's conditional `ℓ¹` error. -/
theorem conditionalPositiveL1Error_nonneg (m : ℕ) (p : ProbabilityMass) :
    0 ≤ conditionalPositiveL1Error m p :=
  discreteL1Distance_nonneg _ _

/-- Any pointwise absolute-value upper bound is automatically nonnegative. -/
theorem supLE_bound_nonneg (f : Seq) (B : ℝ) (h : SupLE f B) : 0 ≤ B :=
  (abs_nonneg (f 0)).trans (h 0)

/-- The shifted geometric target is a probability mass function. -/
theorem shiftedGeometricMass_hasSum (m : ℕ) (hm : 2 ≤ m) :
    HasSum (shiftedGeometricMass m) 1 := by
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have h := (inversePower_succ_hasSum m hm).mul_left ((m : ℝ) - 1)
  convert h using 1
  field_simp [hfactor]

/-- A positive readout normalization produces a normalized shifted mass function. -/
theorem normalizedReadoutMass_hasSum
    (m : ℕ) (f : Seq) (a : ℝ) (ha : 0 < a)
    (hreadout : HasSum (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹ * f j) a) :
    HasSum (normalizedReadoutMass m f a) 1 := by
  have h := hreadout.div_const a
  convert h using 1
  field_simp [ha.ne']

/-- The normalized readout mass is pointwise nonnegative when the density is. -/
theorem normalizedReadoutMass_nonneg
    (m : ℕ) (f : Seq) (a : ℝ) (ha : 0 < a) (hf : ∀ j : ℕ, 0 ≤ f j)
    (j : ℕ) :
    0 ≤ normalizedReadoutMass m f a j := by
  exact div_nonneg (mul_nonneg (by positivity) (hf j)) ha.le

/-- The exact geometric first-moment expression used in the `ℓ¹` estimate. -/
theorem inversePower_succ_mul_normalizationCost_hasSum (m : ℕ) (hm : 2 ≤ m) :
    HasSum
      (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹ *
        ((j : ℝ) + 1 / ((m : ℝ) - 1)))
      (2 / ((m : ℝ) - 1) ^ 2) := by
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hfirst := nat_mul_inversePower_succ_hasSum m hm
  have hzero := (inversePower_succ_hasSum m hm).mul_left (1 / ((m : ℝ) - 1))
  have hsum := hfirst.add hzero
  convert hsum using 1
  · funext j
    ring
  · field_simp [hfactor]
    ring

/-- First normalization inequality in `U17`, specialized to the existing `rho` readout. -/
theorem survivalReadout_sub_boundary_le
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (B : ℝ) (hdelta : SupLE (discreteDerivative (rho m p)) B) :
    |survivalReadout m p - rho m p 0 / ((m : ℝ) - 1)| ≤
      B / ((m : ℝ) - 1) ^ 2 := by
  have hmOne : 1 ≤ m := by omega
  have hB := supLE_bound_nonneg (discreteDerivative (rho m p)) B hdelta
  apply geometricReadout_sub_boundary_le m hm (rho m p) (survivalReadout m p)
    B hB hdelta
  simpa [survivalReadout] using
    (survivalReadout_hasSum m p hmOne hcrit).summable.hasSum

/-- Generic second normalization inequality: every density value is close to the
The constant `(m-1) a`, with the exact linear cost used in the manuscript. -/
theorem abs_sub_tiltFactor_mul_readout_le
    (m : ℕ) (hm : 2 ≤ m) (f : Seq) (a B : ℝ)
    (hdelta : SupLE (discreteDerivative f) B)
    (hreadout : HasSum (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹ * f j) a)
    (j : ℕ) :
    |f j - ((m : ℝ) - 1) * a| ≤
      B * ((j : ℝ) + 1 / ((m : ℝ) - 1)) := by
  have hB := supLE_bound_nonneg (discreteDerivative f) B hdelta
  have hfactor : 0 < (m : ℝ) - 1 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hboundary := geometricReadout_sub_boundary_le
    m hm f a B hB hdelta hreadout
  have hboundaryScaled :
      |f 0 - ((m : ℝ) - 1) * a| ≤ B / ((m : ℝ) - 1) := by
    have heq :
        f 0 - ((m : ℝ) - 1) * a =
          -((m : ℝ) - 1) * (a - f 0 / ((m : ℝ) - 1)) := by
      field_simp [hfactor.ne']
      ring
    rw [heq, abs_mul, abs_neg, abs_of_pos hfactor]
    calc
      ((m : ℝ) - 1) * |a - f 0 / ((m : ℝ) - 1)| ≤
          ((m : ℝ) - 1) * (B / ((m : ℝ) - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hboundary hfactor.le
      _ = B / ((m : ℝ) - 1) := by
        field_simp [hfactor.ne']
        ring
  have hj := abs_sub_zero_le_of_discreteDerivative f B hB hdelta j
  calc
    |f j - ((m : ℝ) - 1) * a| =
        |(f j - f 0) + (f 0 - ((m : ℝ) - 1) * a)| := by ring_nf
    _ ≤ |f j - f 0| + |f 0 - ((m : ℝ) - 1) * a| := abs_add _ _
    _ ≤ (j : ℝ) * B + B / ((m : ℝ) - 1) := add_le_add hj hboundaryScaled
    _ = B * ((j : ℝ) + 1 / ((m : ℝ) - 1)) := by ring

/-- Second normalization inequality in the source's `k ≥ 1` indexing. -/
theorem rho_sub_tiltFactor_mul_survivalReadout_le
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (B : ℝ) (hdelta : SupLE (discreteDerivative (rho m p)) B)
    (k : ℕ) (hk : 1 ≤ k) :
    |rho m p (k - 1) - ((m : ℝ) - 1) * survivalReadout m p| ≤
      B * ((k : ℝ) - 1 + 1 / ((m : ℝ) - 1)) := by
  have hmOne : 1 ≤ m := by omega
  convert abs_sub_tiltFactor_mul_readout_le m hm (rho m p) (survivalReadout m p)
    B hdelta (by simpa [survivalReadout] using
      (survivalReadout_hasSum m p hmOne hcrit).summable.hasSum) (k - 1) using 1
  rw [Nat.cast_sub hk]
  norm_num

/-- Exact `ℓ¹` consequence of the two normalization inequalities.  The readout
normalization is proved positive before any cancellation by `a`. -/
theorem normalizedReadoutL1Error_le
    (m : ℕ) (hm : 2 ≤ m) (f : Seq) (a B : ℝ) (ha : 0 < a)
    (hdelta : SupLE (discreteDerivative f) B)
    (hreadout : HasSum (fun j : ℕ ↦ ((m : ℝ) ^ (j + 1))⁻¹ * f j) a) :
    normalizedReadoutL1Error m f a ≤
      (2 * B) / (a * ((m : ℝ) - 1) ^ 2) := by
  have hB := supLE_bound_nonneg (discreteDerivative f) B hdelta
  have hfactor : 0 < (m : ℝ) - 1 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hpoint : ∀ j : ℕ,
      |normalizedReadoutMass m f a j - shiftedGeometricMass m j| ≤
        (B / a) * (((m : ℝ) ^ (j + 1))⁻¹ *
          ((j : ℝ) + 1 / ((m : ℝ) - 1))) := by
    intro j
    have hscale : 0 ≤ ((m : ℝ) ^ (j + 1))⁻¹ / a :=
      div_nonneg (by positivity) ha.le
    have hvalue := abs_sub_tiltFactor_mul_readout_le
      m hm f a B hdelta hreadout j
    have heq :
        normalizedReadoutMass m f a j - shiftedGeometricMass m j =
          (((m : ℝ) ^ (j + 1))⁻¹ / a) *
            (f j - ((m : ℝ) - 1) * a) := by
      simp only [normalizedReadoutMass, shiftedGeometricMass]
      field_simp [ha.ne']
      ring
    rw [heq, abs_mul, abs_of_nonneg hscale]
    calc
      ((m : ℝ) ^ (j + 1))⁻¹ / a * |f j - ((m : ℝ) - 1) * a| ≤
          ((m : ℝ) ^ (j + 1))⁻¹ / a *
            (B * ((j : ℝ) + 1 / ((m : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hvalue hscale
      _ = (B / a) * (((m : ℝ) ^ (j + 1))⁻¹ *
          ((j : ℝ) + 1 / ((m : ℝ) - 1))) := by ring
  have hmajor :=
    (inversePower_succ_mul_normalizationCost_hasSum m hm).mul_left (B / a)
  have hmajor' :
      HasSum
        (fun j : ℕ ↦ (B / a) * (((m : ℝ) ^ (j + 1))⁻¹ *
          ((j : ℝ) + 1 / ((m : ℝ) - 1))))
        ((2 * B) / (a * ((m : ℝ) - 1) ^ 2)) := by
    convert hmajor using 1
    field_simp [ha.ne', hfactor.ne']
    ring
  have herrorSummable :
      Summable (fun j : ℕ ↦
        |normalizedReadoutMass m f a j - shiftedGeometricMass m j|) :=
    hmajor'.summable.of_nonneg_of_le (fun j ↦ abs_nonneg _) hpoint
  rw [normalizedReadoutL1Error, discreteL1Distance]
  calc
    (∑' j : ℕ, |normalizedReadoutMass m f a j - shiftedGeometricMass m j|) ≤
        ∑' j : ℕ, (B / a) * (((m : ℝ) ^ (j + 1))⁻¹ *
          ((j : ℝ) + 1 / ((m : ℝ) - 1))) :=
      Summable.tsum_le_tsum hpoint herrorSummable hmajor'.summable
    _ = (2 * B) / (a * ((m : ℝ) - 1) ^ 2) := hmajor'.tsum_eq

/-- Manuscript specialization of the explicit `ℓ¹` bound to the existing `rho`
and `survivalReadout`. -/
theorem rho_normalizedReadoutL1Error_le
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (B : ℝ) (ha : 0 < survivalReadout m p)
    (hdelta : SupLE (discreteDerivative (rho m p)) B) :
    normalizedReadoutL1Error m (rho m p) (survivalReadout m p) ≤
      (2 * B) /
        (survivalReadout m p * ((m : ℝ) - 1) ^ 2) := by
  have hmOne : 1 ≤ m := by omega
  apply normalizedReadoutL1Error_le m hm (rho m p) (survivalReadout m p) B
    ha hdelta
  simpa [survivalReadout] using
    (survivalReadout_hasSum m p hmOne hcrit).summable.hasSum

/-- Positive survival implies positivity of the readout normalization `a`. -/
theorem survivalReadout_pos_of_survival_pos
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (hsurvival : 0 < survival p) :
    0 < survivalReadout m p := by
  have hmOne : 1 ≤ m := by omega
  have hG := normalizedTilt_denominator_pos m p hmOne hcrit
  have hfactor := critical_tiltFactor_pos m p hmOne hcrit
  have hreadout := survival_eq_partition_mul_readout m p hm hcrit
  rw [hreadout] at hsurvival
  have hscale : 0 < tiltedPartition m p / ((m : ℝ) - 1) :=
    div_pos hG hfactor
  nlinarith

/-- Conversely, a positive readout normalization gives positive survival. -/
theorem survival_pos_of_survivalReadout_pos
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (ha : 0 < survivalReadout m p) :
    0 < survival p := by
  have hmOne : 1 ≤ m := by omega
  have hG := normalizedTilt_denominator_pos m p hmOne hcrit
  have hfactor := critical_tiltFactor_pos m p hmOne hcrit
  rw [survival_eq_partition_mul_readout m p hm hcrit]
  exact mul_pos (div_pos hG hfactor) ha

/-- The normalized rho readout is exactly the shifted conditional original law. -/
theorem conditionalPositiveMass_eq_normalizedReadoutMass
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (hsurvival : 0 < survival p) (j : ℕ) :
    conditionalPositiveMass p j =
      normalizedReadoutMass m (rho m p) (survivalReadout m p) j := by
  have hmOne : 1 ≤ m := by omega
  have hG := normalizedTilt_denominator_pos m p hmOne hcrit
  have hfactor := critical_tiltFactor_pos m p hmOne hcrit
  have ha := survivalReadout_pos_of_survival_pos m p hm hcrit hsurvival
  rw [conditionalPositiveMass, normalizedReadoutMass,
    atom_eq_partition_mul_rho m p hm hcrit (j + 1) (by omega),
    survival_eq_partition_mul_readout m p hm hcrit]
  field_simp [hG.ne', hfactor.ne', ha.ne']
  ring

/-- Under positive survival, the shifted conditional mass is normalized. -/
theorem conditionalPositiveMass_hasSum
    (p : ProbabilityMass) (hsurvival : 0 < survival p) :
    HasSum (conditionalPositiveMass p) 1 := by
  have h := (survival_hasSum p).div_const (survival p)
  convert h using 1
  field_simp [hsurvival.ne']

/-- The actual conditional `ℓ¹` error equals the normalized-readout error. -/
theorem conditionalPositiveL1Error_eq_normalizedReadoutL1Error
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (hsurvival : 0 < survival p) :
    conditionalPositiveL1Error m p =
      normalizedReadoutL1Error m (rho m p) (survivalReadout m p) := by
  apply tsum_congr
  intro j
  rw [conditionalPositiveMass_eq_normalizedReadoutMass m p hm hcrit hsurvival j]

/-- Explicit manuscript bound for the genuine conditional law. -/
theorem conditionalPositiveL1Error_le
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (B : ℝ) (hsurvival : 0 < survival p)
    (hdelta : SupLE (discreteDerivative (rho m p)) B) :
    conditionalPositiveL1Error m p ≤
      (2 * B) /
        (survivalReadout m p * ((m : ℝ) - 1) ^ 2) := by
  have ha := survivalReadout_pos_of_survival_pos m p hm hcrit hsurvival
  rw [conditionalPositiveL1Error_eq_normalizedReadoutL1Error
    m p hm hcrit hsurvival]
  exact rho_normalizedReadoutL1Error_le m p hm hcrit B ha hdelta

/-- Transfer an explicit positive lower bound on `a` and an explicit upper bound
on the gradient into the conditional `ℓ¹` estimate. -/
theorem conditionalPositiveL1Error_le_of_readout_gradient_bounds
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (aLower B BUpper : ℝ) (haLower : 0 < aLower)
    (hBUpper : 0 ≤ BUpper) (hreadoutLower : aLower ≤ survivalReadout m p)
    (hgradient : B ≤ BUpper)
    (hdelta : SupLE (discreteDerivative (rho m p)) B) :
    conditionalPositiveL1Error m p ≤
      (2 * BUpper) / (aLower * ((m : ℝ) - 1) ^ 2) := by
  have hfactor : 0 < (m : ℝ) - 1 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have ha : 0 < survivalReadout m p := haLower.trans_le hreadoutLower
  have hsurvival := survival_pos_of_survivalReadout_pos m p hm hcrit ha
  have hbase := conditionalPositiveL1Error_le
    m p hm hcrit B hsurvival hdelta
  have hnumerator : 2 * B ≤ 2 * BUpper :=
    mul_le_mul_of_nonneg_left hgradient (by norm_num)
  have hdenominator :
      aLower * ((m : ℝ) - 1) ^ 2 ≤
        survivalReadout m p * ((m : ℝ) - 1) ^ 2 :=
    mul_le_mul_of_nonneg_right hreadoutLower (sq_nonneg _)
  exact hbase.trans (div_le_div₀ (mul_nonneg (by norm_num) hBUpper) hnumerator
    (mul_pos haLower (sq_pos_of_pos hfactor)) hdenominator)

/-- Profile-scale specialization: the explicit hypotheses
`a ≥ A/(n+1)^2` and `B ≤ D log(n+2)/(n+1)^3` yield the manuscript rate. -/
theorem conditionalPositiveL1Error_profile_scale_le
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p)
    (n : ℕ) (A D B : ℝ) (hA : 0 < A) (hD : 0 ≤ D)
    (hreadoutLower : A / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ survivalReadout m p)
    (hgradient :
      B ≤ D * Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3)
    (hdelta : SupLE (discreteDerivative (rho m p)) B) :
    conditionalPositiveL1Error m p ≤
      (2 * D / (A * ((m : ℝ) - 1) ^ 2)) *
        Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  have hfactor : 0 < (m : ℝ) - 1 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hindex : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  have haScale : 0 < A / ((n + 1 : ℕ) : ℝ) ^ 2 :=
    div_pos hA (sq_pos_of_pos hindex)
  have hgradientScale :
      0 ≤ D * Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 :=
    div_nonneg (mul_nonneg hD hlog) (by positivity)
  have hbound := conditionalPositiveL1Error_le_of_readout_gradient_bounds
    m p hm hcrit (A / ((n + 1 : ℕ) : ℝ) ^ 2) B
      (D * Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3)
      haScale hgradientScale hreadoutLower hgradient hdelta
  convert hbound using 1
  field_simp [hA.ne', hfactor.ne', hindex.ne']
  ring

/-- The pointwise profile-scale estimate, uniformly along a family of laws, is
exactly the big-O assertion in source equation `eq:tv`. -/
theorem conditionalPositiveL1Error_isBigO_of_profile_scale
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : ∀ n : ℕ, Critical m (p n))
    (A D : ℝ) (hA : 0 < A) (hD : 0 ≤ D)
    (B : ℕ → ℝ)
    (hreadoutLower : ∀ n : ℕ,
      A / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ survivalReadout m (p n))
    (hgradient : ∀ n : ℕ,
      B n ≤ D * Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3)
    (hdelta : ∀ n : ℕ,
      SupLE (discreteDerivative (rho m (p n))) (B n)) :
    (fun n : ℕ ↦ conditionalPositiveL1Error m (p n)) =O[atTop]
      (fun n : ℕ ↦ Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  refine isBigO_iff.mpr ⟨2 * D / (A * ((m : ℝ) - 1) ^ 2), ?_⟩
  filter_upwards with n
  have hbound := conditionalPositiveL1Error_profile_scale_le
    m (p n) hm (hcrit n) n A D (B n) hA hD
      (hreadoutLower n) (hgradient n) (hdelta n)
  have herrorNonneg := conditionalPositiveL1Error_nonneg m (p n)
  have hlog : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hdenom : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrate :
      0 ≤ Real.log ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg hlog hdenom
  rw [Real.norm_eq_abs, abs_of_nonneg herrorNonneg,
    Real.norm_eq_abs, abs_of_nonneg hrate]
  simpa only [div_eq_mul_inv, mul_assoc] using hbound

/-- For discrete mass functions the manuscript `ℓ¹` convention is exactly twice
conventional total variation. -/
theorem discreteL1Distance_eq_two_mul_discreteTotalVariation (u v : Seq) :
    discreteL1Distance u v = 2 * discreteTotalVariation u v := by
  simp [discreteTotalVariation]

/-- Specialized factor-two convention for `eq:tv`. -/
theorem conditionalPositiveL1Error_eq_two_mul_totalVariation
    (m : ℕ) (p : ProbabilityMass) :
    conditionalPositiveL1Error m p =
      2 * conditionalPositiveTotalVariation m p := by
  exact discreteL1Distance_eq_two_mul_discreteTotalVariation
    (conditionalPositiveMass p) (shiftedGeometricMass m)

end

end DerridaRetaux
