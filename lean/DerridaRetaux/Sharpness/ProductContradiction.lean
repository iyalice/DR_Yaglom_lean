import DerridaRetaux.Sharpness.StableProduct
import DerridaRetaux.Model.Criticality
import DerridaRetaux.Model.TiltedProperties
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# The subquadratic-product contradiction

This file formalizes the internal analytic contradiction in Section 8 (`U62`).
The Chen--Shi theorem is used only through an explicit `ChenShiStableProductFact`
parameter in the source-shaped applications at the end of the file.
-/

/-- Half-open product of the `d`th powers of a real sequence. -/
def poweredPrefixProduct (G : ℕ → ℝ) (d n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, G j ^ d

/-- The empty half-open prefix has product one. -/
@[simp]
theorem poweredPrefixProduct_zero (G : ℕ → ℝ) (d : ℕ) :
    poweredPrefixProduct G d 0 = 1 := by
  simp [poweredPrefixProduct]

/-- Pointwise lower bounds by one make every powered prefix strictly positive,
including the empty prefix. -/
theorem poweredPrefixProduct_pos
    (G : ℕ → ℝ) (d n : ℕ) (hG : ∀ j : ℕ, 1 ≤ G j) :
    0 < poweredPrefixProduct G d n := by
  rw [poweredPrefixProduct]
  exact Finset.prod_pos fun j hj ↦ pow_pos (lt_of_lt_of_le zero_lt_one (hG j)) d

/-- The logarithm of a positive powered prefix product is the corresponding finite sum. -/
theorem log_poweredPrefixProduct
    (G : ℕ → ℝ) (d n : ℕ) (hG : ∀ j : ℕ, 1 ≤ G j) :
    Real.log (poweredPrefixProduct G d n) =
      (d : ℝ) * ∑ j ∈ Finset.range n, Real.log (G j) := by
  rw [poweredPrefixProduct, Real.log_prod]
  · simp_rw [Real.log_pow]
    exact (Finset.mul_sum (Finset.range n) (fun j ↦ Real.log (G j)) (d : ℝ)).symm
  · intro j hj
    exact (pow_pos (lt_of_lt_of_le zero_lt_one (hG j)) d).ne'

/-- A real harmonic tail is exactly a difference of harmonic numbers. -/
theorem sum_Ico_inv_nat_succ_eq_harmonic_sub (a n : ℕ) (han : a ≤ n) :
    ∑ j ∈ Finset.Ico a n, (((j + 1 : ℕ) : ℝ))⁻¹ =
      (harmonic n : ℝ) - (harmonic a : ℝ) := by
  rw [Finset.sum_Ico_eq_sub _ han]
  simp only [harmonic, Rat.cast_sub, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- A scaled lower bound on `G j - 1` gives the harmonic logarithmic bound used
in the product contradiction.  The shift to `j + 1` handles the harmonic sum
without changing its leading coefficient. -/
theorem div_nat_succ_le_log_of_scaled_sub_one
    (G : ℕ → ℝ) (beta : ℝ) (hbeta : 0 < beta) (hbetaTwo : beta ≤ 2)
    (j : ℕ) (hj : 1 ≤ j) (hscaled : beta ≤ (j : ℝ) * (G j - 1)) :
    beta / ((j + 1 : ℕ) : ℝ) ≤ Real.log (G j) := by
  have hjReal : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hsub : beta / (j : ℝ) ≤ G j - 1 := by
    rw [div_le_iff₀ hjReal]
    simpa [mul_comm] using hscaled
  have hx : 0 ≤ beta / (j : ℝ) := div_nonneg hbeta.le hjReal.le
  have hlogMonotone :
      Real.log (1 + beta / (j : ℝ)) ≤ Real.log (G j) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hfraction :
      beta / ((j + 1 : ℕ) : ℝ) ≤
        2 * (beta / (j : ℝ)) / (beta / (j : ℝ) + 2) := by
    have heq :
        2 * (beta / (j : ℝ)) / (beta / (j : ℝ) + 2) =
          2 * beta / (beta + 2 * (j : ℝ)) := by
      field_simp [hjReal.ne']
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num [Nat.cast_add]
    nlinarith [mul_nonneg hbeta.le (sub_nonneg.mpr hbetaTwo)]
  exact hfraction.trans ((Real.le_log_one_add_of_nonneg hx).trans hlogMonotone)

/-- A sequence with `n * (G n - 1) → 2 / (m - 1)` and `G n ≥ 1` cannot
have even an eventual half-open product bound by a strictly subquadratic real power. -/
theorem no_eventual_subquadratic_poweredPrefixProduct_bound
    (m : ℕ) (G : ℕ → ℝ) (p : ℝ) (hm : 2 ≤ m) (hp : 0 < p) (hpTwo : p < 2)
    (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop
      (nhds (2 / ((m : ℝ) - 1)))) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      poweredPrefixProduct G (m - 1) n ≤ C * Real.rpow (n : ℝ) p := by
  rintro ⟨C, hC, hupper⟩
  have hmOne : 1 ≤ m := by omega
  have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hdegree : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  let beta : ℝ := (p + 2) / (2 * ((m : ℝ) - 1))
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have hbetaLimit : beta < 2 / ((m : ℝ) - 1) := by
    dsimp [beta]
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) hdegree) hdegree]
    nlinarith
  have hbetaTwo : beta ≤ 2 := by
    have hdegreeOne : (1 : ℝ) ≤ (m : ℝ) - 1 := by exact_mod_cast (show 1 ≤ m - 1 by omega)
    dsimp [beta]
    rw [div_le_iff₀ (mul_pos (by norm_num) hdegree)]
    nlinarith
  have hcoefficient :
      ((m : ℝ) - 1) * beta = (p + 2) / 2 := by
    dsimp [beta]
    field_simp [hdegree.ne']
    ring
  have hgap : 0 < ((m : ℝ) - 1) * beta - p := by
    rw [hcoefficient]
    linarith
  have heventualScaled :
      ∀ᶠ j : ℕ in atTop, beta ≤ (j : ℝ) * (G j - 1) :=
    (hlimit.eventually_const_lt hbetaLimit).mono fun _ hj ↦ hj.le
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp heventualScaled
  let J := max J₀ 1
  have hJOne : 1 ≤ J := le_max_right J₀ 1
  have hscaled (j : ℕ) (hj : J ≤ j) : beta ≤ (j : ℝ) * (G j - 1) :=
    hJ₀ j (le_trans (le_max_left J₀ 1) hj)
  have hlogLower (n : ℕ) (hJn : J ≤ n) :
      ((m : ℝ) - 1) * beta *
          (Real.log (n : ℝ) - (harmonic J : ℝ)) ≤
        Real.log (poweredPrefixProduct G (m - 1) n) := by
    have hpoint : ∀ j ∈ Finset.Ico J n,
        beta / ((j + 1 : ℕ) : ℝ) ≤ Real.log (G j) := by
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      exact div_nat_succ_le_log_of_scaled_sub_one G beta hbeta hbetaTwo j
        (le_trans hJOne hj'.1) (hscaled j hj'.1)
    have htail :
        beta * ((harmonic n : ℝ) - (harmonic J : ℝ)) ≤
          ∑ j ∈ Finset.Ico J n, Real.log (G j) := by
      calc
        beta * ((harmonic n : ℝ) - (harmonic J : ℝ)) =
            ∑ j ∈ Finset.Ico J n, beta / ((j + 1 : ℕ) : ℝ) := by
          rw [← sum_Ico_inv_nat_succ_eq_harmonic_sub J n hJn]
          simp_rw [div_eq_mul_inv]
          exact Finset.mul_sum _ _ _
        _ ≤ ∑ j ∈ Finset.Ico J n, Real.log (G j) := Finset.sum_le_sum hpoint
    have htailSubset :
        ∑ j ∈ Finset.Ico J n, Real.log (G j) ≤
          ∑ j ∈ Finset.range n, Real.log (G j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      · intro j hj hjnot
        exact Real.log_nonneg (hG j)
    have hlogHarmonic : Real.log (n : ℝ) ≤ (harmonic n : ℝ) := by
      have hnOne : 1 ≤ n := le_trans hJOne hJn
      have hcast : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnOne
      calc
        Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
          apply Real.log_le_log hcast
          exact_mod_cast (Nat.le_add_right n 1)
        _ ≤ (harmonic n : ℝ) := log_add_one_le_harmonic n
    rw [log_poweredPrefixProduct G (m - 1) n hG, Nat.cast_sub hmOne]
    norm_num
    calc
      ((m : ℝ) - 1) * beta *
          (Real.log (n : ℝ) - (harmonic J : ℝ)) =
          ((m : ℝ) - 1) *
            (beta * (Real.log (n : ℝ) - (harmonic J : ℝ))) := by ring
      _ ≤ ((m : ℝ) - 1) *
          (beta * ((harmonic n : ℝ) - (harmonic J : ℝ))) := by
        gcongr
      _ ≤ ((m : ℝ) - 1) *
          (∑ j ∈ Finset.Ico J n, Real.log (G j)) :=
        mul_le_mul_of_nonneg_left htail hdegree.le
      _ ≤ ((m : ℝ) - 1) *
          (∑ j ∈ Finset.range n, Real.log (G j)) :=
        mul_le_mul_of_nonneg_left htailSubset hdegree.le
  have hlogTendsto : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let K : ℝ := Real.log C + ((m : ℝ) - 1) * beta * (harmonic J : ℝ)
  let R : ℝ := K / (((m : ℝ) - 1) * beta - p) + 1
  have heventualLog : ∀ᶠ n : ℕ in atTop, R ≤ Real.log (n : ℝ) :=
    Filter.tendsto_atTop.mp hlogTendsto R
  have heventualJ : ∀ᶠ n : ℕ in atTop, J ≤ n := eventually_ge_atTop J
  obtain ⟨n, ⟨hJn, hnLog⟩, hnUpper⟩ :=
    ((heventualJ.and heventualLog).and hupper).exists
  have hnOne : 1 ≤ n := le_trans hJOne hJn
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnOne
  have hproductPos : 0 < poweredPrefixProduct G (m - 1) n :=
    poweredPrefixProduct_pos G (m - 1) n hG
  have hrpowPos : 0 < Real.rpow (n : ℝ) p := Real.rpow_pos_of_pos hnReal p
  have hlogUpper :
      Real.log (poweredPrefixProduct G (m - 1) n) ≤
        Real.log C + p * Real.log (n : ℝ) := by
    calc
      Real.log (poweredPrefixProduct G (m - 1) n) ≤
          Real.log (C * Real.rpow (n : ℝ) p) :=
        Real.log_le_log hproductPos hnUpper
      _ = Real.log C + p * Real.log (n : ℝ) := by
        rw [Real.log_mul hC.ne' hrpowPos.ne']
        congr 1
        exact Real.log_rpow hnReal p
  have hmain :
      (((m : ℝ) - 1) * beta - p) * Real.log (n : ℝ) ≤ K := by
    have hlower := hlogLower n hJn
    dsimp [K]
    linarith
  have hKR : K < (((m : ℝ) - 1) * beta - p) * R := by
    dsimp [R]
    rw [mul_add, mul_one, mul_div_cancel₀ K hgap.ne']
    linarith
  have hRlog :
      (((m : ℝ) - 1) * beta - p) * R ≤
        (((m : ℝ) - 1) * beta - p) * Real.log (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnLog hgap.le
  linarith

/-- All-index polynomial bounds are a fortiori eventual bounds. -/
theorem no_subquadratic_poweredPrefixProduct_bound
    (m : ℕ) (G : ℕ → ℝ) (p : ℝ) (hm : 2 ≤ m) (hp : 0 < p) (hpTwo : p < 2)
    (hG : ∀ n : ℕ, 1 ≤ G n)
    (hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ) * (G n - 1)) atTop
      (nhds (2 / ((m : ℝ) - 1)))) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      poweredPrefixProduct G (m - 1) n ≤ C * Real.rpow (n : ℝ) p := by
  rintro ⟨C, hC, hupper⟩
  apply no_eventual_subquadratic_poweredPrefixProduct_bound
    m G p hm hp hpTwo hG hlimit
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact hupper n hn

/-- The generic powered prefix product specializes definitionally to the
source half-open critical product. -/
theorem poweredPrefixProduct_tiltedPartition_eq_criticalProduct
    (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    poweredPrefixProduct
        (fun j : ℕ ↦ tiltedPartition m (orbit m p₀ j)) (m - 1) n =
      criticalProduct m p₀ n :=
  rfl

/-- Source-shaped U62: the explicit stable-tail law cannot satisfy the
generating-function excess limit asserted by the finite-third-moment profile theorem.
The Chen--Shi result remains an explicit theorem parameter. -/
theorem sharpnessPowerLaw_not_partition_excess_limit
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
    ¬ Tendsto
      (fun n : ℕ ↦ (n : ℝ) *
        (tiltedPartition m (orbit m (sharpnessPowerLaw m r hm hr₀ hr₃) n) - 1))
      atTop (nhds (2 / ((m : ℝ) - 1))) := by
  intro hlimit
  let p₀ := sharpnessPowerLaw m r hm hr₀ hr₃
  let exponent := sharpPowerExponent r - 2
  have hcrit : Critical m p₀ := sharpnessPowerLaw_critical m r hm hr₀ hr₃
  have hpartition : ∀ n : ℕ, 1 ≤ tiltedPartition m (orbit m p₀ n) := by
    intro n
    exact tiltedPartition_one_le_of_critical m (orbit m p₀ n) (by omega)
      (orbit_critical m p₀ (by omega) hcrit n)
  have hexponentPos : 0 < exponent := by
    dsimp [exponent]
    linarith [three_lt_sharpPowerExponent r hr₀]
  have hexponentTwo : exponent < 2 := by
    dsimp [exponent]
    linarith [sharpPowerExponent_lt_four r hr₃]
  have hlimit' :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) * (tiltedPartition m (orbit m p₀ n) - 1))
        atTop (nhds (2 / ((m : ℝ) - 1))) := by
    simpa [p₀] using hlimit
  apply no_eventual_subquadratic_poweredPrefixProduct_bound
    m (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n)) exponent
      hm hexponentPos hexponentTwo hpartition hlimit'
  obtain ⟨c₁, c₂, hc₁, hc₁c₂, hbounds⟩ :=
    sharpnessPowerLaw_product_bounds m r hm hr₀ hr₃ hStable
  refine ⟨c₂, lt_of_lt_of_le hc₁ hc₁c₂, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa [p₀, exponent, poweredPrefixProduct, criticalProduct] using (hbounds n hn).2

/-- Complete source-shaped sharpness conclusion: for every real tilted-moment
order in [0, 3), the explicit critical non-Dirac law has that moment finite,
has infinite third tilted moment, and violates the profile excess limit. -/
theorem exists_critical_law_with_finite_real_tilt_and_no_profile_excess_limit
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
    ∃ p₀ : ProbabilityMass,
      Critical m p₀ ∧
        ¬ IsDirac p₀ ∧
        RealTiltSummable m r p₀ ∧
        ¬ TiltSummable m 3 p₀ ∧
        ¬ Tendsto
          (fun n : ℕ ↦ (n : ℝ) * (tiltedPartition m (orbit m p₀ n) - 1))
          atTop (nhds (2 / ((m : ℝ) - 1))) := by
  refine ⟨sharpnessPowerLaw m r hm hr₀ hr₃,
    sharpnessPowerLaw_critical m r hm hr₀ hr₃,
    sharpnessPowerLaw_not_isDirac m r hm hr₀ hr₃,
    sharpnessPowerLaw_realTiltSummable m r hm hr₀ hr₃,
    sharpnessPowerLaw_not_tiltSummable_three m r hm hr₀ hr₃, ?_⟩
  exact sharpnessPowerLaw_not_partition_excess_limit m r hm hr₀ hr₃ hStable

end

end DerridaRetaux
