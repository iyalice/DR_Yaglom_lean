import DerridaRetaux.ExternalSignatures
import DerridaRetaux.Model.CoarseRelations
import DerridaRetaux.Model.TiltedRecursion
import DerridaRetaux.Model.ZeroAtom
import DerridaRetaux.Model.TransportCoefficient
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

open Filter Topology

/-!
# First tilted atom and its tail

This file proves the elementary part of source equations `eq:theta`, `eq:c`, and
`lem:atomtail`.  The published CDHLS excess estimate is always an explicit theorem
parameter; this module does not import `HumanInputs`.
-/

noncomputable section

/-- Source notation `epsilon_n = G_n - 1`. -/
def orbitExcess (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  excess m (orbit m p₀ n)

/-- Source notation `theta_n = 1 - x_n`. -/
def orbitPositiveTiltMass (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  positiveTiltMass m (orbit m p₀ n)

/-- Source notation for the first strictly positive tilted atom. -/
def firstTiltedAtom (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  normalizedTilt m (orbit m p₀ n) 1

/-- The nonnegative coefficient defect `1 - c_n`. -/
def orbitTransportDefect (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  1 - transportCoeff m (orbit m p₀ n)

/-- The inverse-coefficient correction in the exact first-atom identity. -/
def firstAtomCorrection (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  ((transportCoeff m (orbit m p₀ n))⁻¹ - 1) *
    zeroTilt m (orbit m p₀ (n + 1))

/-- The source tail `T_n = sum_{s ≥ n} q_{s,1}`. -/
def firstTiltedAtomTail (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  ∑' j : ℕ, firstTiltedAtom m p₀ (n + j)

/-- The CDHLS `C / n` estimate, enlarged once, holds uniformly as `C' / (n + 1)`.
The same witness also records the internally proved nonnegativity of the excess. -/
theorem orbitExcess_bound_all
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      0 ≤ orbitExcess m p₀ n ∧
        orbitExcess m p₀ n ≤ C / ((n + 1 : ℕ) : ℝ) := by
  rcases hExcess with ⟨C, hC, hbound⟩
  let C' := max (orbitExcess m p₀ 0) (2 * C)
  have hC' : 0 < C' := by
    exact lt_of_lt_of_le (mul_pos (by norm_num) hC) (le_max_right _ _)
  refine ⟨C', hC', fun n ↦ ⟨?_, ?_⟩⟩
  · exact excess_nonneg m (orbit m p₀ n) (by omega)
      (orbit_critical m p₀ (by omega) hcrit n).1
  · by_cases hn : n = 0
    · subst n
      norm_num [orbitExcess, C']
    · have hnNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hnSuccReal : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hsource := hbound n hnNat
      change orbitExcess m p₀ n ≤ C / (n : ℝ) at hsource
      calc
        orbitExcess m p₀ n ≤ C / (n : ℝ) := hsource
        _ ≤ (2 * C) / ((n + 1 : ℕ) : ℝ) := by
          apply (div_le_div_iff₀ hnReal hnSuccReal).2
          have hnCast : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
            exact_mod_cast (show n + 1 ≤ 2 * n by omega)
          nlinarith
        _ ≤ C' / ((n + 1 : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right (le_max_right _ _) hnSuccReal.le

/-- The source estimate `theta_n ≤ 2 epsilon_n`; the factor two is uniform for
every arity `m ≥ 2`. -/
theorem positiveTiltMass_le_two_mul_excess
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p) :
    positiveTiltMass m p ≤ 2 * excess m p := by
  have hmOne : 1 ≤ m := by omega
  have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcriticalExcess : 0 ≤ excess m p := excess_nonneg m p hmOne hcrit.1
  have hsurvival := survival_le_excess_div_of_critical m p hm hcrit
  have hfactor : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hdiv : excess m p / ((m : ℝ) - 1) ≤ excess m p := by
    apply (div_le_iff₀ hfactor).2
    nlinarith
  have hsurvivalExcess : survival p ≤ excess m p := le_trans hsurvival hdiv
  have hGpos := tiltedPartition_pos_of_critical m p hmOne hcrit
  have hGone := tiltedPartition_one_le_of_critical m p hmOne hcrit
  rw [positiveTiltMass_eq_excess_add_survival_div m p hmOne hcrit]
  have hnumerator : 0 ≤ excess m p + survival p :=
    add_nonneg hcriticalExcess (survival_nonneg p)
  have hquotient :
      (excess m p + survival p) / tiltedPartition m p ≤
        excess m p + survival p := by
    apply (div_le_iff₀ hGpos).2
    nlinarith
  linarith

/-- The published excess estimate gives the source bound
`theta_n = O(1 / (n + 1))` with an explicit positive witness. -/
theorem orbitPositiveTiltMass_bound_all
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      0 ≤ orbitPositiveTiltMass m p₀ n ∧
        orbitPositiveTiltMass m p₀ n ≤ C / ((n + 1 : ℕ) : ℝ) := by
  rcases orbitExcess_bound_all m p₀ hm hcrit hthird hnonconstant hExcess with
    ⟨C, hC, hbound⟩
  refine ⟨2 * C, mul_pos (by norm_num) hC, fun n ↦ ⟨?_, ?_⟩⟩
  · exact positiveTiltMass_nonneg m (orbit m p₀ n) (by omega)
      (orbit_critical m p₀ (by omega) hcrit n)
  · calc
      orbitPositiveTiltMass m p₀ n ≤ 2 * orbitExcess m p₀ n :=
        positiveTiltMass_le_two_mul_excess m (orbit m p₀ n) hm
          (orbit_critical m p₀ (by omega) hcrit n)
      _ ≤ 2 * (C / ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hbound n).2 (by norm_num)
      _ = (2 * C) / ((n + 1 : ℕ) : ℝ) := by ring

/-- Exact source recurrence `x_(n+1) = c_n (x_n + q_(n,1))`. -/
theorem orbitZeroTilt_succ_eq_transportCoeff_mul
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    zeroTilt m (orbit m p₀ (n + 1)) =
      transportCoeff m (orbit m p₀ n) *
        (zeroTilt m (orbit m p₀ n) + firstTiltedAtom m p₀ n) := by
  rw [zeroTilt_orbit_succ m p₀ hm hcrit n]
  simp only [transportCoeff, firstTiltedAtom]
  ring

/-- Exact zero-atom relation from `lem:atomtail`.  Positivity of the zero atom is
used first to justify the inverse transport coefficient. -/
theorem firstTiltedAtom_eq_theta_sub_theta_succ_add
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (n : ℕ) :
    firstTiltedAtom m p₀ n =
      orbitPositiveTiltMass m p₀ n - orbitPositiveTiltMass m p₀ (n + 1) +
        ((transportCoeff m (orbit m p₀ n))⁻¹ - 1) *
          zeroTilt m (orbit m p₀ (n + 1)) := by
  have hmOne : 1 ≤ m := by omega
  have hcritn := orbit_critical m p₀ hmOne hcrit n
  have hx := orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint n
  have hc := transportCoeff_pos m (orbit m p₀ n) hmOne hcritn hx
  have hrec := orbitZeroTilt_succ_eq_transportCoeff_mul m p₀ hmOne hcrit n
  calc
    firstTiltedAtom m p₀ n =
        (transportCoeff m (orbit m p₀ n))⁻¹ *
            zeroTilt m (orbit m p₀ (n + 1)) - zeroTilt m (orbit m p₀ n) := by
      rw [hrec]
      field_simp [hc.ne']
    _ = orbitPositiveTiltMass m p₀ n - orbitPositiveTiltMass m p₀ (n + 1) +
        ((transportCoeff m (orbit m p₀ n))⁻¹ - 1) *
          zeroTilt m (orbit m p₀ (n + 1)) := by
      simp only [orbitPositiveTiltMass, positiveTiltMass]
      ring

/-- Definitionally packaged form of the exact first-atom identity. -/
theorem firstTiltedAtom_eq_theta_sub_theta_succ_add_correction
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (n : ℕ) :
    firstTiltedAtom m p₀ n =
      orbitPositiveTiltMass m p₀ n - orbitPositiveTiltMass m p₀ (n + 1) +
        firstAtomCorrection m p₀ n := by
  simpa [firstAtomCorrection] using
    firstTiltedAtom_eq_theta_sub_theta_succ_add m p₀ hm hcrit hnotBinaryFixedPoint n

/-- Every coefficient defect along a critical orbit is nonnegative. -/
theorem orbitTransportDefect_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    0 ≤ orbitTransportDefect m p₀ n := by
  rw [orbitTransportDefect]
  linarith [transportCoeff_le_one m (orbit m p₀ n) hm
    (orbit_critical m p₀ hm hcrit n)]

/-- The correction term is nonnegative once the source admissibility condition
guarantees a nonzero transport coefficient. -/
theorem firstAtomCorrection_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (n : ℕ) :
    0 ≤ firstAtomCorrection m p₀ n := by
  have hmOne : 1 ≤ m := by omega
  have hcritn := orbit_critical m p₀ hmOne hcrit n
  have hx := orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint n
  have hc := transportCoeff_pos m (orbit m p₀ n) hmOne hcritn hx
  have hcle := transportCoeff_le_one m (orbit m p₀ n) hmOne hcritn
  have hinv : 1 ≤ (transportCoeff m (orbit m p₀ n))⁻¹ :=
    (one_le_inv₀ hc).2 hcle
  exact mul_nonneg (sub_nonneg.mpr hinv)
    (normalizedTilt_nonneg m (orbit m p₀ (n + 1)) hmOne
      (orbit_critical m p₀ hmOne hcrit (n + 1)) 0)

/-- A pointwise `theta_n ≤ C/(n+1)` estimate gives the explicit quadratic bound
on the transport defect used after source equation `eq:c`. -/
theorem orbitTransportDefect_le_of_positiveTiltMass_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (C : ℝ) (hC : 0 ≤ C)
    (htheta : ∀ n : ℕ,
      orbitPositiveTiltMass m p₀ n ≤ C / ((n + 1 : ℕ) : ℝ))
    (n : ℕ) :
    orbitTransportDefect m p₀ n ≤
      (((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 * C ^ 2) /
        ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hcritn := orbit_critical m p₀ hm hcrit n
  have hthetaNonneg : 0 ≤ orbitPositiveTiltMass m p₀ n :=
    positiveTiltMass_nonneg m (orbit m p₀ n) hm hcritn
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hright : 0 ≤ C / ((n + 1 : ℕ) : ℝ) := div_nonneg hC hden.le
  have hsquare :
      orbitPositiveTiltMass m p₀ n ^ 2 ≤
        (C / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith [htheta n]
  have hconstant :
      0 ≤ ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 := by positivity
  calc
    orbitTransportDefect m p₀ n ≤
        ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 *
          orbitPositiveTiltMass m p₀ n ^ 2 := by
      simpa [orbitTransportDefect, orbitPositiveTiltMass, positiveTiltMass] using
        one_subCoeff_le_quadratic m (orbit m p₀ n) hm hcritn
    _ ≤ ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 *
        (C / ((n + 1 : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hconstant
    _ = (((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 * C ^ 2) /
        ((n + 1 : ℕ) : ℝ) ^ 2 := by ring

/-- The quadratic defect estimate forces `c_n ≥ 1/2` from some explicit finite
index onward. -/
theorem eventually_half_le_transportCoeff_of_positiveTiltMass_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (C : ℝ) (hC : 0 ≤ C)
    (htheta : ∀ n : ℕ,
      orbitPositiveTiltMass m p₀ n ≤ C / ((n + 1 : ℕ) : ℝ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 : ℝ) / 2 ≤ transportCoeff m (orbit m p₀ n) := by
  let K := ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 * C ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * K)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnSucc : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by norm_num
  have hlarge : 2 * K < ((n + 1 : ℕ) : ℝ) := lt_trans (hN.trans_le hNn) hnSucc
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdenOne : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have hdenSquare :
      ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hquotient : K / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).2
    nlinarith
  have hdefect := orbitTransportDefect_le_of_positiveTiltMass_bound
    m p₀ hm hcrit C hC htheta n
  have hdefect' : orbitTransportDefect m p₀ n ≤ K / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [K] using hdefect
  rw [orbitTransportDefect] at hdefect'
  linarith

/-- Once `c_n ≥ 1/2`, the inverse-coefficient correction is at most twice the
ordinary coefficient defect. -/
theorem firstAtomCorrection_le_two_mul_defect
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (n : ℕ)
    (hhalf : (1 : ℝ) / 2 ≤ transportCoeff m (orbit m p₀ n)) :
    firstAtomCorrection m p₀ n ≤ 2 * orbitTransportDefect m p₀ n := by
  have hmOne : 1 ≤ m := by omega
  have hcritn := orbit_critical m p₀ hmOne hcrit n
  have hx := orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint n
  have hc := transportCoeff_pos m (orbit m p₀ n) hmOne hcritn hx
  have hcle := transportCoeff_le_one m (orbit m p₀ n) hmOne hcritn
  have hdefect : 0 ≤ orbitTransportDefect m p₀ n :=
    orbitTransportDefect_nonneg m p₀ hmOne hcrit n
  have hinvOne : 1 ≤ (transportCoeff m (orbit m p₀ n))⁻¹ :=
    (one_le_inv₀ hc).2 hcle
  have hinvTwo : (transportCoeff m (orbit m p₀ n))⁻¹ ≤ 2 := by
    exact (inv_le_iff_one_le_mul₀ hc).2 (by nlinarith)
  have hfactor :
      (transportCoeff m (orbit m p₀ n))⁻¹ - 1 ≤
        2 * orbitTransportDefect m p₀ n := by
    rw [orbitTransportDefect]
    have hinvIdentity :
        (transportCoeff m (orbit m p₀ n))⁻¹ - 1 =
          (transportCoeff m (orbit m p₀ n))⁻¹ *
            (1 - transportCoeff m (orbit m p₀ n)) := by
      field_simp [hc.ne']
    rw [hinvIdentity]
    exact mul_le_mul_of_nonneg_right hinvTwo (sub_nonneg.mpr hcle)
  have hxNext := zeroTilt_le_one m (orbit m p₀ (n + 1)) hmOne
    (orbit_critical m p₀ hmOne hcrit (n + 1))
  have hfactorNonneg :
      0 ≤ (transportCoeff m (orbit m p₀ n))⁻¹ - 1 := sub_nonneg.mpr hinvOne
  calc
    firstAtomCorrection m p₀ n ≤
        (transportCoeff m (orbit m p₀ n))⁻¹ - 1 := by
      exact mul_le_of_le_one_right hfactorNonneg hxNext
    _ ≤ 2 * orbitTransportDefect m p₀ n := hfactor

/-- The quadratic coefficient defects are summable.  This is the internal
summability consequence of `theta_n = O(1/(n+1))`; no infinite-product theorem
is assumed. -/
theorem orbitTransportDefect_summable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    Summable (fun n : ℕ ↦ orbitTransportDefect m p₀ n) := by
  rcases orbitPositiveTiltMass_bound_all m p₀ hm hcrit hthird hnonconstant hExcess with
    ⟨C, hC, htheta⟩
  let K := ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 * C ^ 2
  have hpSeries : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hpSeriesShift :
      Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using (summable_nat_add_iff 1).2 hpSeries
  have hmajorant : Summable (fun n : ℕ ↦ K / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [div_eq_mul_inv] using hpSeriesShift.mul_left K
  apply hmajorant.of_nonneg_of_le
  · exact fun n ↦ orbitTransportDefect_nonneg m p₀ (by omega) hcrit n
  · intro n
    simpa [K] using
      orbitTransportDefect_le_of_positiveTiltMass_bound m p₀ (by omega) hcrit C hC.le
        (fun j ↦ (htheta j).2) n

/-- Summability of `1 - c_n` gives convergence of the infinite product of the
transport coefficients. -/
theorem orbitTransportCoeff_multipliable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    Multipliable (fun n : ℕ ↦ transportCoeff m (orbit m p₀ n)) := by
  have hdefect := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hproduct := Real.multipliable_one_add_of_summable hdefect.neg
  convert hproduct using 1
  funext n
  simp [orbitTransportDefect]

/-- The infinite transport product is strictly positive under the source
admissibility condition. -/
theorem orbitTransportCoeff_tprod_pos
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    0 < ∏' n : ℕ, transportCoeff m (orbit m p₀ n) := by
  have hmOne : 1 ≤ m := by omega
  have hdefect := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hlogBase := Real.summable_log_one_add_of_summable hdefect.neg
  have hlog : Summable (fun n : ℕ ↦ Real.log (transportCoeff m (orbit m p₀ n))) := by
    convert hlogBase using 1
    funext n
    simp [orbitTransportDefect]
  have hc : ∀ n : ℕ, 0 < transportCoeff m (orbit m p₀ n) := by
    intro n
    exact transportCoeff_pos m (orbit m p₀ n) hmOne
      (orbit_critical m p₀ hmOne hcrit n)
      (orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint n)
  rw [← Real.rexp_tsum_eq_tprod hc hlog]
  exact Real.exp_pos _

/-- Source equation `eq:C`: the finite exclusive products converge to a positive
limit. -/
theorem transportProduct_tendsto_pos
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    ∃ Cinf : ℝ, 0 < Cinf ∧ Tendsto (transportProduct m p₀) atTop (𝓝 Cinf) := by
  let Cinf := ∏' n : ℕ, transportCoeff m (orbit m p₀ n)
  have hmultiple := orbitTransportCoeff_multipliable
    m p₀ hm hcrit hthird hnonconstant hExcess
  refine ⟨Cinf, ?_, ?_⟩
  · exact orbitTransportCoeff_tprod_pos
      m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess
  · simpa [Cinf, transportProduct] using hmultiple.tendsto_prod_tprod_nat

/-- The inverse-coefficient corrections are summable.  A finite prefix is harmless;
on the tail, `c_n ≥ 1/2` reduces this to the summable quadratic defect. -/
theorem firstAtomCorrection_summable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    Summable (fun n : ℕ ↦ firstAtomCorrection m p₀ n) := by
  rcases orbitPositiveTiltMass_bound_all m p₀ hm hcrit hthird hnonconstant hExcess with
    ⟨C, hC, htheta⟩
  rcases eventually_half_le_transportCoeff_of_positiveTiltMass_bound
      m p₀ (by omega) hcrit C hC.le (fun n ↦ (htheta n).2) with ⟨N, hhalf⟩
  have hdefect := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hdefectShift :
      Summable (fun n : ℕ ↦ orbitTransportDefect m p₀ (n + N)) :=
    (summable_nat_add_iff N).2 hdefect
  have hmajorant :
      Summable (fun n : ℕ ↦ 2 * orbitTransportDefect m p₀ (n + N)) :=
    hdefectShift.mul_left 2
  have hcorrectionShift :
      Summable (fun n : ℕ ↦ firstAtomCorrection m p₀ (n + N)) := by
    apply hmajorant.of_nonneg_of_le
    · exact fun n ↦ firstAtomCorrection_nonneg m p₀ hm hcrit hnotBinaryFixedPoint (n + N)
    · intro n
      exact firstAtomCorrection_le_two_mul_defect
        m p₀ hm hcrit hnotBinaryFixedPoint (n + N) (hhalf (n + N) (by omega))
  exact (summable_nat_add_iff N).1 hcorrectionShift

/-- The positive tilted mass tends to zero under the published excess estimate. -/
theorem orbitPositiveTiltMass_tendsto_zero
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    Tendsto (orbitPositiveTiltMass m p₀) atTop (𝓝 0) := by
  rcases orbitPositiveTiltMass_bound_all m p₀ hm hcrit hthird hnonconstant hExcess with
    ⟨C, _hC, htheta⟩
  apply squeeze_zero
  · exact fun n ↦ (htheta n).1
  · exact fun n ↦ (htheta n).2
  · convert (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (tendsto_add_atTop_nat 1) using 1

/-- The first tilted atoms form a summable sequence.  This is proved directly from
bounded nonnegative partial sums, the exact atom identity, and the summable
correction; it does not assume monotonicity of `theta_n`. -/
theorem firstTiltedAtom_summable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    Summable (fun n : ℕ ↦ firstTiltedAtom m p₀ n) := by
  have hmOne : 1 ≤ m := by omega
  have hcorrection := firstAtomCorrection_summable
    m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess
  apply summable_of_sum_range_le
    (c := orbitPositiveTiltMass m p₀ 0 + ∑' n : ℕ, firstAtomCorrection m p₀ n)
  · intro n
    exact normalizedTilt_nonneg m (orbit m p₀ n) hmOne
      (orbit_critical m p₀ hmOne hcrit n) 1
  · intro N
    have hsumIdentity :
        (∑ n ∈ Finset.range N, firstTiltedAtom m p₀ n) =
          orbitPositiveTiltMass m p₀ 0 - orbitPositiveTiltMass m p₀ N +
            ∑ n ∈ Finset.range N, firstAtomCorrection m p₀ n := by
      calc
        (∑ n ∈ Finset.range N, firstTiltedAtom m p₀ n) =
            ∑ n ∈ Finset.range N,
              (
              (orbitPositiveTiltMass m p₀ n - orbitPositiveTiltMass m p₀ (n + 1)) +
                firstAtomCorrection m p₀ n) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact firstTiltedAtom_eq_theta_sub_theta_succ_add_correction
            m p₀ hm hcrit hnotBinaryFixedPoint n
        _ = (∑ n ∈ Finset.range N,
              (orbitPositiveTiltMass m p₀ n - orbitPositiveTiltMass m p₀ (n + 1))) +
              ∑ n ∈ Finset.range N, firstAtomCorrection m p₀ n := by
          rw [Finset.sum_add_distrib]
        _ = orbitPositiveTiltMass m p₀ 0 - orbitPositiveTiltMass m p₀ N +
              ∑ n ∈ Finset.range N, firstAtomCorrection m p₀ n := by
          rw [Finset.sum_range_sub']
    have hthetaN : 0 ≤ orbitPositiveTiltMass m p₀ N :=
      positiveTiltMass_nonneg m (orbit m p₀ N) hmOne
        (orbit_critical m p₀ hmOne hcrit N)
    have hcorrectionPartial :
        (∑ n ∈ Finset.range N, firstAtomCorrection m p₀ n) ≤
          ∑' n : ℕ, firstAtomCorrection m p₀ n :=
      hcorrection.sum_le_tsum (Finset.range N)
        (fun n hn ↦ firstAtomCorrection_nonneg m p₀ hm hcrit hnotBinaryFixedPoint n)
    rw [hsumIdentity]
    linarith

/-- Exact tail decomposition
`T_n = theta_n + sum_{s ≥ n} (c_s⁻¹ - 1) x_(s+1)`. -/
theorem firstTiltedAtomTail_eq_theta_add_correctionTail
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) (n : ℕ) :
    firstTiltedAtomTail m p₀ n =
      orbitPositiveTiltMass m p₀ n +
        ∑' j : ℕ, firstAtomCorrection m p₀ (n + j) := by
  have hq := firstTiltedAtom_summable
    m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess
  have hcorrection := firstAtomCorrection_summable
    m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess
  have hqShift : Summable (fun j : ℕ ↦ firstTiltedAtom m p₀ (n + j)) := by
    simpa [add_comm] using (summable_nat_add_iff n).2 hq
  have hcorrectionShift : Summable (fun j : ℕ ↦ firstAtomCorrection m p₀ (n + j)) := by
    simpa [add_comm] using (summable_nat_add_iff n).2 hcorrection
  have hdiff : Summable (fun j : ℕ ↦
      orbitPositiveTiltMass m p₀ (n + j) - orbitPositiveTiltMass m p₀ (n + j + 1)) := by
    apply (hqShift.sub hcorrectionShift).congr
    intro j
    rw [firstTiltedAtom_eq_theta_sub_theta_succ_add_correction
      m p₀ hm hcrit hnotBinaryFixedPoint (n + j)]
    ring
  have htheta := orbitPositiveTiltMass_tendsto_zero
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hthetaShift :
      Tendsto (fun N : ℕ ↦ orbitPositiveTiltMass m p₀ (n + N)) atTop (𝓝 0) := by
    simpa [add_comm] using htheta.comp (tendsto_add_atTop_nat n)
  have htelescope :
      Tendsto
        (fun N : ℕ ↦ ∑ j ∈ Finset.range N,
          (orbitPositiveTiltMass m p₀ (n + j) -
            orbitPositiveTiltMass m p₀ (n + j + 1)))
        atTop (𝓝 (orbitPositiveTiltMass m p₀ n)) := by
    have htelescopeIdentity : ∀ N : ℕ,
        (∑ j ∈ Finset.range N,
          (orbitPositiveTiltMass m p₀ (n + j) -
            orbitPositiveTiltMass m p₀ (n + j + 1))) =
          orbitPositiveTiltMass m p₀ n - orbitPositiveTiltMass m p₀ (n + N) := by
      intro N
      simpa [add_assoc] using
        Finset.sum_range_sub' (fun j : ℕ ↦ orbitPositiveTiltMass m p₀ (n + j)) N
    simp_rw [htelescopeIdentity]
    simpa using hthetaShift.const_sub (orbitPositiveTiltMass m p₀ n)
  have hdiffTsum :
      (∑' j : ℕ, (orbitPositiveTiltMass m p₀ (n + j) -
        orbitPositiveTiltMass m p₀ (n + j + 1))) = orbitPositiveTiltMass m p₀ n :=
    tendsto_nhds_unique hdiff.hasSum.tendsto_sum_nat htelescope
  rw [firstTiltedAtomTail]
  calc
    (∑' j : ℕ, firstTiltedAtom m p₀ (n + j)) =
        ∑' j : ℕ, ((orbitPositiveTiltMass m p₀ (n + j) -
          orbitPositiveTiltMass m p₀ (n + j + 1)) +
            firstAtomCorrection m p₀ (n + j)) := by
      apply tsum_congr
      intro j
      exact firstTiltedAtom_eq_theta_sub_theta_succ_add_correction
        m p₀ hm hcrit hnotBinaryFixedPoint (n + j)
    _ = (∑' j : ℕ, (orbitPositiveTiltMass m p₀ (n + j) -
          orbitPositiveTiltMass m p₀ (n + j + 1))) +
            ∑' j : ℕ, firstAtomCorrection m p₀ (n + j) := by
      rw [hdiff.tsum_add hcorrectionShift]
    _ = orbitPositiveTiltMass m p₀ n +
          ∑' j : ℕ, firstAtomCorrection m p₀ (n + j) := by rw [hdiffTsum]

/-- Every first tilted atom tail is nonnegative. -/
theorem firstTiltedAtomTail_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    0 ≤ firstTiltedAtomTail m p₀ n := by
  rw [firstTiltedAtomTail]
  exact tsum_nonneg fun j ↦ normalizedTilt_nonneg m (orbit m p₀ (n + j)) hm
    (orbit_critical m p₀ hm hcrit (n + j)) 1

/-- A tail of the nonnegative summable first-atom series is bounded by its full sum. -/
theorem firstTiltedAtomTail_le_zero
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) (n : ℕ) :
    firstTiltedAtomTail m p₀ n ≤ firstTiltedAtomTail m p₀ 0 := by
  have hmOne : 1 ≤ m := by omega
  have hq := firstTiltedAtom_summable
    m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess
  have hqShift : Summable (fun j : ℕ ↦ firstTiltedAtom m p₀ (n + j)) := by
    simpa [add_comm] using (summable_nat_add_iff n).2 hq
  rw [firstTiltedAtomTail, firstTiltedAtomTail]
  simp only [zero_add]
  exact Summable.tsum_le_tsum_of_inj
    (fun j : ℕ ↦ n + j) (add_right_injective n)
    (fun c hc ↦ normalizedTilt_nonneg m (orbit m p₀ c) hmOne
      (orbit_critical m p₀ hmOne hcrit c) 1)
    (fun j ↦ le_rfl) hqShift hq

/-- Elementary finite-tail estimate for the shifted reciprocal-square series. -/
theorem sum_range_shifted_inv_sq_le (n N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (((n + j + 1 : ℕ) : ℝ) ^ 2)) ≤
      2 / ((n + 1 : ℕ) : ℝ) := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) n (n + N + 1)
  rw [← Nat.Ico_succ_left, Finset.sum_Ico_eq_sum_range] at h
  have hsub : n + N + 1 - (n + 1) = N := by omega
  rw [hsub] at h
  simpa [add_assoc, add_comm, add_left_comm, one_div] using h

/-- A reciprocal-square pointwise bound on the correction gives an explicit
reciprocal first-tail bound. -/
theorem firstAtomCorrectionTail_le_of_eventual_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (K : ℝ) (hK : 0 ≤ K) (N : ℕ)
    (hbound : ∀ s : ℕ, N ≤ s →
      firstAtomCorrection m p₀ s ≤ K / ((s + 1 : ℕ) : ℝ) ^ 2)
    (n : ℕ) (hn : N ≤ n) :
    (∑' j : ℕ, firstAtomCorrection m p₀ (n + j)) ≤
      (2 * K) / ((n + 1 : ℕ) : ℝ) := by
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact firstAtomCorrection_nonneg m p₀ hm hcrit hnotBinaryFixedPoint (n + j)
  · intro L
    calc
      (∑ j ∈ Finset.range L, firstAtomCorrection m p₀ (n + j)) ≤
          ∑ j ∈ Finset.range L, K / (((n + j) + 1 : ℕ) : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hbound (n + j) (hn.trans (Nat.le_add_right n j))
      _ = K * (∑ j ∈ Finset.range L, 1 / (((n + j) + 1 : ℕ) : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ K * (2 / ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_range_shifted_inv_sq_le n L) hK
      _ = (2 * K) / ((n + 1 : ℕ) : ℝ) := by ring

/-- The source first tilted atom tail is `O(1/(n+1))`, with positive constants
and an explicit eventual quantifier. -/
theorem firstTiltedAtomTail_bound_eventually
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 ≤ firstTiltedAtomTail m p₀ n ∧
        firstTiltedAtomTail m p₀ n ≤ C / ((n + 1 : ℕ) : ℝ) := by
  rcases orbitPositiveTiltMass_bound_all m p₀ hm hcrit hthird hnonconstant hExcess with
    ⟨Ctheta, hCtheta, htheta⟩
  let K := ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 * Ctheta ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  rcases eventually_half_le_transportCoeff_of_positiveTiltMass_bound
      m p₀ (by omega) hcrit Ctheta hCtheta.le (fun n ↦ (htheta n).2) with ⟨N, hhalf⟩
  have hcorrectionBound : ∀ s : ℕ, N ≤ s →
      firstAtomCorrection m p₀ s ≤ (2 * K) / ((s + 1 : ℕ) : ℝ) ^ 2 := by
    intro s hs
    calc
      firstAtomCorrection m p₀ s ≤ 2 * orbitTransportDefect m p₀ s :=
        firstAtomCorrection_le_two_mul_defect
          m p₀ hm hcrit hnotBinaryFixedPoint s (hhalf s hs)
      _ ≤ 2 * (K / ((s + 1 : ℕ) : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa [K] using
          orbitTransportDefect_le_of_positiveTiltMass_bound
            m p₀ (by omega) hcrit Ctheta hCtheta.le (fun n ↦ (htheta n).2) s
      _ = (2 * K) / ((s + 1 : ℕ) : ℝ) ^ 2 := by ring
  refine ⟨Ctheta + 4 * K, add_pos_of_pos_of_nonneg hCtheta (mul_nonneg (by norm_num) hK),
    N, fun n hn ↦ ⟨?_, ?_⟩⟩
  · rw [firstTiltedAtomTail]
    exact tsum_nonneg fun j ↦ normalizedTilt_nonneg m (orbit m p₀ (n + j)) (by omega)
      (orbit_critical m p₀ (by omega) hcrit (n + j)) 1
  · rw [firstTiltedAtomTail_eq_theta_add_correctionTail
      m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess n]
    have hcorrectionTail := firstAtomCorrectionTail_le_of_eventual_bound
      m p₀ hm hcrit hnotBinaryFixedPoint (2 * K) (mul_nonneg (by norm_num) hK) N
        hcorrectionBound n hn
    calc
      orbitPositiveTiltMass m p₀ n +
          (∑' j : ℕ, firstAtomCorrection m p₀ (n + j)) ≤
        Ctheta / ((n + 1 : ℕ) : ℝ) +
          (2 * (2 * K)) / ((n + 1 : ℕ) : ℝ) :=
        add_le_add (htheta n).2 hcorrectionTail
      _ = (Ctheta + 4 * K) / ((n + 1 : ℕ) : ℝ) := by ring

/-- Uniform version of the source atom-tail estimate, valid for every `n ≥ 0`.
The finite prefix is absorbed into the witness constant using nonnegativity of the
summable first-atom series. -/
theorem firstTiltedAtomTail_bound_all
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      0 ≤ firstTiltedAtomTail m p₀ n ∧
        firstTiltedAtomTail m p₀ n ≤ C / ((n + 1 : ℕ) : ℝ) := by
  rcases firstTiltedAtomTail_bound_eventually
      m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess with
    ⟨C, hC, N, htail⟩
  let Tzero := firstTiltedAtomTail m p₀ 0
  have hTzero : 0 ≤ Tzero :=
    firstTiltedAtomTail_nonneg m p₀ (by omega) hcrit 0
  let C' := C + (N : ℝ) * Tzero
  have hC' : 0 < C' := by
    exact add_pos_of_pos_of_nonneg hC (mul_nonneg (Nat.cast_nonneg N) hTzero)
  refine ⟨C', hC', fun n ↦ ⟨firstTiltedAtomTail_nonneg m p₀ (by omega) hcrit n, ?_⟩⟩
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  by_cases hn : N ≤ n
  · calc
      firstTiltedAtomTail m p₀ n ≤ C / ((n + 1 : ℕ) : ℝ) := (htail n hn).2
      _ ≤ C' / ((n + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hden.le
        dsimp [C']
        exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg N) hTzero)
  · have hnN : n + 1 ≤ N := by omega
    have hnNReal : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have htailZero := firstTiltedAtomTail_le_zero
      m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess n
    have hprefix : Tzero ≤ ((N : ℝ) * Tzero) / ((n + 1 : ℕ) : ℝ) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    calc
      firstTiltedAtomTail m p₀ n ≤ Tzero := by simpa [Tzero] using htailZero
      _ ≤ ((N : ℝ) * Tzero) / ((n + 1 : ℕ) : ℝ) := hprefix
      _ ≤ C' / ((n + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hden.le
        dsimp [C']
        exact le_add_of_nonneg_left hC.le

end

end DerridaRetaux
