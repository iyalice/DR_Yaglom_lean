import DerridaRetaux.Analysis.MeanConsequences
import DerridaRetaux.Prelim.AtomTail
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-!
# Geometric domination of fixed atoms

This file supplies the domination step in unnumbered obligation `U16`.  The
published excess bound and the pointwise density estimate remain separate,
explicit theorem parameters.  No profile conclusion is assumed or hidden.
-/

/-- The published `O(1/(n+1))` excess estimate already implies `G_n -> 1`. -/
theorem orbitPartition_tendsto_one_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    Tendsto
      (fun n : ℕ ↦ tiltedPartition m (orbit m p₀ n))
      atTop (nhds 1) := by
  rcases orbitExcess_bound_all
      m p₀ hm hcrit hthird hnonconstant hExcess with ⟨C, hC, hbound⟩
  have hupper : Tendsto
      (fun n : ℕ ↦ C / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (tendsto_add_atTop_nat 1)
  have hexcess : Tendsto (orbitExcess m p₀) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n ↦ (hbound n).1)
      (Eventually.of_forall fun n ↦ (hbound n).2) hupper
  have hadd := hexcess.add_const 1
  simpa only [orbitExcess, excess_add_one, zero_add] using hadd

/-- A cubic weighted pointwise bound controls the unweighted density at the
source scale by the same numerator. -/
theorem natSquare_mul_density_le_of_weightedSup
    (f : ℕ → Seq) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n j : ℕ, 0 ≤ f n j)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ) (f n)
        (B / ((n + 1 : ℕ) : ℝ) ^ 2))
    (n j : ℕ) :
    (n : ℝ) ^ 2 * f n j ≤ B := by
  let L : ℝ := ((n + 1 : ℕ) : ℝ)
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hweight : 1 ≤ cubicWeight L j := by
    unfold cubicWeight
    have hbase : 1 ≤ 1 + (j : ℝ) / L :=
      le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg j) hL.le)
    nlinarith [sq_nonneg (1 + (j : ℝ) / L),
      mul_le_mul_of_nonneg_left hbase (sq_nonneg (1 + (j : ℝ) / L))]
  have hpoint := hSup n j
  have hfj : 0 ≤ f n j := hf n j
  rw [abs_of_nonneg hfj] at hpoint
  have hunweighted : f n j ≤ B / L ^ 2 := by
    calc
      f n j ≤ cubicWeight L j * f n j := by
        nlinarith [mul_le_mul_of_nonneg_right hweight hfj]
      _ ≤ B / L ^ 2 := by simpa only [L] using hpoint
  have hnL : (n : ℝ) ≤ L := by
    dsimp only [L]
    norm_num
  have hsquare : (n : ℝ) ^ 2 ≤ L ^ 2 := by gcongr
  have hquotient : (n : ℝ) ^ 2 / L ^ 2 ≤ 1 := by
    exact (div_le_one (sq_pos_of_pos hL)).2 hsquare
  calc
    (n : ℝ) ^ 2 * f n j ≤ (n : ℝ) ^ 2 * (B / L ^ 2) :=
      mul_le_mul_of_nonneg_left hunweighted (sq_nonneg _)
    _ = ((n : ℝ) ^ 2 / L ^ 2) * B := by ring
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hquotient hB
    _ = B := one_mul B

/-- The exact atom readout and `eq:sup` give the manuscript's uniform
geometric majorant `n^2 P(X_n=k) <= C m^{-k}`. -/
theorem orbit_fixedAtom_geometric_bound_of_H1_and_pointwise
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (B : ℝ) (hB : 0 ≤ B)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (rho m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k →
      (n : ℝ) ^ 2 * orbit m p₀ n k ≤
        C * ((m : ℝ)⁻¹) ^ k := by
  rcases orbitExcess_bound_all
      m p₀ hm hcrit hthird hnonconstant hExcess with ⟨A, hA, hbound⟩
  let C : ℝ := (1 + A) * B / ((m : ℝ) - 1) + 1
  have hmFactor : 0 < (m : ℝ) - 1 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show 1 < m by omega)
    linarith
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n k hk
  have hcritn := orbit_critical m p₀ (by omega) hcrit n
  have hGnonneg : 0 ≤ tiltedPartition m (orbit m p₀ n) :=
    (tiltedPartition_pos_of_critical m (orbit m p₀ n) (by omega) hcritn).le
  have hdenOne : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have hAdiv : A / ((n + 1 : ℕ) : ℝ) ≤ A :=
    (div_le_self hA.le hdenOne)
  have hGupper : tiltedPartition m (orbit m p₀ n) ≤ 1 + A := by
    rw [← excess_add_one]
    change orbitExcess m p₀ n + 1 ≤ 1 + A
    linarith [(hbound n).2]
  have hrhoNonneg : ∀ s j : ℕ, 0 ≤ rho m (orbit m p₀ s) j := by
    intro s j
    exact positiveTiltedDensity_nonneg m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s) j
  have hrhoScaled := natSquare_mul_density_le_of_weightedSup
    (fun s ↦ rho m (orbit m p₀ s)) B hB hrhoNonneg hSup n (k - 1)
  have hinvPowNonneg : 0 ≤ ((m : ℝ)⁻¹) ^ k := by positivity
  have hcoefficient :
      0 ≤ tiltedPartition m (orbit m p₀ n) / ((m : ℝ) - 1) *
        ((m : ℝ)⁻¹) ^ k :=
    mul_nonneg (div_nonneg hGnonneg hmFactor.le) hinvPowNonneg
  rw [atom_eq_partition_mul_rho m (orbit m p₀ n) hm hcritn k hk]
  rw [← inv_pow]
  calc
    (n : ℝ) ^ 2 *
          (tiltedPartition m (orbit m p₀ n) / ((m : ℝ) - 1) *
            ((m : ℝ)⁻¹) ^ k * rho m (orbit m p₀ n) (k - 1)) =
        (tiltedPartition m (orbit m p₀ n) / ((m : ℝ) - 1) *
          ((m : ℝ)⁻¹) ^ k) *
            ((n : ℝ) ^ 2 * rho m (orbit m p₀ n) (k - 1)) := by ring
    _ ≤ (tiltedPartition m (orbit m p₀ n) / ((m : ℝ) - 1) *
          ((m : ℝ)⁻¹) ^ k) * B :=
      mul_le_mul_of_nonneg_left hrhoScaled hcoefficient
    _ ≤ ((1 + A) / ((m : ℝ) - 1) * ((m : ℝ)⁻¹) ^ k) * B := by
      have hquotient := div_le_div_of_nonneg_right hGupper hmFactor.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hquotient hinvPowNonneg) hB
    _ ≤ C * ((m : ℝ)⁻¹) ^ k := by
      dsimp only [C]
      have hbaseNonneg : 0 ≤ (1 + A) * B / ((m : ℝ) - 1) := by positivity
      calc
        ((1 + A) / ((m : ℝ) - 1) * ((m : ℝ)⁻¹) ^ k) * B =
            ((1 + A) * B / ((m : ℝ) - 1)) * ((m : ℝ)⁻¹) ^ k := by ring
        _ ≤ (((1 + A) * B / ((m : ℝ) - 1)) + 1) *
              ((m : ℝ)⁻¹) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) hinvPowNonneg

end

end DerridaRetaux
