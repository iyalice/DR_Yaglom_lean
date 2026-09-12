import DerridaRetaux.Analysis.DensityMassLimit
import DerridaRetaux.Analysis.OrbitConvolutionBounds
import DerridaRetaux.Prelim.WeightedMassOrbit
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

/-!
# Total density mass by fixed macroscopic cutoffs

This file removes the need to assume a preselected escaping diagonal cutoff.
For each fixed natural `M`, split at `M * (n + 1)`, first let `n` tend to
infinity, and only then let `M` tend to infinity.  The order of these two
limits is explicit in the proof.
-/

noncomputable section

/-- A fixed macroscopic coefficient cutoff. -/
def linearProfileCutoff (M n : ℕ) : ℕ := M * (n + 1)

/-- The cutoff-to-mesh ratio for a fixed macroscopic window tends to `M`. -/
theorem linearProfileCutoff_ratio_tendsto (M : ℕ) :
    Tendsto
      (fun n : ℕ ↦ (linearProfileCutoff M n : ℝ) / (n : ℝ))
      atTop (nhds (M : ℝ)) := by
  have hzero := tendsto_const_div_atTop_nhds_zero_nat (M : ℝ)
  have hsum : Tendsto
      (fun n : ℕ ↦ (M : ℝ) + (M : ℝ) / (n : ℝ))
      atTop (nhds ((M : ℝ) + 0)) := tendsto_const_nhds.add hzero
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp only [linearProfileCutoff]
  push_cast
  field_simp only [hn0]
  ring

/-- At a fixed macroscopic cutoff, the comparison-grid tail has the exact
limit `2 * exp (-2M)`. -/
theorem exponentialProfileGridTail_linearCutoff_tendsto (M : ℕ) :
    Tendsto
      (exponentialProfileGridTail (linearProfileCutoff M))
      atTop (nhds (2 * Real.exp (-2 * (M : ℝ)))) := by
  have hratio := linearProfileCutoff_ratio_tendsto M
  have hexponent : Tendsto
      (fun n : ℕ ↦ -2 *
        ((linearProfileCutoff M n : ℝ) / (n : ℝ)))
      atTop (nhds (-2 * (M : ℝ))) := tendsto_const_nhds.mul hratio
  have hexp : Tendsto
      (fun n : ℕ ↦ Real.exp (-2 *
        ((linearProfileCutoff M n : ℝ) / (n : ℝ))))
      atTop (nhds (Real.exp (-2 * (M : ℝ)))) :=
    (Real.continuous_exp.tendsto _).comp hexponent
  have hproduct := hexp.mul exponentialProfileGrid_tsum_tendsto_two
  have hproduct' : Tendsto
      (fun n : ℕ ↦ Real.exp (-2 *
          ((linearProfileCutoff M n : ℝ) / (n : ℝ))) *
        ∑' j : ℕ, exponentialProfileGrid n j)
      atTop (nhds (2 * Real.exp (-2 * (M : ℝ)))) := by
    simpa only [mul_comm] using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [exponentialProfileGridTail_eq (linearProfileCutoff M) n (by omega)]
  congr 2
  ring

/-- The cubic weighted norm makes the source tail beyond `M(n+1)` uniformly
small in the generation. -/
theorem scaledDensityTailL1_linearCutoff_le
    (f : ℕ → Seq) (A : ℝ) (hA : 0 ≤ A) (M n : ℕ)
    (hsum : Summable (weightedAbs ((n + 1 : ℕ) : ℝ) (f n)))
    (hweighted : weightedL1Three ((n + 1 : ℕ) : ℝ) (f n) ≤
      A / ((n + 1 : ℕ) : ℝ)) :
    scaledDensityTailL1 f (linearProfileCutoff M) n ≤
      A / (1 + (M : ℝ)) ^ 3 := by
  let L : ℝ := ((n + 1 : ℕ) : ℝ)
  have hL : 0 < L := by positivity
  have htail := abs_coefficientTail_le_weightedL1Three_div
    L hL (f n) (by simpa only [L] using hsum) (linearProfileCutoff M n)
  have hweight : 0 < cubicWeight L (linearProfileCutoff M n) :=
    cubicWeight_pos L hL _
  have hfirst : scaledDensityTailL1 f (linearProfileCutoff M) n ≤
      (n : ℝ) *
        ((A / L) / cubicWeight L (linearProfileCutoff M n)) := by
    rw [scaledDensityTailL1]
    calc
      (n : ℝ) * ∑' j : ℕ, |f n (j + linearProfileCutoff M n)| ≤
          (n : ℝ) *
            (weightedL1Three L (f n) /
              cubicWeight L (linearProfileCutoff M n)) :=
        mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) *
          ((A / L) / cubicWeight L (linearProfileCutoff M n)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        exact div_le_div_of_nonneg_right (by simpa only [L] using hweighted) hweight.le
  calc
    scaledDensityTailL1 f (linearProfileCutoff M) n ≤
        (n : ℝ) *
          ((A / L) / cubicWeight L (linearProfileCutoff M n)) := hfirst
    _ = (((n : ℝ) / L) * A) / (1 + (M : ℝ)) ^ 3 := by
      dsimp only [cubicWeight, linearProfileCutoff, L]
      push_cast
      field_simp
    _ ≤ A / (1 + (M : ℝ)) ^ 3 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (by positivity) 3)
      have hratio : (n : ℝ) / L ≤ 1 := by
        apply (div_le_one hL).2
        dsimp only [L]
        exact_mod_cast Nat.le_succ n
      calc
        ((n : ℝ) / L) * A = A * ((n : ℝ) / L) := by ring
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hratio hA
        _ = A := mul_one A

/-- The uniform source-tail majorant vanishes when the macroscopic cutoff is
sent to infinity. -/
theorem const_div_linearCutoffCube_tendsto_zero (A : ℝ) :
    Tendsto (fun M : ℕ ↦ A / (1 + (M : ℝ)) ^ 3) atTop (nhds 0) := by
  have hbase : Tendsto (fun M : ℕ ↦ 1 + (M : ℝ)) atTop atTop :=
    tendsto_atTop_mono
      (fun M : ℕ ↦ (show (M : ℝ) ≤ 1 + (M : ℝ) by linarith))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcube : Tendsto (fun M : ℕ ↦ (1 + (M : ℝ)) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (show (3 : ℕ) ≠ 0 by norm_num)).comp hbase
  exact hcube.const_div_atTop A

/-- The limiting exponential-grid tail vanishes as the fixed macroscopic
cutoff tends to infinity. -/
theorem exponentialProfile_limitTail_tendsto_zero :
    Tendsto (fun M : ℕ ↦ 2 * Real.exp (-2 * (M : ℝ))) atTop (nhds 0) := by
  have hnegative : Tendsto (fun M : ℕ ↦ -2 * (M : ℝ)) atTop atBot :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (by norm_num)
  simpa only [mul_zero] using
    tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hnegative)

/-- Local convergence on every fixed macroscopic window plus one uniform
cubic weighted-mass estimate implies global `l1` convergence to the
exponential comparison grid. -/
theorem densityProfileL1Error_tendsto_zero_of_fixed_windows
    (f : ℕ → Seq) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n : ℕ, 0 < n → Summable (f n))
    (hweightedSummable : ∀ n : ℕ,
      Summable (weightedAbs ((n + 1 : ℕ) : ℝ) (f n)))
    (hweighted : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ) (f n) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hlocal : ∀ M : ℕ,
      Tendsto (densityProfilePrefixL1Error f (linearProfileCutoff M))
        atTop (nhds 0)) :
    Tendsto (densityProfileL1Error f) atTop (nhds 0) := by
  have hcutoffBound : Tendsto
      (fun M : ℕ ↦ A / (1 + (M : ℝ)) ^ 3 +
        2 * Real.exp (-2 * (M : ℝ)))
      atTop (nhds 0) := by
    simpa only [zero_add] using
      (const_div_linearCutoffCube_tendsto_zero A).add
        exponentialProfile_limitTail_tendsto_zero
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.mp hcutoffBound ε hε
  let M := M₀
  have hMdist := hM₀ M₀ le_rfl
  have hsourceNonneg : 0 ≤ A / (1 + (M : ℝ)) ^ 3 :=
    div_nonneg hA (pow_nonneg (by positivity) 3)
  have hlimitNonneg : 0 ≤ 2 * Real.exp (-2 * (M : ℝ)) := by positivity
  have hMsmall :
      A / (1 + (M : ℝ)) ^ 3 + 2 * Real.exp (-2 * (M : ℝ)) < ε := by
    simpa only [M, Real.dist_eq, sub_zero,
      abs_of_nonneg (add_nonneg hsourceNonneg hlimitNonneg)] using hMdist
  let gap := ε - A / (1 + (M : ℝ)) ^ 3 - 2 * Real.exp (-2 * (M : ℝ))
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hcombined : Tendsto
      (fun n : ℕ ↦
        densityProfilePrefixL1Error f (linearProfileCutoff M) n +
          exponentialProfileGridTail (linearProfileCutoff M) n)
      atTop (nhds (2 * Real.exp (-2 * (M : ℝ)))) := by
    simpa only [zero_add] using
      (hlocal M).add (exponentialProfileGridTail_linearCutoff_tendsto M)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hcombined gap hgap
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hnOne : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnear := hN n hnN
  rw [Real.dist_eq] at hnear
  have hcombinedUpper := (abs_lt.mp hnear).2
  have htail := scaledDensityTailL1_linearCutoff_le
    f A hA M n (hweightedSummable n) (hweighted n)
  have hfull := densityProfileL1Error_le_cutoff
    f (linearProfileCutoff M) n (by omega) (hf n (by omega))
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (tsum_nonneg fun _ ↦ abs_nonneg _)]
  calc
    densityProfileL1Error f n ≤
        densityProfilePrefixL1Error f (linearProfileCutoff M) n +
          scaledDensityTailL1 f (linearProfileCutoff M) n +
            exponentialProfileGridTail (linearProfileCutoff M) n := hfull
    _ ≤ densityProfilePrefixL1Error f (linearProfileCutoff M) n +
          A / (1 + (M : ℝ)) ^ 3 +
            exponentialProfileGridTail (linearProfileCutoff M) n := by linarith
    _ < ε := by dsimp only [gap] at hcombinedUpper ⊢; linarith

/-- Fixed-window local convergence and a uniform weighted-mass estimate give
the total density mass `2`. -/
theorem scaled_tsum_tendsto_two_of_fixed_windows_and_weighted_mass
    (f : ℕ → Seq) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n : ℕ, 0 < n → Summable (f n))
    (hweightedSummable : ∀ n : ℕ,
      Summable (weightedAbs ((n + 1 : ℕ) : ℝ) (f n)))
    (hweighted : ∀ n : ℕ,
      weightedL1Three ((n + 1 : ℕ) : ℝ) (f n) ≤
        A / ((n + 1 : ℕ) : ℝ))
    (hlocal : ∀ M : ℕ,
      Tendsto (densityProfilePrefixL1Error f (linearProfileCutoff M))
        atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ∑' j : ℕ, f n j) atTop (nhds 2) :=
  scaled_tsum_tendsto_two_of_profileL1Error f hf
    (densityProfileL1Error_tendsto_zero_of_fixed_windows
      f A hA hf hweightedSummable hweighted hlocal)

/-- Orbit specialization: the approved H1 facts enter only through the
already-compiled cubic weighted-mass theorem, while fixed-window profile
convergence stays an explicit internal hypothesis. -/
theorem orbit_densityTotalMass_tendsto_two_of_fixed_windows
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant)
    (hlocal : ∀ M : ℕ,
      Tendsto
        (densityProfilePrefixL1Error
          (fun n ↦ positiveTiltedDensity m (orbit m p₀ n))
          (linearProfileCutoff M))
        atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * densityTotalMass m (orbit m p₀ n))
      atTop (nhds 2) := by
  rcases weightedL1Three_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with ⟨A, hA, hweighted⟩
  have hsummable : ∀ n : ℕ, 0 < n →
      Summable (positiveTiltedDensity m (orbit m p₀ n)) := by
    intro n _
    exact (positiveTiltedDensity_hasSum m (orbit m p₀ n) (by omega)
      (orbit_critical m p₀ (by omega) hcrit n)).summable
  have hweightedSummable : ∀ n : ℕ,
      Summable (weightedAbs ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))) :=
    weightedAbs_positiveTiltedDensity_orbit_summable m p₀ hm hcrit hthird
  simpa only [densityTotalMass, rho] using
    scaled_tsum_tendsto_two_of_fixed_windows_and_weighted_mass
      (fun n ↦ positiveTiltedDensity m (orbit m p₀ n))
      A hA.le hsummable hweightedSummable hweighted hlocal

end

end DerridaRetaux
