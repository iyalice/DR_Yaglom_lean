import DerridaRetaux.Analysis.ExcessConsequences
import DerridaRetaux.Analysis.ExponentialGrid
import DerridaRetaux.Analysis.WeightedNorm
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

/-!
# Total density mass from local profile control and tails

This file isolates the uniform-integrability step after local convergence to the
profile `4 * exp (-2x)`.  Every analytic input is a literal theorem parameter:
the prefix profile error, a weighted `l1` tail estimate, and growth of the cutoff.
-/

noncomputable section

/-- The mass-normalized exponential profile on the mesh `j / n`. -/
def exponentialProfileGrid (n j : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * (4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ))))

/-- The `l1` discrepancy between a scaled density and the exponential grid. -/
def densityProfileL1Error (f : ℕ → Seq) (n : ℕ) : ℝ :=
  ∑' j : ℕ, |(n : ℝ) * f n j - exponentialProfileGrid n j|

/-- The profile discrepancy before a moving coefficient cutoff. -/
def densityProfilePrefixL1Error (f : ℕ → Seq) (K : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K n),
    |(n : ℝ) * f n j - exponentialProfileGrid n j|

/-- The scaled absolute mass of the density after a moving cutoff. -/
def scaledDensityTailL1 (f : ℕ → Seq) (K : ℕ → ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) * ∑' j : ℕ, |f n (j + K n)|

/-- The mass of the exponential comparison grid after a moving cutoff. -/
def exponentialProfileGridTail (K : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, exponentialProfileGrid n (j + K n)

theorem exponentialProfileGrid_nonneg (n j : ℕ) :
    0 ≤ exponentialProfileGrid n j := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (by positivity)

theorem exponentialProfileGrid_summable (n : ℕ) (hn : 0 < n) :
    Summable (exponentialProfileGrid n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let r : ℝ := Real.exp (-2 / (n : ℝ))
  have hexponent : -2 / (n : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) hnpos
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr hexponent
  have hgeom : Summable (fun j : ℕ ↦ r ^ j) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hterms : exponentialProfileGrid n =
      fun j : ℕ ↦ ((n : ℝ)⁻¹ * 4) * r ^ j := by
    funext j
    have hexp : Real.exp (-2 * ((j : ℝ) / (n : ℝ))) = r ^ j := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp only [r]
      field_simp only [hnpos.ne']
      ring
    rw [exponentialProfileGrid, hexp]
    ring
  rw [hterms]
  exact hgeom.mul_left ((n : ℝ)⁻¹ * 4)

/-- `ExponentialGrid` supplies the total mass of the normalized comparison grid. -/
theorem exponentialProfileGrid_tsum_tendsto_two :
    Tendsto (fun n : ℕ ↦ ∑' j : ℕ, exponentialProfileGrid n j)
      atTop (nhds 2) := by
  simpa only [exponentialProfileGrid, tsum_mul_left] using
    exponentialProfile_gridMass_tendsto_two

/-- Exact translation formula for the exponential-grid tail. -/
theorem exponentialProfileGridTail_eq
    (K : ℕ → ℕ) (n : ℕ) (hn : 0 < n) :
    exponentialProfileGridTail K n =
      Real.exp (-2 * ((K n : ℕ) : ℝ) / (n : ℝ)) *
        ∑' j : ℕ, exponentialProfileGrid n j := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold exponentialProfileGridTail
  rw [show (fun j : ℕ ↦ exponentialProfileGrid n (j + K n)) =
      fun j : ℕ ↦ Real.exp (-2 * ((K n : ℕ) : ℝ) / (n : ℝ)) *
        exponentialProfileGrid n j by
    funext j
    have hexponent :
        -2 * (((j + K n : ℕ) : ℝ) / (n : ℝ)) =
          -2 * ((K n : ℕ) : ℝ) / (n : ℝ) +
            -2 * ((j : ℝ) / (n : ℝ)) := by
      push_cast
      field_simp only [hn0]
      ring
    rw [exponentialProfileGrid, exponentialProfileGrid, hexponent, Real.exp_add]
    ring]
  exact tsum_mul_left

/-- A cutoff escaping every profile scale makes the exponential comparison tail
vanish. -/
theorem exponentialProfileGridTail_tendsto_zero
    (K : ℕ → ℕ)
    (hK : Tendsto (fun n : ℕ ↦ (K n : ℝ) / (n : ℝ)) atTop atTop) :
    Tendsto (exponentialProfileGridTail K) atTop (nhds 0) := by
  have hnegative :
      Tendsto (fun n : ℕ ↦ -2 * ((K n : ℝ) / (n : ℝ))) atTop atBot :=
    hK.const_mul_atTop_of_neg (by norm_num)
  have hexp :
      Tendsto (fun n : ℕ ↦ Real.exp (-2 * ((K n : ℝ) / (n : ℝ))))
        atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hproduct := hexp.mul exponentialProfileGrid_tsum_tendsto_two
  have hproduct' : Tendsto
      (fun n : ℕ ↦
        Real.exp (-2 * ((K n : ℝ) / (n : ℝ))) *
          ∑' j : ℕ, exponentialProfileGrid n j)
      atTop (nhds 0) := by
    simpa only [zero_mul] using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [exponentialProfileGridTail_eq K n (by omega)]
  congr 2
  ring

/-- On a positive mesh, the prefix error is exactly the Riemann normalization
of the source's quadratic-scale coefficient error. -/
theorem densityProfilePrefixL1Error_eq_rescaled
    (f : ℕ → Seq) (K : ℕ → ℕ) (n : ℕ) (hn : 0 < n) :
    densityProfilePrefixL1Error f K n =
      (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (K n),
        |(n : ℝ) ^ 2 * f n j -
          4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))| := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [densityProfilePrefixL1Error, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have halgebra :
      (n : ℝ) * f n j - exponentialProfileGrid n j =
        (n : ℝ)⁻¹ * ((n : ℝ) ^ 2 * f n j -
          4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))) := by
    rw [exponentialProfileGrid]
    field_simp only [hnpos.ne']
    ring
  rw [halgebra, abs_mul, abs_of_pos (inv_pos.mpr hnpos)]

/-- A pointwise profile error on the cutoff window bounds the integrated prefix
error by `(K_n / n) * error_n`. -/
theorem densityProfilePrefixL1Error_le_uniform
    (f : ℕ → Seq) (K : ℕ → ℕ) (error : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n)
    (hprofile : ∀ j : ℕ, j < K n →
      |(n : ℝ) ^ 2 * f n j -
        4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))| ≤ error n) :
    densityProfilePrefixL1Error f K n ≤
      ((K n : ℝ) / (n : ℝ)) * error n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [densityProfilePrefixL1Error_eq_rescaled f K n hn]
  calc
    (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (K n),
        |(n : ℝ) ^ 2 * f n j -
          4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))| ≤
        (n : ℝ)⁻¹ * ∑ _j ∈ Finset.range (K n), error n := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hnpos.le)
      apply Finset.sum_le_sum
      intro j hj
      exact hprofile j (Finset.mem_range.mp hj)
    _ = ((K n : ℝ) / (n : ℝ)) * error n := by
      simp [Finset.sum_const, div_eq_mul_inv]
      ring

/-- A literal uniform profile estimate whose integrated error vanishes supplies
the prefix hypothesis used in the mass-limit theorem. -/
theorem densityProfilePrefixL1Error_tendsto_zero_of_uniform
    (f : ℕ → Seq) (K : ℕ → ℕ) (error : ℕ → ℝ)
    (hprofile : ∀ n : ℕ, 0 < n → ∀ j : ℕ, j < K n →
      |(n : ℝ) ^ 2 * f n j -
        4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))| ≤ error n)
    (hintegrated : Tendsto
      (fun n : ℕ ↦ ((K n : ℝ) / (n : ℝ)) * error n)
      atTop (nhds 0)) :
    Tendsto (densityProfilePrefixL1Error f K) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact densityProfilePrefixL1Error_le_uniform
      f K error n (by omega) (hprofile n (by omega))
  · exact hintegrated

/-- The weighted `l1` norm controls every unweighted coefficient tail. -/
theorem abs_coefficientTail_le_weightedL1Three_div
    (L : ℝ) (hL : 0 < L) (f : Seq)
    (hf : Summable (weightedAbs L f)) (K : ℕ) :
    (∑' j : ℕ, |f (j + K)|) ≤
      weightedL1Three L f / cubicWeight L K := by
  have hweight : 0 < cubicWeight L K := cubicWeight_pos L hL K
  have htailWeighted : Summable (fun j : ℕ ↦ weightedAbs L f (j + K)) :=
    (summable_nat_add_iff K).2 hf
  have hmajor :
      Summable (fun j : ℕ ↦
        (cubicWeight L K)⁻¹ * weightedAbs L f (j + K)) :=
    htailWeighted.mul_left (cubicWeight L K)⁻¹
  have htailAbs : Summable (fun j : ℕ ↦ |f (j + K)|) := by
    apply Summable.of_nonneg_of_le
      (f := fun j : ℕ ↦ (cubicWeight L K)⁻¹ * weightedAbs L f (j + K))
    · exact fun _ ↦ abs_nonneg _
    · intro j
      have hmono : cubicWeight L K ≤ cubicWeight L (j + K) :=
        cubicWeight_mono L hL (by omega)
      calc
        |f (j + K)| =
            (cubicWeight L K)⁻¹ *
              (cubicWeight L K * |f (j + K)|) := by
          field_simp only [hweight.ne']
          ring
        _ ≤ (cubicWeight L K)⁻¹ *
              (cubicWeight L (j + K) * |f (j + K)|) := by
          gcongr
        _ = (cubicWeight L K)⁻¹ * weightedAbs L f (j + K) := rfl
    · exact hmajor
  have htailBound :
      (∑' j : ℕ, |f (j + K)|) ≤
        (cubicWeight L K)⁻¹ *
          ∑' j : ℕ, weightedAbs L f (j + K) := by
    rw [← htailWeighted.tsum_mul_left]
    exact Summable.tsum_le_tsum (fun j ↦ by
      have hmono : cubicWeight L K ≤ cubicWeight L (j + K) :=
        cubicWeight_mono L hL (by omega)
      calc
        |f (j + K)| =
            (cubicWeight L K)⁻¹ *
              (cubicWeight L K * |f (j + K)|) := by
          field_simp only [hweight.ne']
          ring
        _ ≤ (cubicWeight L K)⁻¹ *
              (cubicWeight L (j + K) * |f (j + K)|) := by
          gcongr
        _ = (cubicWeight L K)⁻¹ * weightedAbs L f (j + K) := rfl)
      htailAbs hmajor
  calc
    (∑' j : ℕ, |f (j + K)|) ≤
        (cubicWeight L K)⁻¹ *
          ∑' j : ℕ, weightedAbs L f (j + K) := htailBound
    _ ≤ (cubicWeight L K)⁻¹ * weightedL1Three L f := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hweight.le)
      rw [weightedL1Three_eq_tsum_weightedAbs,
        ← hf.sum_add_tsum_nat_add K]
      exact le_add_of_nonneg_left
        (Finset.sum_nonneg fun j _ ↦ weightedAbs_nonneg L hL f j)
    _ = weightedL1Three L f / cubicWeight L K := by
      rw [div_eq_mul_inv]
      ring

/-- A literal weighted-tail rate implies the scaled unweighted tail rate. -/
theorem scaledDensityTailL1_tendsto_zero_of_weighted
    (f : ℕ → Seq) (L : ℕ → ℝ) (K : ℕ → ℕ)
    (hL : ∀ n : ℕ, 0 < L n)
    (hsum : ∀ n : ℕ, Summable (weightedAbs (L n) (f n)))
    (hweighted : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          (weightedL1Three (L n) (f n) / cubicWeight (L n) (K n)))
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ scaledDensityTailL1 f K n) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact mul_nonneg (Nat.cast_nonneg n) (tsum_nonneg fun _ ↦ abs_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (abs_coefficientTail_le_weightedL1Three_div
        (L n) (hL n) (f n) (hsum n) (K n))
      (Nat.cast_nonneg n)
  · exact hweighted

/-- Splitting at a cutoff bounds the global discrepancy by the prefix error and
the two absolute tails. -/
theorem densityProfileL1Error_le_cutoff
    (f : ℕ → Seq) (K : ℕ → ℕ) (n : ℕ) (hn : 0 < n)
    (hf : Summable (f n)) :
    densityProfileL1Error f n ≤
      densityProfilePrefixL1Error f K n +
        scaledDensityTailL1 f K n + exponentialProfileGridTail K n := by
  have hgrid := exponentialProfileGrid_summable n hn
  have hscaled : Summable (fun j : ℕ ↦ (n : ℝ) * f n j) :=
    hf.mul_left (n : ℝ)
  have hdiff : Summable (fun j : ℕ ↦
      (n : ℝ) * f n j - exponentialProfileGrid n j) :=
    hscaled.sub hgrid
  have herror : Summable (fun j : ℕ ↦
      |(n : ℝ) * f n j - exponentialProfileGrid n j|) := by
    simpa only [Real.norm_eq_abs] using hdiff.norm
  have htailDensity : Summable (fun j : ℕ ↦ |f n (j + K n)|) := by
    simpa only [Real.norm_eq_abs] using ((summable_nat_add_iff (K n)).2 hf).norm
  have htailGrid : Summable (fun j : ℕ ↦
      exponentialProfileGrid n (j + K n)) :=
    (summable_nat_add_iff (K n)).2 hgrid
  have htailMajor : Summable (fun j : ℕ ↦
      (n : ℝ) * |f n (j + K n)| +
        exponentialProfileGrid n (j + K n)) :=
    (htailDensity.mul_left (n : ℝ)).add htailGrid
  have htailError : Summable (fun j : ℕ ↦
      |(n : ℝ) * f n (j + K n) -
        exponentialProfileGrid n (j + K n)|) :=
    (summable_nat_add_iff (K n)).2 herror
  rw [densityProfileL1Error, ← herror.sum_add_tsum_nat_add (K n)]
  change densityProfilePrefixL1Error f K n +
      (∑' j : ℕ, |(n : ℝ) * f n (j + K n) -
        exponentialProfileGrid n (j + K n)|) ≤ _
  rw [add_assoc]
  apply add_le_add_left _
  calc
    (∑' j : ℕ, |(n : ℝ) * f n (j + K n) -
        exponentialProfileGrid n (j + K n)|) ≤
        ∑' j : ℕ, ((n : ℝ) * |f n (j + K n)| +
          exponentialProfileGrid n (j + K n)) := by
      apply Summable.tsum_le_tsum _ htailError htailMajor
      intro j
      calc
        |(n : ℝ) * f n (j + K n) -
            exponentialProfileGrid n (j + K n)| ≤
            |(n : ℝ) * f n (j + K n)| +
              |exponentialProfileGrid n (j + K n)| := abs_sub _ _
        _ = (n : ℝ) * |f n (j + K n)| +
              exponentialProfileGrid n (j + K n) := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n),
            abs_of_nonneg (exponentialProfileGrid_nonneg n (j + K n))]
    _ = scaledDensityTailL1 f K n + exponentialProfileGridTail K n := by
      rw [(htailDensity.mul_left (n : ℝ)).tsum_add htailGrid]
      rw [htailDensity.tsum_mul_left]
      rfl

/-- Vanishing prefix and tail errors imply global `l1` profile convergence. -/
theorem densityProfileL1Error_tendsto_zero_of_cutoff
    (f : ℕ → Seq) (K : ℕ → ℕ)
    (hf : ∀ n : ℕ, 0 < n → Summable (f n))
    (hprefix : Tendsto (densityProfilePrefixL1Error f K) atTop (nhds 0))
    (htail : Tendsto (scaledDensityTailL1 f K) atTop (nhds 0))
    (hgridTail : Tendsto (exponentialProfileGridTail K) atTop (nhds 0)) :
    Tendsto (densityProfileL1Error f) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ tsum_nonneg fun _ ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact densityProfileL1Error_le_cutoff f K n (by omega) (hf n (by omega))
  · simpa only [zero_add, add_zero, add_assoc] using
      hprefix.add (htail.add hgridTail)

/-- Global `l1` convergence to the exponential grid gives total mass `2`. -/
theorem scaled_tsum_tendsto_two_of_profileL1Error
    (f : ℕ → Seq)
    (hf : ∀ n : ℕ, 0 < n → Summable (f n))
    (herror : Tendsto (densityProfileL1Error f) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ∑' j : ℕ, f n j) atTop (nhds 2) := by
  apply tendsto_of_abs_sub_le_error exponentialProfileGrid_tsum_tendsto_two herror
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hfn := hf n (by omega)
  have hgrid := exponentialProfileGrid_summable n (by omega)
  have hscaled : Summable (fun j : ℕ ↦ (n : ℝ) * f n j) :=
    hfn.mul_left (n : ℝ)
  have hdiff := hscaled.sub hgrid
  calc
    |(n : ℝ) * (∑' j : ℕ, f n j) -
        ∑' j : ℕ, exponentialProfileGrid n j| =
        ‖∑' j : ℕ,
          ((n : ℝ) * f n j - exponentialProfileGrid n j)‖ := by
      rw [hscaled.tsum_sub hgrid, hfn.tsum_mul_left, Real.norm_eq_abs]
    _ ≤ ∑' j : ℕ,
        ‖(n : ℝ) * f n j - exponentialProfileGrid n j‖ :=
      norm_tsum_le_tsum_norm hdiff.norm
    _ = densityProfileL1Error f n := by
      simp only [densityProfileL1Error, Real.norm_eq_abs]

/-- Main generic passage: a prefix profile estimate, a weighted `l1` tail rate,
and an escaping cutoff imply the total density-mass limit. -/
theorem scaled_tsum_tendsto_two_of_local_profile_and_weighted_tail
    (f : ℕ → Seq) (L : ℕ → ℝ) (K : ℕ → ℕ)
    (hf : ∀ n : ℕ, 0 < n → Summable (f n))
    (hL : ∀ n : ℕ, 0 < L n)
    (hweightedSummable : ∀ n : ℕ, Summable (weightedAbs (L n) (f n)))
    (hcutoff : Tendsto (fun n : ℕ ↦ (K n : ℝ) / (n : ℝ)) atTop atTop)
    (hlocal : Tendsto (densityProfilePrefixL1Error f K) atTop (nhds 0))
    (hweightedTail : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          (weightedL1Three (L n) (f n) / cubicWeight (L n) (K n)))
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ∑' j : ℕ, f n j) atTop (nhds 2) := by
  apply scaled_tsum_tendsto_two_of_profileL1Error f hf
  apply densityProfileL1Error_tendsto_zero_of_cutoff f K hf hlocal
  · exact scaledDensityTailL1_tendsto_zero_of_weighted
      f L K hL hweightedSummable hweightedTail
  · exact exponentialProfileGridTail_tendsto_zero K hcutoff

/-- Pointwise-window version of the main generic passage.  The extra hypothesis
`(K_n / n) * error_n -> 0` is precisely the cost of summing the local uniform
error over the cutoff window. -/
theorem scaled_tsum_tendsto_two_of_uniform_profile_and_weighted_tail
    (f : ℕ → Seq) (L : ℕ → ℝ) (K : ℕ → ℕ) (error : ℕ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → Summable (f n))
    (hL : ∀ n : ℕ, 0 < L n)
    (hweightedSummable : ∀ n : ℕ, Summable (weightedAbs (L n) (f n)))
    (hcutoff : Tendsto (fun n : ℕ ↦ (K n : ℝ) / (n : ℝ)) atTop atTop)
    (hprofile : ∀ n : ℕ, 0 < n → ∀ j : ℕ, j < K n →
      |(n : ℝ) ^ 2 * f n j -
        4 * Real.exp (-2 * ((j : ℝ) / (n : ℝ)))| ≤ error n)
    (hintegrated : Tendsto
      (fun n : ℕ ↦ ((K n : ℝ) / (n : ℝ)) * error n)
      atTop (nhds 0))
    (hweightedTail : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          (weightedL1Three (L n) (f n) / cubicWeight (L n) (K n)))
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ∑' j : ℕ, f n j) atTop (nhds 2) := by
  apply scaled_tsum_tendsto_two_of_local_profile_and_weighted_tail
    f L K hf hL hweightedSummable hcutoff
  · exact densityProfilePrefixL1Error_tendsto_zero_of_uniform
      f K error hprofile hintegrated
  · exact hweightedTail

/-- Orbit specialization, with the local and weighted-tail estimates exposed
literally. -/
theorem orbit_densityTotalMass_tendsto_two_of_local_profile_and_weighted_tail
    (m : ℕ) (p0 : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p0)
    (L : ℕ → ℝ) (K : ℕ → ℕ)
    (hL : ∀ n : ℕ, 0 < L n)
    (hweightedSummable : ∀ n : ℕ,
      Summable (weightedAbs (L n) (rho m (orbit m p0 n))))
    (hcutoff : Tendsto (fun n : ℕ ↦ (K n : ℝ) / (n : ℝ)) atTop atTop)
    (hlocal : Tendsto
      (densityProfilePrefixL1Error (fun n ↦ rho m (orbit m p0 n)) K)
      atTop (nhds 0))
    (hweightedTail : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          (weightedL1Three (L n) (rho m (orbit m p0 n)) /
            cubicWeight (L n) (K n)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * densityTotalMass m (orbit m p0 n))
      atTop (nhds 2) := by
  have hsum : ∀ n : ℕ, 0 < n → Summable (rho m (orbit m p0 n)) := by
    intro n _
    exact (positiveTiltedDensity_hasSum m (orbit m p0 n) (by omega)
      (orbit_critical m p0 (by omega) hcrit n)).summable
  simpa only [densityTotalMass] using
    scaled_tsum_tendsto_two_of_local_profile_and_weighted_tail
      (fun n ↦ rho m (orbit m p0 n)) L K hsum hL hweightedSummable
        hcutoff hlocal hweightedTail

/-- The total-density limit immediately feeds the exact normalization in
`ExcessConsequences`. -/
theorem orbit_positiveTiltMass_tendsto_of_local_profile_and_weighted_tail
    (m : ℕ) (p0 : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p0)
    (L : ℕ → ℝ) (K : ℕ → ℕ)
    (hL : ∀ n : ℕ, 0 < L n)
    (hweightedSummable : ∀ n : ℕ,
      Summable (weightedAbs (L n) (rho m (orbit m p0 n))))
    (hcutoff : Tendsto (fun n : ℕ ↦ (K n : ℝ) / (n : ℝ)) atTop atTop)
    (hlocal : Tendsto
      (densityProfilePrefixL1Error (fun n ↦ rho m (orbit m p0 n)) K)
      atTop (nhds 0))
    (hweightedTail : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          (weightedL1Three (L n) (rho m (orbit m p0 n)) /
            cubicWeight (L n) (K n)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * positiveTiltMass m (orbit m p0 n))
      atTop (nhds (2 / ((m : ℝ) - 1))) := by
  have horbitCrit : ∀ n : ℕ, Critical m (orbit m p0 n) :=
    fun n ↦ orbit_critical m p0 (by omega) hcrit n
  apply scaledPositiveTiltMass_tendsto_of_densityTotalMass
    m (orbit m p0) hm horbitCrit 2
  exact orbit_densityTotalMass_tendsto_two_of_local_profile_and_weighted_tail
    m p0 hm hcrit L K hL hweightedSummable hcutoff hlocal hweightedTail

end

end DerridaRetaux
