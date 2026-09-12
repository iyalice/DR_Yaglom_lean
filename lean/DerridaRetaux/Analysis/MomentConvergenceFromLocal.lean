import DerridaRetaux.Analysis.ContinuumMomentIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace DerridaRetaux

noncomputable section

/-- A smooth compact truncation of a scaled lattice moment. -/
def softScaledDiscreteMoment
    (rho : Seq) (r N R : ℕ) : ℝ :=
  ∑' j : ℕ, (N : ℝ) * rho j *
    positiveMomentCutoff r R ((j : ℝ) / (N : ℝ))

/-- The smooth truncation lies below the full moment, and the omitted part is
bounded by the strict tail beyond `R`. -/
theorem softScaledDiscreteMoment_sandwich
    (rho : Seq) (r N R : ℕ) (hN : 0 < N)
    (hrho : ∀ j : ℕ, 0 ≤ rho j)
    (hmoment : Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho j)) :
    softScaledDiscreteMoment rho r N R ≤
        scaledDiscreteMoment rho r N ∧
      scaledDiscreteMoment rho r N ≤
        softScaledDiscreteMoment rho r N R +
          scaledDiscreteMomentTail rho r N (R : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let fullTerm : ℕ → ℝ := fun j ↦
    ((N : ℝ) / (N : ℝ) ^ r) * ((j : ℝ) ^ r * rho j)
  let softTerm : ℕ → ℝ := fun j ↦
    (N : ℝ) * rho j *
      positiveMomentCutoff r R ((j : ℝ) / (N : ℝ))
  let tailTerm : ℕ → ℝ := fun j ↦
    ((N : ℝ) / (N : ℝ) ^ r) *
      ((j : ℝ) ^ r * rho j *
        strictTailIndicator ((R : ℝ) * (N : ℝ)) (j : ℝ))
  have hfull : Summable fullTerm := hmoment.mul_left
    ((N : ℝ) / (N : ℝ) ^ r)
  have htailBase := momentTail_summable_of_moment
    rho r ((R : ℝ) * (N : ℝ)) hrho hmoment
  have htail : Summable tailTerm := htailBase.mul_left
    ((N : ℝ) / (N : ℝ) ^ r)
  have hsoftNonneg : ∀ j : ℕ, 0 ≤ softTerm j := by
    intro j
    exact mul_nonneg
      (mul_nonneg hNR.le (hrho j))
      (positiveMomentCutoff_nonneg r R _)
  have hfullNonneg : ∀ j : ℕ, 0 ≤ fullTerm j := by
    intro j
    exact mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (hrho j))
  have hsoftLe : ∀ j : ℕ, softTerm j ≤ fullTerm j := by
    intro j
    have hx : 0 ≤ (j : ℝ) / (N : ℝ) :=
      div_nonneg (Nat.cast_nonneg j) hNR.le
    have hcut := positiveMomentCutoff_le_power_of_nonneg r R hx
    dsimp only [softTerm, fullTerm]
    calc
      (N : ℝ) * rho j *
          positiveMomentCutoff r R ((j : ℝ) / (N : ℝ)) ≤
        (N : ℝ) * rho j * ((j : ℝ) / (N : ℝ)) ^ r :=
          mul_le_mul_of_nonneg_left hcut
            (mul_nonneg hNR.le (hrho j))
      _ = ((N : ℝ) / (N : ℝ) ^ r) *
          ((j : ℝ) ^ r * rho j) := by
        field_simp
        ring
  have hsoft : Summable softTerm :=
    hfull.of_nonneg_of_le hsoftNonneg hsoftLe
  have hfullLe : ∀ j : ℕ, fullTerm j ≤ softTerm j + tailTerm j := by
    intro j
    by_cases hj : (j : ℝ) ≤ (R : ℝ) * (N : ℝ)
    · have hxR : (j : ℝ) / (N : ℝ) ≤ (R : ℝ) := by
        rw [div_le_iff₀ hNR]
        exact hj
      have hcut := positiveMomentCutoff_eq_power r R
        ⟨div_nonneg (Nat.cast_nonneg j) hNR.le, hxR⟩
      have htailZero : strictTailIndicator
          ((R : ℝ) * (N : ℝ)) (j : ℝ) = 0 := by
        simp [strictTailIndicator, not_lt_of_ge hj]
      dsimp only [fullTerm, softTerm, tailTerm]
      rw [hcut, htailZero]
      apply le_of_eq
      field_simp
      ring
    · have hj' : (R : ℝ) * (N : ℝ) < (j : ℝ) := lt_of_not_ge hj
      have htailOne : strictTailIndicator
          ((R : ℝ) * (N : ℝ)) (j : ℝ) = 1 := by
        simp [strictTailIndicator, hj']
      dsimp only [fullTerm, tailTerm]
      rw [htailOne, mul_one]
      exact le_add_of_nonneg_left (hsoftNonneg j)
  have hsoftTsumLe := hsoft.tsum_le_tsum hsoftLe hfull
  have hrightSummable := hsoft.add htail
  have hfullTsumLe := hfull.tsum_le_tsum hfullLe hrightSummable
  have hfullTsumLe' : (∑' j, fullTerm j) ≤
      (∑' j, softTerm j) + ∑' j, tailTerm j := by
    rw [← hsoft.tsum_add htail]
    exact hfullTsumLe
  simpa only [softScaledDiscreteMoment, scaledDiscreteMoment,
    scaledDiscreteMomentTail, fullTerm, softTerm, tailTerm,
    hmoment.tsum_mul_left, htailBase.tsum_mul_left] using
      And.intro hsoftTsumLe hfullTsumLe'

/-- Compact cutoffs converge to the full continuum moment. -/
theorem integral_positiveMomentCutoff_tendsto_continuumMoment
    (u : ℝ → ℝ) (r : ℕ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (hint : IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ))) :
    Tendsto
      (fun R : ℕ ↦ ∫ x in Ici (0 : ℝ),
        u x * positiveMomentCutoff r R x)
      atTop (nhds (continuumMoment u r)) := by
  have hconv := tendsto_integral_of_dominated_convergence
    (fun x : ℝ ↦ x ^ r * u x)
    (fun R ↦ (hucont.mul
      (continuous_positiveMomentCutoff r R).continuousOn).aestronglyMeasurable
        measurableSet_Ici)
    hint
    (fun R ↦ by
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
      have hx0 : 0 ≤ x := hx
      have hu0 := hunonneg x hx0
      have hcut0 := positiveMomentCutoff_nonneg r R x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu0 hcut0)]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (positiveMomentCutoff_le_power_of_nonneg r R hx0) hu0)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
      have hx0 : 0 ≤ x := hx
      obtain ⟨R₀, hR₀⟩ := exists_nat_ge x
      apply tendsto_atTop_of_eventually_const (i₀ := R₀)
      intro R hR
      have hxR : x ≤ (R : ℝ) := hR₀.trans (by exact_mod_cast hR)
      rw [positiveMomentCutoff_eq_power r R ⟨hx0, hxR⟩]
      )
  simpa only [continuumMoment, mul_comm] using hconv

end

end DerridaRetaux
