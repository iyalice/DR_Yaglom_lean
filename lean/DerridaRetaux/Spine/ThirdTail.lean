import DerridaRetaux.Prelim.CoarseMomentBounds
import DerridaRetaux.Spine.PathTail
import DerridaRetaux.Spine.SizeBiased
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators
open Filter Topology

namespace DerridaRetaux

noncomputable section

/-!
# From the cubic spine tail to the ordinary third-moment tail

This file isolates the deterministic transfer in `cor:thirdtail`.  The only
non-algebraic inputs of the orbit-level theorem are the earlier H1b product
estimate and the earlier spine-tail estimate; neither is hidden as a conclusion
of the theorem being proved.
-/

/-- Strict tail of the normalized tilted third moment. -/
def normalizedTiltThirdTail
    (m : ℕ) (p : ProbabilityMass) (R : ℝ) : ℝ :=
  ∑' k : ℕ,
    (k : ℝ) ^ 3 * normalizedTilt m p k * strictTailIndicator R (k : ℝ)

/-- Strict tail of an arbitrary probability mass on `ℕ`. -/
def probabilityMassTail (p : ProbabilityMass) (R : ℝ) : ℝ :=
  ∑' k : ℕ, p k * strictTailIndicator R (k : ℝ)

/-- Cubic-carrier tail before normalization by `J`. -/
def normalizedCubicCarrierTail
    (m : ℕ) (p : ProbabilityMass) (R : ℝ) : ℝ :=
  ∑' k : ℕ,
    cubicCarrier m k * normalizedTilt m p k * strictTailIndicator R (k : ℝ)

theorem probabilityMassTail_nonneg (p : ProbabilityMass) (R : ℝ) :
    0 ≤ probabilityMassTail p R := by
  apply tsum_nonneg
  intro k
  apply mul_nonneg (p.nonneg k)
  unfold strictTailIndicator
  split_ifs <;> norm_num

theorem probabilityMassTail_summable (p : ProbabilityMass) (R : ℝ) :
    Summable (fun k : ℕ ↦ p k * strictTailIndicator R (k : ℝ)) := by
  apply p.summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (p.nonneg k) (by
      unfold strictTailIndicator
      split_ifs <;> norm_num)
  · intro k
    have hindicator : strictTailIndicator R (k : ℝ) ≤ 1 := by
      unfold strictTailIndicator
      split_ifs <;> norm_num
    simpa using mul_le_mul_of_nonneg_left hindicator (p.nonneg k)

/-- The strict tail of a single fixed probability mass vanishes as the real
cutoff tends to infinity.  No first moment is needed. -/
theorem probabilityMassTail_tendsto_zero (p : ProbabilityMass) :
    Tendsto (probabilityMassTail p) atTop (nhds 0) := by
  have hpoint (k : ℕ) :
      Tendsto (fun R : ℝ ↦ p k * strictTailIndicator R (k : ℝ))
        atTop (nhds 0) := by
    apply tendsto_atTop_of_eventually_const (i₀ := (k : ℝ))
    intro R hR
    simp [strictTailIndicator, not_lt_of_ge hR]
  have hbound : ∀ᶠ R : ℝ in atTop,
      ∀ k : ℕ, ‖p k * strictTailIndicator R (k : ℝ)‖ ≤ p k := by
    filter_upwards [] with R
    intro k
    have hindicatorNonneg : 0 ≤ strictTailIndicator R (k : ℝ) := by
      unfold strictTailIndicator
      split_ifs <;> norm_num
    have hindicatorLe : strictTailIndicator R (k : ℝ) ≤ 1 := by
      unfold strictTailIndicator
      split_ifs <;> norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (p.nonneg k) hindicatorNonneg)]
    simpa using mul_le_mul_of_nonneg_left hindicatorLe (p.nonneg k)
  simpa [probabilityMassTail] using
    (tendsto_tsum_of_dominated_convergence
      (f := fun R : ℝ ↦ fun k : ℕ ↦
        p k * strictTailIndicator R (k : ℝ))
      (g := fun _ : ℕ ↦ (0 : ℝ)) (bound := fun k : ℕ ↦ p k)
      p.summable hpoint hbound)

/-- The arity-uniform comparison used beyond a cutoff at least two. -/
theorem cube_le_four_thirds_mul_cubicCarrier
    (m k : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ k) :
    (k : ℝ) ^ 3 ≤ (4 / 3 : ℝ) * cubicCarrier m k := by
  by_cases hmTwo : m = 2
  · subst m
    exact cube_le_four_thirds_mul_cubicCarrier_two k hk
  · have hmThree : 3 ≤ m := by omega
    have hbase := cube_le_cubicCarrier m k hmThree
    have hcarrier := cubicCarrier_nonneg m k hm
    nlinarith

/-- Multiplying a cubic size-biased tail by its normalizer exactly recovers the
unnormalized carrier tail, including every zero-carrier row. -/
theorem normalizedCubicCarrierTail_eq_mul_probabilityMassTail_cubicSizeBiased
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (R : ℝ) :
    normalizedCubicCarrierTail m p R =
      normalizedCubicMoment m p *
        probabilityMassTail (cubicSizeBiasedLaw m p hm hcrit hthird hJ) R := by
  have htail := probabilityMassTail_summable
    (cubicSizeBiasedLaw m p hm hcrit hthird hJ) R
  rw [normalizedCubicCarrierTail, probabilityMassTail,
    ← htail.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [cubicSizeBiasedLaw_apply]
  unfold strictTailIndicator
  split_ifs
  · simp only [mul_one]
    have hG : 0 < tiltedPartition m p :=
      tiltedPartition_pos_of_critical m p (by omega) hcrit
    field_simp [hJ.ne', hG.ne']; ring
  · simp

/-- On every strict tail above `R ≥ 2`, the ordinary third moment is at most
`4/3` times the unnormalized cubic-carrier tail. -/
theorem normalizedTiltThirdTail_le_four_thirds_mul_cubicCarrierTail
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (R : ℝ) (hR : 2 ≤ R) :
    normalizedTiltThirdTail m p R ≤
      (4 / 3 : ℝ) * normalizedCubicCarrierTail m p R := by
  have hleft : Summable (fun k : ℕ ↦
      (k : ℝ) ^ 3 * normalizedTilt m p k * strictTailIndicator R (k : ℝ)) := by
    apply (normalizedTilt_cube_summable m p hthird).of_nonneg_of_le
    · intro k
      exact mul_nonneg
        (mul_nonneg (by positivity) (normalizedTilt_nonneg m p (by omega) hcrit k))
        (by unfold strictTailIndicator; split_ifs <;> norm_num)
    · intro k
      have hindicator : strictTailIndicator R (k : ℝ) ≤ 1 := by
        unfold strictTailIndicator
        split_ifs <;> norm_num
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hindicator
        (mul_nonneg (by positivity) (normalizedTilt_nonneg m p (by omega) hcrit k))
  have hcarrierBase := normalizedCubicMoment_summable m p hm hcrit hthird
  have hcarrierTail : Summable (fun k : ℕ ↦
      cubicCarrier m k * normalizedTilt m p k * strictTailIndicator R (k : ℝ)) := by
    apply hcarrierBase.of_nonneg_of_le
    · intro k
      exact mul_nonneg
        (mul_nonneg (cubicCarrier_nonneg m k hm)
          (normalizedTilt_nonneg m p (by omega) hcrit k))
        (by unfold strictTailIndicator; split_ifs <;> norm_num)
    · intro k
      have hindicator : strictTailIndicator R (k : ℝ) ≤ 1 := by
        unfold strictTailIndicator
        split_ifs <;> norm_num
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hindicator
        (mul_nonneg (cubicCarrier_nonneg m k hm)
          (normalizedTilt_nonneg m p (by omega) hcrit k))
  rw [normalizedTiltThirdTail, normalizedCubicCarrierTail,
    ← hcarrierTail.tsum_mul_left]
  apply hleft.tsum_le_tsum
  · intro k
    unfold strictTailIndicator
    by_cases hkTail : R < (k : ℝ)
    · rw [if_pos hkTail]
      have hkTwo : 2 ≤ k := by
        have hkReal : (2 : ℝ) < (k : ℝ) := lt_of_le_of_lt hR hkTail
        have hkStrict : 2 < k := by exact_mod_cast hkReal
        exact hkStrict.le
      have hq := normalizedTilt_nonneg m p (by omega) hcrit k
      simp only [mul_one]
      calc
        (k : ℝ) ^ 3 * normalizedTilt m p k ≤
            ((4 / 3 : ℝ) * cubicCarrier m k) * normalizedTilt m p k :=
          mul_le_mul_of_nonneg_right
            (cube_le_four_thirds_mul_cubicCarrier m k hm hkTwo) hq
        _ = (4 / 3 : ℝ) *
              (cubicCarrier m k * normalizedTilt m p k) := by ring
    · rw [if_neg hkTail]
      norm_num
  · exact hcarrierTail.mul_left (4 / 3 : ℝ)

/-- The exact normalized transfer: third-moment tail is controlled by `J` times
the cubic size-biased probability tail. -/
theorem normalizedTiltThirdTail_le_cubicSizeBiasedTail
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (hJ : 0 < normalizedCubicMoment m p) (R : ℝ) (hR : 2 ≤ R) :
    normalizedTiltThirdTail m p R ≤
      (4 / 3 : ℝ) * normalizedCubicMoment m p *
        probabilityMassTail (cubicSizeBiasedLaw m p hm hcrit hthird hJ) R := by
  calc
    normalizedTiltThirdTail m p R ≤
        (4 / 3 : ℝ) * normalizedCubicCarrierTail m p R :=
      normalizedTiltThirdTail_le_four_thirds_mul_cubicCarrierTail
        m p hm hcrit hthird R hR
    _ = (4 / 3 : ℝ) * normalizedCubicMoment m p *
          probabilityMassTail (cubicSizeBiasedLaw m p hm hcrit hthird hJ) R := by
      rw [normalizedCubicCarrierTail_eq_mul_probabilityMassTail_cubicSizeBiased
        m p hm hcrit hthird hJ R]
      ring

/-- Tail of the concrete orbit spine marginal. -/
def spineMarginalTail
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) (R : ℝ) : ℝ :=
  probabilityMassTail (spineMarginal m data n) R

/-- Concrete orbit form of the exact normalized transfer. -/
theorem profileThirdTail_le_spineMarginalTail
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ)
    (R : ℝ) (hR : 2 ≤ R) :
    normalizedTiltThirdTail m (orbit m data.law n) R ≤
      (4 / 3 : ℝ) * normalizedCubicMoment m (orbit m data.law n) *
        spineMarginalTail m data n R := by
  simpa [spineMarginalTail, spineMarginal] using
    normalizedTiltThirdTail_le_cubicSizeBiasedTail
      m (orbit m data.law n) data.arity
      (orbit_critical m data.law (le_trans (by norm_num) data.arity) data.critical n)
      (orbit_tiltSummable_three m data.law (le_trans (by norm_num) data.arity)
        data.critical data.third n)
      (normalizedCubicMoment_profile_orbit_pos m data n) R hR

/-- Source-shaped `eq:thirdtail`, conditional on exactly the two prior inputs:
the published H1b product estimate and the spine tail inequality. -/
theorem profileThirdTail_quadratic_of_spineTail
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant)
    (hsharp : ∀ (n : ℕ) (R : ℝ), 0 < R →
      spineMarginalTail m data n R ≤
        spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (R : ℝ), 2 ≤ R →
      normalizedTiltThirdTail m (orbit m data.law n) R ≤
        C * ((n + 1 : ℕ) : ℝ) ^ 2 *
          (spineMarginalTail m data 0 (R / 2) + (n : ℝ) / R) := by
  rcases normalizedCubicMoment_orbit_bound
      m data.law data.arity data.critical data.third hnonconstant hProduct with
    ⟨B, hB, hJ⟩
  refine ⟨(32 / 3 : ℝ) * B, by positivity, ?_⟩
  intro n R hR
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have htail0 : 0 ≤ spineMarginalTail m data 0 (R / 2) :=
    probabilityMassTail_nonneg _ _
  have hnR : 0 ≤ (n : ℝ) / R := by positivity
  have hJnNonneg : 0 ≤ normalizedCubicMoment m (orbit m data.law n) :=
    (normalizedCubicMoment_profile_orbit_pos m data n).le
  have hsumNonneg :
      0 ≤ spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R := by
    positivity
  have htailInflate :
      spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R ≤
        8 * (spineMarginalTail m data 0 (R / 2) + (n : ℝ) / R) := by
    have hx : spineMarginalTail m data 0 (R / 2) ≤
        8 * spineMarginalTail m data 0 (R / 2) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 8 by norm_num) htail0
    calc
      spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R ≤
          8 * spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R :=
        add_le_add_right hx _
      _ = 8 * (spineMarginalTail m data 0 (R / 2) + (n : ℝ) / R) := by
        ring
  calc
    normalizedTiltThirdTail m (orbit m data.law n) R ≤
        (4 / 3 : ℝ) * normalizedCubicMoment m (orbit m data.law n) *
          spineMarginalTail m data n R :=
      profileThirdTail_le_spineMarginalTail m data n R hR
    _ ≤ (4 / 3 : ℝ) * normalizedCubicMoment m (orbit m data.law n) *
          (spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R) := by
      exact mul_le_mul_of_nonneg_left (hsharp n R hRpos)
        (mul_nonneg (by norm_num) hJnNonneg)
    _ ≤ (4 / 3 : ℝ) * (B * ((n + 1 : ℕ) : ℝ) ^ 2) *
          (spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hJ n) (by norm_num)) hsumNonneg
    _ ≤ (4 / 3 : ℝ) * (B * ((n + 1 : ℕ) : ℝ) ^ 2) *
          (8 * (spineMarginalTail m data 0 (R / 2) + (n : ℝ) / R)) := by
      exact mul_le_mul_of_nonneg_left htailInflate
        (mul_nonneg (by norm_num) (mul_nonneg hB.le (sq_nonneg _)))
    _ = (32 / 3 : ℝ) * B * ((n + 1 : ℕ) : ℝ) ^ 2 *
          (spineMarginalTail m data 0 (R / 2) + (n : ℝ) / R) := by
      ring

/-- The rescaled finite-window estimate underlying `eq:UI`.  The lower window
cutoff `eta N` is irrelevant for this upper bound; only `n ≤ T N` is used. -/
theorem profileThirdTail_rescaled_window_of_spineTail
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant)
    (hsharp : ∀ (n : ℕ) (R : ℝ), 0 < R →
      spineMarginalTail m data n R ≤
        spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T A : ℝ) (N n : ℕ),
      0 < T → 0 < A → 1 ≤ N → 2 ≤ A * (N : ℝ) →
      (n : ℝ) ≤ T * (N : ℝ) →
      normalizedTiltThirdTail m (orbit m data.law n) (A * (N : ℝ)) /
          (N : ℝ) ^ 2 ≤
        C * (T + 1) ^ 2 *
          (spineMarginalTail m data 0 (A * (N : ℝ) / 2) + T / A) := by
  rcases profileThirdTail_quadratic_of_spineTail
      m data hnonconstant hProduct hsharp with ⟨C, hC, htail⟩
  refine ⟨C, hC, ?_⟩
  intro T A N n hT hA hN hcutoff hnT
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hANpos : 0 < A * (N : ℝ) := mul_pos hA hNpos
  have hnNonneg : 0 ≤ (n : ℝ) := by positivity
  have htail0 : 0 ≤ spineMarginalTail m data 0 (A * (N : ℝ) / 2) :=
    probabilityMassTail_nonneg _ _
  have hnRatioNonneg : 0 ≤ (n : ℝ) / (A * (N : ℝ)) := by positivity
  have hTRatioNonneg : 0 ≤ T / A := by positivity
  have hnRatio : (n : ℝ) / (A * (N : ℝ)) ≤ T / A := by
    apply (div_le_div_iff₀ hANpos hA).2
    have hmul := mul_le_mul_of_nonneg_left hnT hA.le
    nlinarith
  have hstepRatio : ((n + 1 : ℕ) : ℝ) / (N : ℝ) ≤ T + 1 := by
    apply (div_le_iff₀ hNpos).2
    have hOneN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast
    nlinarith
  have hstepRatioNonneg :
      0 ≤ ((n + 1 : ℕ) : ℝ) / (N : ℝ) := by positivity
  have hTOneNonneg : 0 ≤ T + 1 := by linarith
  have hstepSquare :
      (((n + 1 : ℕ) : ℝ) / (N : ℝ)) ^ 2 ≤ (T + 1) ^ 2 := by
    exact pow_le_pow_left₀ hstepRatioNonneg hstepRatio 2
  have hinner :
      spineMarginalTail m data 0 (A * (N : ℝ) / 2) +
          (n : ℝ) / (A * (N : ℝ)) ≤
        spineMarginalTail m data 0 (A * (N : ℝ) / 2) + T / A :=
    add_le_add_left hnRatio _
  have hinnerNonneg :
      0 ≤ spineMarginalTail m data 0 (A * (N : ℝ) / 2) +
        (n : ℝ) / (A * (N : ℝ)) := add_nonneg htail0 hnRatioNonneg
  have htargetInnerNonneg :
      0 ≤ spineMarginalTail m data 0 (A * (N : ℝ) / 2) + T / A :=
    add_nonneg htail0 hTRatioNonneg
  have hscale (X : ℝ) :
      (C * ((n + 1 : ℕ) : ℝ) ^ 2 * X) / (N : ℝ) ^ 2 =
        C * (((n + 1 : ℕ) : ℝ) / (N : ℝ)) ^ 2 * X := by
    field_simp [hNpos.ne']
  calc
    normalizedTiltThirdTail m (orbit m data.law n) (A * (N : ℝ)) /
          (N : ℝ) ^ 2 ≤
        (C * ((n + 1 : ℕ) : ℝ) ^ 2 *
          (spineMarginalTail m data 0 (A * (N : ℝ) / 2) +
            (n : ℝ) / (A * (N : ℝ)))) / (N : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (htail n (A * (N : ℝ)) hcutoff) (sq_nonneg _)
    _ = C * (((n + 1 : ℕ) : ℝ) / (N : ℝ)) ^ 2 *
          (spineMarginalTail m data 0 (A * (N : ℝ) / 2) +
            (n : ℝ) / (A * (N : ℝ))) := by
      exact hscale _
    _ ≤ C * (T + 1) ^ 2 *
          (spineMarginalTail m data 0 (A * (N : ℝ) / 2) +
            (n : ℝ) / (A * (N : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstepSquare hC.le) hinnerNonneg
    _ ≤ C * (T + 1) ^ 2 *
          (spineMarginalTail m data 0 (A * (N : ℝ) / 2) + T / A) := by
      exact mul_le_mul_of_nonneg_left hinner
        (mul_nonneg hC.le (sq_nonneg _))

/-- Along every positive linear cutoff, the tail of the fixed initial spine
marginal vanishes. -/
theorem spineMarginalTail_initial_linear_tendsto_zero
    (m : ℕ) (data : ProfileInitialData m) (A : ℝ) (hA : 0 < A) :
    Tendsto
      (fun N : ℕ ↦ spineMarginalTail m data 0 (A * (N : ℝ) / 2))
      atTop (nhds 0) := by
  have hcoefficient : 0 < A / 2 := by positivity
  have hcutoff :
      Tendsto (fun N : ℕ ↦ A * (N : ℝ) / 2) atTop atTop := by
    convert
      (tendsto_natCast_atTop_atTop.const_mul_atTop hcoefficient :
        Tendsto (fun N : ℕ ↦ (A / 2) * (N : ℝ)) atTop atTop) using 1
    funext N
    ring
  simpa [spineMarginalTail] using
    (probabilityMassTail_tendsto_zero (spineMarginal m data 0)).comp hcutoff

/-- Filter form of the nested uniform-integrability conclusion.  It is stronger
than the manuscript window because it is uniform over all `0 ≤ n ≤ T N`; hence
any additional lower cutoff `eta N ≤ n` may be imposed for free. -/
theorem profileThirdTail_uniform_integrability_of_spineTail
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant)
    (hsharp : ∀ (n : ℕ) (R : ℝ), 0 < R →
      spineMarginalTail m data n R ≤
        spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R) :
    ∀ (T : ℝ), 0 < T → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * (N : ℝ) →
        normalizedTiltThirdTail m (orbit m data.law n) (A * (N : ℝ)) /
            (N : ℝ) ^ 2 ≤ ε := by
  rcases profileThirdTail_rescaled_window_of_spineTail
      m data hnonconstant hProduct hsharp with ⟨C, hC, hwindow⟩
  intro T hT ε hε
  let M : ℝ := C * (T + 1) ^ 2
  have hM : 0 < M := by
    dsimp [M]
    positivity
  let δ : ℝ := ε / (4 * M)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hMδ : M * δ = ε / 4 := by
    dsimp [δ]
    field_simp [hM.ne']
    ring
  have hTdiv : Tendsto (fun A : ℝ ↦ T / A) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have houterTend :
      Tendsto (fun A : ℝ ↦ M * (δ + T / A)) atTop (nhds (ε / 4)) := by
    simpa only [add_zero, hMδ] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℝ ↦ δ) atTop (nhds δ)).add hTdiv).const_mul M
  have houterSmall : ∀ᶠ A : ℝ in atTop, M * (δ + T / A) < ε :=
    (tendsto_order.1 houterTend).2 ε (by linarith)
  filter_upwards [eventually_gt_atTop (0 : ℝ), houterSmall] with A hA hASmall
  have hcutoffTend :
      Tendsto (fun N : ℕ ↦ A * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hA
  have htailSmall : ∀ᶠ N : ℕ in atTop,
      spineMarginalTail m data 0 (A * (N : ℝ) / 2) < δ :=
    (tendsto_order.1
      (spineMarginalTail_initial_linear_tendsto_zero m data A hA)).2 δ hδ
  filter_upwards [eventually_ge_atTop (1 : ℕ),
      hcutoffTend.eventually (eventually_ge_atTop (2 : ℝ)), htailSmall] with
      N hN hcutoff htail
  intro n hnT
  have hbound := hwindow T A N n hT hA hN hcutoff hnT
  change normalizedTiltThirdTail m (orbit m data.law n) (A * (N : ℝ)) /
      (N : ℝ) ^ 2 ≤
        M * (spineMarginalTail m data 0 (A * (N : ℝ) / 2) + T / A) at hbound
  have hstrict :
      M * (spineMarginalTail m data 0 (A * (N : ℝ) / 2) + T / A) <
        M * (δ + T / A) := by
    exact mul_lt_mul_of_pos_left (add_lt_add_right htail _) hM
  exact (hbound.trans_lt (hstrict.trans hASmall)).le

end

end DerridaRetaux
