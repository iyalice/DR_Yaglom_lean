import DerridaRetaux.Spine.ThirdTail
import DerridaRetaux.Prelim.WeightedMass
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Passage of lattice moments to a continuum limit

The lemmas here isolate the uniform-integrability argument used after the
cubic spine bound.  They do not assume convergence of a full moment: only
compactly truncated convergence and the explicit cubic tail estimate enter.
-/

/-- The source normalization `N^(1-r) sum j^r rho(j)` written without integer
exponents. -/
def scaledDiscreteMoment (rho : Seq) (r N : ℕ) : ℝ :=
  ((N : ℝ) / (N : ℝ) ^ r) * ∑' j : ℕ, (j : ℝ) ^ r * rho j

/-- Strict spatial tail of the scaled lattice moment beyond `A*N`. -/
def scaledDiscreteMomentTail (rho : Seq) (r N : ℕ) (A : ℝ) : ℝ :=
  ((N : ℝ) / (N : ℝ) ^ r) *
    ∑' j : ℕ, (j : ℝ) ^ r * rho j *
      strictTailIndicator (A * (N : ℝ)) (j : ℝ)

/-- Above the scale `A*N`, every normalized moment of order at most three is
dominated by the normalized third moment, with the expected power of `A`. -/
theorem scaledPower_le_scaledCube
    (r N j : ℕ) (A : ℝ) (hr : r ≤ 3) (hN : 1 ≤ N)
    (hA : 1 ≤ A) (hj : A * (N : ℝ) < (j : ℝ)) :
    ((N : ℝ) / (N : ℝ) ^ r) * (j : ℝ) ^ r ≤
      (((N : ℝ) / (N : ℝ) ^ 3) * (j : ℝ) ^ 3) /
        A ^ (3 - r) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hAR : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hjR : 0 < (j : ℝ) := lt_of_lt_of_le (mul_pos hAR hNR) hj.le
  interval_cases r
  · norm_num
    have hcubed : (A * (N : ℝ)) ^ 3 < (j : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hj (mul_nonneg hAR.le hNR.le) (by norm_num)
    have hform :
        ((N : ℝ) / (N : ℝ) ^ 3 * (j : ℝ) ^ 3) / A ^ 3 =
          (j : ℝ) ^ 3 / ((N : ℝ) ^ 2 * A ^ 3) := by
      field_simp
      ring
    rw [hform]
    apply (le_div_iff₀ (mul_pos (pow_pos hNR 2) (pow_pos hAR 3))).2
    rw [mul_pow] at hcubed
    nlinarith
  · norm_num
    have hsquared : (A * (N : ℝ)) ^ 2 < (j : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hj (mul_nonneg hAR.le hNR.le) (by norm_num)
    have hform :
        ((N : ℝ) / (N : ℝ) ^ 3 * (j : ℝ) ^ 3) / A ^ 2 =
          (j : ℝ) ^ 3 / ((N : ℝ) ^ 2 * A ^ 2) := by
      field_simp
      ring
    have hleft :
        ((N : ℝ) / (N : ℝ)) * (j : ℝ) = (j : ℝ) := by
      field_simp
    rw [hleft, hform]
    apply (le_div_iff₀ (mul_pos (pow_pos hNR 2) (pow_pos hAR 2))).2
    rw [mul_pow] at hsquared
    have hmul := mul_lt_mul_of_pos_left hsquared hjR
    ring_nf at hmul ⊢
    exact hmul.le
  · norm_num
    have hleft :
        ((N : ℝ) / (N : ℝ) ^ 2) * (j : ℝ) ^ 2 =
          (j : ℝ) ^ 2 / (N : ℝ) := by
      field_simp
      ring
    have hright :
        ((N : ℝ) / (N : ℝ) ^ 3 * (j : ℝ) ^ 3) / A =
          (j : ℝ) ^ 3 / ((N : ℝ) ^ 2 * A) := by
      field_simp
      ring
    rw [hleft, hright]
    apply (div_le_div_iff₀ hNR (mul_pos (pow_pos hNR 2) hAR)).2
    have hmul := mul_lt_mul_of_pos_left hj (sq_pos_of_pos hjR)
    have hmulN := mul_le_mul_of_nonneg_right hmul.le hNR.le
    ring_nf at hmulN ⊢
    exact hmulN
  · norm_num

/-- The pointwise comparison sums without losing its normalization.  This is
the concrete analytic step that reduces all strict tails of order at most three
to the cubic strict tail. -/
theorem scaledDiscreteMomentTail_le_third
    (rho : Seq) (r N : ℕ) (A : ℝ) (hr : r ≤ 3) (hN : 1 ≤ N)
    (hA : 1 ≤ A) (hrho : ∀ j : ℕ, 0 ≤ rho j)
    (hrSummable : Summable (fun j : ℕ ↦
      (j : ℝ) ^ r * rho j * strictTailIndicator (A * (N : ℝ)) (j : ℝ)))
    (hthreeSummable : Summable (fun j : ℕ ↦
      (j : ℝ) ^ 3 * rho j * strictTailIndicator (A * (N : ℝ)) (j : ℝ))) :
    scaledDiscreteMomentTail rho r N A ≤
      scaledDiscreteMomentTail rho 3 N A / A ^ (3 - r) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hAR : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hscaleR : 0 ≤ (N : ℝ) / (N : ℝ) ^ r := by positivity
  have hscaleThree : 0 ≤ (N : ℝ) / (N : ℝ) ^ 3 := by positivity
  have hleftSummable : Summable (fun j : ℕ ↦
      (((N : ℝ) / (N : ℝ) ^ r) * (j : ℝ) ^ r) *
        (rho j * strictTailIndicator (A * (N : ℝ)) (j : ℝ))) := by
    convert hrSummable.mul_left ((N : ℝ) / (N : ℝ) ^ r) using 1
    funext j
    ring
  have hrightSummable : Summable (fun j : ℕ ↦
      ((((N : ℝ) / (N : ℝ) ^ 3) * (j : ℝ) ^ 3) /
          A ^ (3 - r)) *
        (rho j * strictTailIndicator (A * (N : ℝ)) (j : ℝ))) := by
    convert (hthreeSummable.mul_left
      (((N : ℝ) / (N : ℝ) ^ 3) / A ^ (3 - r))) using 1
    funext j
    ring
  have hsum :
      (∑' j : ℕ,
        (((N : ℝ) / (N : ℝ) ^ r) * (j : ℝ) ^ r) *
          (rho j * strictTailIndicator (A * (N : ℝ)) (j : ℝ))) ≤
      ∑' j : ℕ,
        ((((N : ℝ) / (N : ℝ) ^ 3) * (j : ℝ) ^ 3) /
            A ^ (3 - r)) *
          (rho j * strictTailIndicator (A * (N : ℝ)) (j : ℝ)) := by
    apply hleftSummable.tsum_le_tsum
    · intro j
      unfold strictTailIndicator
      by_cases hj : A * (N : ℝ) < (j : ℝ)
      · rw [if_pos hj]
        simp only [mul_one]
        exact mul_le_mul_of_nonneg_right
          (scaledPower_le_scaledCube r N j A hr hN hA hj) (hrho j)
      · rw [if_neg hj]
        simp
    · exact hrightSummable
  have hleftEq :
      scaledDiscreteMomentTail rho r N A =
        ∑' j : ℕ,
          (((N : ℝ) / (N : ℝ) ^ r) * (j : ℝ) ^ r) *
            (rho j * strictTailIndicator (A * (N : ℝ)) (j : ℝ)) := by
    rw [scaledDiscreteMomentTail, ← hrSummable.tsum_mul_left]
    apply tsum_congr
    intro j
    ring
  have hrightEq :
      scaledDiscreteMomentTail rho 3 N A / A ^ (3 - r) =
        ∑' j : ℕ,
          ((((N : ℝ) / (N : ℝ) ^ 3) * (j : ℝ) ^ 3) /
              A ^ (3 - r)) *
            (rho j * strictTailIndicator (A * (N : ℝ)) (j : ℝ)) := by
    rw [scaledDiscreteMomentTail, ← hthreeSummable.tsum_mul_left,
      ← tsum_div_const]
    apply tsum_congr
    intro j
    ring
  rw [hleftEq, hrightEq]
  exact hsum

/-- Reindexing `rho(j) = (m-1) q(j+1)` transfers a strict cubic tail to
the normalized tilted law, with only the literal factor `m-1`. -/
theorem positiveTiltedDensityThirdTail_le_normalizedTiltThirdTail
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hthird : TiltSummable m 3 p) (R : ℝ) :
    (∑' j : ℕ, (j : ℝ) ^ 3 * positiveTiltedDensity m p j *
        strictTailIndicator R (j : ℝ)) ≤
      ((m : ℝ) - 1) * normalizedTiltThirdTail m p R := by
  have hfactor : 0 ≤ (m : ℝ) - 1 :=
    (critical_tiltFactor_pos m p hm hcrit).le
  have hleftBase :=
    positiveTiltedDensity_third_summable m p hm hcrit hthird
  have hleft : Summable (fun j : ℕ ↦
      (j : ℝ) ^ 3 * positiveTiltedDensity m p j *
        strictTailIndicator R (j : ℝ)) := by
    apply hleftBase.of_nonneg_of_le
    · intro j
      exact mul_nonneg
        (mul_nonneg (by positivity)
          (positiveTiltedDensity_nonneg m p hm hcrit j))
        (by unfold strictTailIndicator; split_ifs <;> norm_num)
    · intro j
      have hindicator : strictTailIndicator R (j : ℝ) ≤ 1 := by
        unfold strictTailIndicator
        split_ifs <;> norm_num
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hindicator
        (mul_nonneg (by positivity)
          (positiveTiltedDensity_nonneg m p hm hcrit j))
  have hcube := normalizedTilt_cube_summable m p hthird
  have hfull : Summable (fun k : ℕ ↦
      (k : ℝ) ^ 3 * normalizedTilt m p k *
        strictTailIndicator R (k : ℝ)) := by
    apply hcube.of_nonneg_of_le
    · intro k
      exact mul_nonneg
        (mul_nonneg (by positivity) (normalizedTilt_nonneg m p hm hcrit k))
        (by unfold strictTailIndicator; split_ifs <;> norm_num)
    · intro k
      have hindicator : strictTailIndicator R (k : ℝ) ≤ 1 := by
        unfold strictTailIndicator
        split_ifs <;> norm_num
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hindicator
        (mul_nonneg (by positivity) (normalizedTilt_nonneg m p hm hcrit k))
  have hshift : Summable (fun j : ℕ ↦
      ((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1) *
        strictTailIndicator R ((j + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).2 hfull
  have hright : Summable (fun j : ℕ ↦
      ((m : ℝ) - 1) *
        (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1) *
          strictTailIndicator R ((j + 1 : ℕ) : ℝ))) :=
    hshift.mul_left ((m : ℝ) - 1)
  have hle :
      (∑' j : ℕ, (j : ℝ) ^ 3 * positiveTiltedDensity m p j *
          strictTailIndicator R (j : ℝ)) ≤
        ∑' j : ℕ, ((m : ℝ) - 1) *
          (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1) *
            strictTailIndicator R ((j + 1 : ℕ) : ℝ)) := by
    apply hleft.tsum_le_tsum
    · intro j
      have hq := normalizedTilt_nonneg m p hm hcrit (j + 1)
      unfold strictTailIndicator
      by_cases hj : R < (j : ℝ)
      · have hjsucc : R < ((j + 1 : ℕ) : ℝ) := by
          have hjlt : (j : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self j
          exact lt_trans hj hjlt
        rw [if_pos hj, if_pos hjsucc, positiveTiltedDensity_apply]
        simp only [mul_one]
        have hjpow : (j : ℝ) ^ 3 ≤ ((j + 1 : ℕ) : ℝ) ^ 3 := by
          gcongr
          exact_mod_cast (Nat.le_succ j)
        calc
          (j : ℝ) ^ 3 * (((m : ℝ) - 1) * normalizedTilt m p (j + 1)) =
              ((m : ℝ) - 1) * ((j : ℝ) ^ 3 * normalizedTilt m p (j + 1)) := by
                ring
          _ ≤ ((m : ℝ) - 1) *
              (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1)) := by
                gcongr
      · rw [if_neg hj]
        simp only [mul_zero]
        exact mul_nonneg hfactor
          (mul_nonneg (mul_nonneg (by positivity) hq)
            (by split_ifs <;> norm_num))
    · exact hright
  calc
    (∑' j : ℕ, (j : ℝ) ^ 3 * positiveTiltedDensity m p j *
        strictTailIndicator R (j : ℝ)) ≤
        ∑' j : ℕ, ((m : ℝ) - 1) *
          (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1) *
            strictTailIndicator R ((j + 1 : ℕ) : ℝ)) := hle
    _ = ((m : ℝ) - 1) *
        ∑' j : ℕ, (((j + 1 : ℕ) : ℝ) ^ 3 * normalizedTilt m p (j + 1) *
          strictTailIndicator R ((j + 1 : ℕ) : ℝ)) :=
      hshift.tsum_mul_left ((m : ℝ) - 1)
    _ = ((m : ℝ) - 1) * normalizedTiltThirdTail m p R := by
      rw [normalizedTiltThirdTail]
      congr 1
      rw [hfull.tsum_eq_zero_add]
      simp

/-- The preceding reindexing has exactly the source normalization after division
by `N^2`. -/
theorem scaledPositiveTiltedDensityThirdTail_le
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hthird : TiltSummable m 3 p) (N : ℕ) (A : ℝ) (hN : 1 ≤ N) :
    scaledDiscreteMomentTail (positiveTiltedDensity m p) 3 N A ≤
      ((m : ℝ) - 1) *
        (normalizedTiltThirdTail m p (A * (N : ℝ)) / (N : ℝ) ^ 2) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have htail := positiveTiltedDensityThirdTail_le_normalizedTiltThirdTail
    m p hm hcrit hthird (A * (N : ℝ))
  rw [scaledDiscreteMomentTail]
  calc
    ((N : ℝ) / (N : ℝ) ^ 3) *
        (∑' j : ℕ, (j : ℝ) ^ 3 * positiveTiltedDensity m p j *
          strictTailIndicator (A * (N : ℝ)) (j : ℝ)) ≤
      ((N : ℝ) / (N : ℝ) ^ 3) *
        (((m : ℝ) - 1) * normalizedTiltThirdTail m p (A * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = ((m : ℝ) - 1) *
        (normalizedTiltThirdTail m p (A * (N : ℝ)) / (N : ℝ) ^ 2) := by
      field_simp
      ring

/-- Orbit-level cubic uniform integrability for the shifted density.  Its only
non-algebraic premise is the concrete spine-tail inequality already isolated in
`ThirdTail`. -/
theorem profileDensityThirdTail_uniform_integrability_of_spineTail
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant)
    (hsharp : ∀ (n : ℕ) (R : ℝ), 0 < R →
      spineMarginalTail m data n R ≤
        spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R) :
    ∀ (T : ℝ), 0 < T → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * (N : ℝ) →
        scaledDiscreteMomentTail
          (positiveTiltedDensity m (orbit m data.law n)) 3 N A ≤ ε := by
  intro T hT ε hε
  have hfactor : 0 < (m : ℝ) - 1 :=
    critical_tiltFactor_pos m data.law
      (le_trans (by norm_num) data.arity) data.critical
  have heps : 0 < ε / ((m : ℝ) - 1) := div_pos hε hfactor
  have hq := profileThirdTail_uniform_integrability_of_spineTail
    m data hnonconstant hProduct hsharp T hT
      (ε / ((m : ℝ) - 1)) heps
  filter_upwards [hq] with A hqA
  filter_upwards [hqA, eventually_ge_atTop (1 : ℕ)] with N hqN hN
  intro n hn
  have horbitCrit := orbit_critical m data.law
    (le_trans (by norm_num) data.arity) data.critical n
  have horbitThird := orbit_tiltSummable_three m data.law
    (le_trans (by norm_num) data.arity)
    data.critical data.third n
  calc
    scaledDiscreteMomentTail
        (positiveTiltedDensity m (orbit m data.law n)) 3 N A ≤
      ((m : ℝ) - 1) *
        (normalizedTiltThirdTail m (orbit m data.law n)
          (A * (N : ℝ)) / (N : ℝ) ^ 2) :=
      scaledPositiveTiltedDensityThirdTail_le
        m (orbit m data.law n) (le_trans (by norm_num) data.arity)
          horbitCrit horbitThird N A hN
    _ ≤ ((m : ℝ) - 1) * (ε / ((m : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (hqN n hn) hfactor.le
    _ = ε := by field_simp

/-- On natural lattice points, every power through degree three is dominated by
`1+j^3`. -/
theorem natCast_pow_le_one_add_cube (r j : ℕ) (hr : r ≤ 3) :
    (j : ℝ) ^ r ≤ 1 + (j : ℝ) ^ 3 := by
  by_cases hj : j = 0
  · subst j
    interval_cases r <;> norm_num
  · have hjOne : 1 ≤ (j : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj)
    exact (pow_le_pow_right₀ hjOne hr).trans
      (le_add_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num))

/-- A nonnegative summable sequence with finite cubic moment has every moment
through order three. -/
theorem moment_summable_of_zero_and_third
    (rho : Seq) (r : ℕ) (hr : r ≤ 3) (hrho : ∀ j : ℕ, 0 ≤ rho j)
    (hzero : Summable rho)
    (hthree : Summable (fun j : ℕ ↦ (j : ℝ) ^ 3 * rho j)) :
    Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho j) := by
  have hdom : Summable (fun j : ℕ ↦ rho j + (j : ℝ) ^ 3 * rho j) :=
    hzero.add hthree
  apply Summable.of_nonneg_of_le (f := fun j : ℕ ↦
    rho j + (j : ℝ) ^ 3 * rho j)
  · intro j
    exact mul_nonneg (by positivity) (hrho j)
  · intro j
    have hp := natCast_pow_le_one_add_cube r j hr
    calc
      (j : ℝ) ^ r * rho j ≤ (1 + (j : ℝ) ^ 3) * rho j :=
        mul_le_mul_of_nonneg_right hp (hrho j)
      _ = rho j + (j : ℝ) ^ 3 * rho j := by ring
  · exact hdom

/-- Restricting a finite nonnegative moment to a strict tail preserves
summability. -/
theorem momentTail_summable_of_moment
    (rho : Seq) (r : ℕ) (R : ℝ) (hrho : ∀ j : ℕ, 0 ≤ rho j)
    (hmoment : Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho j)) :
    Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho j *
      strictTailIndicator R (j : ℝ)) := by
  apply hmoment.of_nonneg_of_le
  · intro j
    exact mul_nonneg (mul_nonneg (by positivity) (hrho j))
      (by unfold strictTailIndicator; split_ifs <;> norm_num)
  · intro j
    have hindicator : strictTailIndicator R (j : ℝ) ≤ 1 := by
      unfold strictTailIndicator
      split_ifs <;> norm_num
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hindicator
      (mul_nonneg (by positivity) (hrho j))

/-- The full source-connected uniform-integrability statement: on every upper
time window, all shifted-density moment tails of orders `0,1,2,3` vanish after
their source normalization. -/
theorem profileDensityMomentTail_uniform_integrability_of_spineTail
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant)
    (hsharp : ∀ (n : ℕ) (R : ℝ), 0 < R →
      spineMarginalTail m data n R ≤
        spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R)
    (r : ℕ) (hr : r ≤ 3) :
    ∀ (T : ℝ), 0 < T → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * (N : ℝ) →
        scaledDiscreteMomentTail
          (positiveTiltedDensity m (orbit m data.law n)) r N A ≤ ε := by
  intro T hT ε hε
  have hthreeUI := profileDensityThirdTail_uniform_integrability_of_spineTail
    m data hnonconstant hProduct hsharp T hT ε hε
  filter_upwards [hthreeUI, eventually_ge_atTop (1 : ℝ)] with A hAUI hA
  filter_upwards [hAUI, eventually_ge_atTop (1 : ℕ)] with N hNUI hN
  intro n hn
  let p := orbit m data.law n
  have hpCrit : Critical m p := orbit_critical m data.law
    (le_trans (by norm_num) data.arity) data.critical n
  have hpThird : TiltSummable m 3 p := orbit_tiltSummable_three m data.law
    (le_trans (by norm_num) data.arity) data.critical data.third n
  have hrho : ∀ j : ℕ, 0 ≤ positiveTiltedDensity m p j :=
    positiveTiltedDensity_nonneg m p
      (le_trans (by norm_num) data.arity) hpCrit
  have hzero : Summable (positiveTiltedDensity m p) :=
    (positiveTiltedDensity_hasSum m p
      (le_trans (by norm_num) data.arity) hpCrit).summable
  have hthree := positiveTiltedDensity_third_summable m p
    (le_trans (by norm_num) data.arity) hpCrit hpThird
  have hrMoment := moment_summable_of_zero_and_third
    (positiveTiltedDensity m p) r hr hrho hzero hthree
  have hrTail := momentTail_summable_of_moment
    (positiveTiltedDensity m p) r (A * (N : ℝ)) hrho hrMoment
  have hthreeTail := momentTail_summable_of_moment
    (positiveTiltedDensity m p) 3 (A * (N : ℝ)) hrho hthree
  have hcompare := scaledDiscreteMomentTail_le_third
    (positiveTiltedDensity m p) r N A hr hN hA hrho hrTail hthreeTail
  have hcubeNonneg :
      0 ≤ scaledDiscreteMomentTail (positiveTiltedDensity m p) 3 N A := by
    unfold scaledDiscreteMomentTail
    apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro j
    exact mul_nonneg (mul_nonneg (by positivity) (hrho j))
      (by unfold strictTailIndicator; split_ifs <;> norm_num)
  have hdenom : 1 ≤ A ^ (3 - r) := one_le_pow₀ hA
  calc
    scaledDiscreteMomentTail (positiveTiltedDensity m p) r N A ≤
        scaledDiscreteMomentTail (positiveTiltedDensity m p) 3 N A /
          A ^ (3 - r) := hcompare
    _ ≤ scaledDiscreteMomentTail (positiveTiltedDensity m p) 3 N A :=
      div_le_self hcubeNonneg hdenom
    _ ≤ ε := hNUI n hn

/-- Indicator of the closed head `x ≤ R`, complementary to
`strictTailIndicator R x`. -/
def weakHeadIndicator (R x : ℝ) : ℝ :=
  if x ≤ R then 1 else 0

theorem weakHeadIndicator_add_strictTailIndicator (R x : ℝ) :
    weakHeadIndicator R x + strictTailIndicator R x = 1 := by
  unfold weakHeadIndicator strictTailIndicator
  by_cases h : x ≤ R
  · rw [if_pos h, if_neg (not_lt_of_ge h)]
    norm_num
  · have hlt : R < x := lt_of_not_ge h
    rw [if_neg h, if_pos hlt]
    norm_num

/-- Bounded-head part of a normalized discrete moment. -/
def scaledDiscreteMomentHead (rho : Seq) (r N : ℕ) (A : ℝ) : ℝ :=
  ((N : ℝ) / (N : ℝ) ^ r) *
    ∑' j : ℕ, (j : ℝ) ^ r * rho j *
      weakHeadIndicator (A * (N : ℝ)) (j : ℝ)

/-- Exact decomposition of a normalized lattice moment into the closed head and
strict tail at `A*N`. -/
theorem scaledDiscreteMoment_eq_head_add_tail
    (rho : Seq) (r N : ℕ) (A : ℝ) (hrho : ∀ j : ℕ, 0 ≤ rho j)
    (hmoment : Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho j)) :
    scaledDiscreteMoment rho r N =
      scaledDiscreteMomentHead rho r N A +
        scaledDiscreteMomentTail rho r N A := by
  have hhead : Summable (fun j : ℕ ↦
      (j : ℝ) ^ r * rho j * weakHeadIndicator (A * (N : ℝ)) (j : ℝ)) := by
    apply hmoment.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (by positivity) (hrho j))
        (by unfold weakHeadIndicator; split_ifs <;> norm_num)
    · intro j
      have hindicator : weakHeadIndicator (A * (N : ℝ)) (j : ℝ) ≤ 1 := by
        unfold weakHeadIndicator
        split_ifs <;> norm_num
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hindicator
        (mul_nonneg (by positivity) (hrho j))
  have htail := momentTail_summable_of_moment rho r (A * (N : ℝ)) hrho hmoment
  have hsplit :
      (∑' j : ℕ, (j : ℝ) ^ r * rho j) =
        (∑' j : ℕ, (j : ℝ) ^ r * rho j *
          weakHeadIndicator (A * (N : ℝ)) (j : ℝ)) +
        ∑' j : ℕ, (j : ℝ) ^ r * rho j *
          strictTailIndicator (A * (N : ℝ)) (j : ℝ) := by
    rw [← hhead.tsum_add htail]
    apply tsum_congr
    intro j
    rw [← mul_add]
    rw [weakHeadIndicator_add_strictTailIndicator]
    ring
  unfold scaledDiscreteMoment scaledDiscreteMomentHead scaledDiscreteMomentTail
  rw [hsplit]
  ring

theorem scaledDiscreteMomentTail_nonneg
    (rho : Seq) (r N : ℕ) (A : ℝ) (hrho : ∀ j : ℕ, 0 ≤ rho j) :
    0 ≤ scaledDiscreteMomentTail rho r N A := by
  unfold scaledDiscreteMomentTail
  apply mul_nonneg (by positivity)
  apply tsum_nonneg
  intro j
  exact mul_nonneg (mul_nonneg (by positivity) (hrho j))
    (by unfold strictTailIndicator; split_ifs <;> norm_num)

/-- Truncation gluing with the order of limits made explicit: first choose a
macroscopic cutoff, then send the lattice scale to infinity.  Compact-head
convergence, convergence of the limiting heads, and a uniform discrete tail
bound imply convergence of the full normalized moments. -/
theorem scaledDiscreteMoment_tendsto_of_heads_and_uniform_tails
    (rho : ℕ → Seq) (r : ℕ) (headLimit : ℝ → ℝ) (L : ℝ)
    (hrho : ∀ N j : ℕ, 0 ≤ rho N j)
    (hmoment : ∀ N : ℕ, Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho N j))
    (hhead : ∀ A : ℝ, 0 ≤ A →
      Tendsto (fun N : ℕ ↦ scaledDiscreteMomentHead (rho N) r N A)
        atTop (nhds (headLimit A)))
    (hheadLimit : Tendsto headLimit atTop (nhds L))
    (htail : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ N : ℕ in atTop,
        scaledDiscreteMomentTail (rho N) r N A ≤ ε) :
    Tendsto (fun N : ℕ ↦ scaledDiscreteMoment (rho N) r N)
      atTop (nhds L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A₀, hA₀⟩ := Metric.tendsto_atTop.mp hheadLimit δ hδ
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.1 (htail δ hδ)
  let A : ℝ := max (max A₀ A₁) 0
  have hA0 : A₀ ≤ A := le_trans (le_max_left A₀ A₁) (le_max_left _ _)
  have hA1 : A₁ ≤ A := le_trans (le_max_right A₀ A₁) (le_max_left _ _)
  have hAnonneg : 0 ≤ A := le_max_right _ _
  have hlimitNear := hA₀ A hA0
  have htailAtA := hA₁ A hA1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 htailAtA
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hhead A hAnonneg) δ hδ
  refine ⟨max N₀ N₁, ?_⟩
  intro N hN
  have hN0 : N₀ ≤ N := le_trans (le_max_left N₀ N₁) hN
  have hN1 : N₁ ≤ N := le_trans (le_max_right N₀ N₁) hN
  have htailSmall := hN₀ N hN0
  have hheadNear := hN₁ N hN1
  have htailNonneg := scaledDiscreteMomentTail_nonneg
    (rho N) r N A (hrho N)
  have hdecomp := scaledDiscreteMoment_eq_head_add_tail
    (rho N) r N A (hrho N) (hmoment N)
  rw [Real.dist_eq] at hlimitNear hheadNear ⊢
  rw [hdecomp]
  calc
    |scaledDiscreteMomentHead (rho N) r N A +
        scaledDiscreteMomentTail (rho N) r N A - L| =
      |(scaledDiscreteMomentHead (rho N) r N A - headLimit A) +
        (headLimit A - L) + scaledDiscreteMomentTail (rho N) r N A| := by
          congr 1
          ring
    _ ≤ |scaledDiscreteMomentHead (rho N) r N A - headLimit A| +
          |headLimit A - L| +
            |scaledDiscreteMomentTail (rho N) r N A| := by
      exact (abs_add _ _).trans
        (add_le_add_right (abs_add _ _) _)
    _ = |scaledDiscreteMomentHead (rho N) r N A - headLimit A| +
          |headLimit A - L| +
            scaledDiscreteMomentTail (rho N) r N A := by
      rw [abs_of_nonneg htailNonneg]
    _ < ε := by
      dsimp [δ] at hheadNear hlimitNear htailSmall ⊢
      linarith

/-- Cofinal-scale form of the truncation gluing theorem.  The sequence index
and the lattice scale are deliberately separate, as required after extracting
an arbitrary Arzela--Ascoli subsequence. -/
theorem scaledDiscreteMoment_tendsto_of_heads_and_uniform_tails_along
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (r : ℕ)
    (headLimit : ℝ → ℝ) (L : ℝ)
    (hrho : ∀ k j : ℕ, 0 ≤ rho k j)
    (hmoment : ∀ k : ℕ, Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho k j))
    (hhead : ∀ A : ℝ, 0 ≤ A →
      Tendsto (fun k : ℕ ↦ scaledDiscreteMomentHead (rho k) r (scale k) A)
        atTop (nhds (headLimit A)))
    (hheadLimit : Tendsto headLimit atTop (nhds L))
    (htail : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ k : ℕ in atTop,
        scaledDiscreteMomentTail (rho k) r (scale k) A ≤ ε) :
    Tendsto (fun k : ℕ ↦ scaledDiscreteMoment (rho k) r (scale k))
      atTop (nhds L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A₀, hA₀⟩ := Metric.tendsto_atTop.mp hheadLimit δ hδ
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.1 (htail δ hδ)
  let A : ℝ := max (max A₀ A₁) 0
  have hA0 : A₀ ≤ A := le_trans (le_max_left A₀ A₁) (le_max_left _ _)
  have hA1 : A₁ ≤ A := le_trans (le_max_right A₀ A₁) (le_max_left _ _)
  have hAnonneg : 0 ≤ A := le_max_right _ _
  have hlimitNear := hA₀ A hA0
  have htailAtA := hA₁ A hA1
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 htailAtA
  obtain ⟨k₁, hk₁⟩ := Metric.tendsto_atTop.mp (hhead A hAnonneg) δ hδ
  refine ⟨max k₀ k₁, ?_⟩
  intro k hk
  have hk0 : k₀ ≤ k := le_trans (le_max_left k₀ k₁) hk
  have hk1 : k₁ ≤ k := le_trans (le_max_right k₀ k₁) hk
  have htailSmall := hk₀ k hk0
  have hheadNear := hk₁ k hk1
  have htailNonneg := scaledDiscreteMomentTail_nonneg
    (rho k) r (scale k) A (hrho k)
  have hdecomp := scaledDiscreteMoment_eq_head_add_tail
    (rho k) r (scale k) A (hrho k) (hmoment k)
  rw [Real.dist_eq] at hlimitNear hheadNear ⊢
  rw [hdecomp]
  calc
    |scaledDiscreteMomentHead (rho k) r (scale k) A +
        scaledDiscreteMomentTail (rho k) r (scale k) A - L| =
      |(scaledDiscreteMomentHead (rho k) r (scale k) A - headLimit A) +
        (headLimit A - L) + scaledDiscreteMomentTail (rho k) r (scale k) A| := by
          congr 1
          ring
    _ ≤ |scaledDiscreteMomentHead (rho k) r (scale k) A - headLimit A| +
          |headLimit A - L| +
            |scaledDiscreteMomentTail (rho k) r (scale k) A| := by
      exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ = |scaledDiscreteMomentHead (rho k) r (scale k) A - headLimit A| +
          |headLimit A - L| +
            scaledDiscreteMomentTail (rho k) r (scale k) A := by
      rw [abs_of_nonneg htailNonneg]
    _ < ε := by
      dsimp [δ] at hheadNear hlimitNear htailSmall ⊢
      linarith

/-- Continuum moment on the nonnegative half-line. -/
def continuumMoment (u : ℝ → ℝ) (r : ℕ) : ℝ :=
  ∫ x in Ici (0 : ℝ), x ^ r * u x

/-- Closed bounded-head continuum moment. -/
def continuumMomentHead (u : ℝ → ℝ) (r : ℕ) (A : ℝ) : ℝ :=
  ∫ x in Icc (0 : ℝ) A, x ^ r * u x

/-- Monotone removal of the continuum cutoff.  This is the final limit in the
two-stage moment-passage argument. -/
theorem continuumMomentHead_tendsto_continuumMoment
    (u : ℝ → ℝ) (r : ℕ)
    (hint : IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ))) :
    Tendsto (continuumMomentHead u r) atTop (nhds (continuumMoment u r)) := by
  have hmono : Monotone (fun A : ℝ ↦ Icc (0 : ℝ) A) := by
    intro A B hAB
    exact Icc_subset_Icc_right hAB
  have hunion : (⋃ A : ℝ, Icc (0 : ℝ) A) = Ici (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨A, hxA⟩
      exact hxA.1
    · intro hx
      exact mem_iUnion.2 ⟨x, hx, le_rfl⟩
  have hconv := tendsto_setIntegral_of_monotone
    (f := fun x : ℝ ↦ x ^ r * u x)
    (s := fun A : ℝ ↦ Icc (0 : ℝ) A)
    (fun _ ↦ measurableSet_Icc) hmono (by simpa [hunion] using hint)
  simpa only [continuumMomentHead, continuumMoment, hunion] using hconv

/-- Source-shaped `eq:momentpass` along a grid-time sequence.  The compact-head
Riemann-sum convergence is the preceding local-limit input; the global passage
is proved here from the actual orbit tail theorem and monotone cutoff removal. -/
theorem profileDensityMoment_tendsto_of_compact_heads_and_spineTail
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant)
    (hsharp : ∀ (n : ℕ) (R : ℝ), 0 < R →
      spineMarginalTail m data n R ≤
        spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R)
    (r : ℕ) (hr : r ≤ 3) (n : ℕ → ℕ) (T : ℝ) (hT : 0 < T)
    (hn : ∀ᶠ N : ℕ in atTop, (n N : ℝ) ≤ T * (N : ℝ))
    (u : ℝ → ℝ)
    (hint : IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ)))
    (hhead : ∀ A : ℝ, 0 ≤ A →
      Tendsto (fun N : ℕ ↦ scaledDiscreteMomentHead
        (positiveTiltedDensity m (orbit m data.law (n N))) r N A)
        atTop (nhds (continuumMomentHead u r A))) :
    Tendsto (fun N : ℕ ↦ scaledDiscreteMoment
      (positiveTiltedDensity m (orbit m data.law (n N))) r N)
      atTop (nhds (continuumMoment u r)) := by
  let rhoN : ℕ → Seq := fun N ↦
    positiveTiltedDensity m (orbit m data.law (n N))
  have hrho : ∀ N j : ℕ, 0 ≤ rhoN N j := by
    intro N j
    apply positiveTiltedDensity_nonneg m (orbit m data.law (n N))
      (le_trans (by norm_num) data.arity)
    exact orbit_critical m data.law (le_trans (by norm_num) data.arity)
      data.critical (n N)
  have hmoment : ∀ N : ℕ,
      Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rhoN N j) := by
    intro N
    have hpCrit := orbit_critical m data.law
      (le_trans (by norm_num) data.arity) data.critical (n N)
    have hpThird := orbit_tiltSummable_three m data.law
      (le_trans (by norm_num) data.arity) data.critical data.third (n N)
    have hzero : Summable (rhoN N) :=
      (positiveTiltedDensity_hasSum m (orbit m data.law (n N))
        (le_trans (by norm_num) data.arity) hpCrit).summable
    have hthree : Summable (fun j : ℕ ↦ (j : ℝ) ^ 3 * rhoN N j) :=
      positiveTiltedDensity_third_summable m (orbit m data.law (n N))
        (le_trans (by norm_num) data.arity) hpCrit hpThird
    exact moment_summable_of_zero_and_third (rhoN N) r hr (hrho N)
      hzero hthree
  have htail : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ N : ℕ in atTop,
        scaledDiscreteMomentTail (rhoN N) r N A ≤ ε := by
    intro ε hε
    have hUI := profileDensityMomentTail_uniform_integrability_of_spineTail
      m data hnonconstant hProduct hsharp r hr T hT ε hε
    filter_upwards [hUI] with A hUIA
    filter_upwards [hUIA, hn] with N hUIN hbound
    exact hUIN (n N) hbound
  apply scaledDiscreteMoment_tendsto_of_heads_and_uniform_tails
    rhoN r (continuumMomentHead u r) (continuumMoment u r)
      hrho hmoment
  · intro A hA
    simpa only [rhoN] using hhead A hA
  · exact continuumMomentHead_tendsto_continuumMoment u r hint
  · exact htail

/-- Cofinal-subsequence form of `eq:momentpass`.  `scale k` is the lattice
scale selected by compactness, while `generation k` is the time slice read on
that scale.  Keeping the two maps explicit prevents silently replacing an
Arzela--Ascoli subsequence by the full sequence. -/
theorem profileDensityMoment_tendsto_of_compact_heads_and_spineTail_along
    (m : ℕ) (data : ProfileInitialData m)
    (hnonconstant : ¬ IsDirac data.law)
    (hProduct : CDHLSProductFact m data.law data.arity data.critical hnonconstant)
    (hsharp : ∀ (n : ℕ) (R : ℝ), 0 < R →
      spineMarginalTail m data n R ≤
        spineMarginalTail m data 0 (R / 2) + 8 * (n : ℝ) / R)
    (r : ℕ) (hr : r ≤ 3)
    (scale generation : ℕ → ℕ)
    (hscale : Tendsto scale atTop atTop)
    (T : ℝ) (hT : 0 < T)
    (hgeneration : ∀ᶠ k : ℕ in atTop,
      (generation k : ℝ) ≤ T * (scale k : ℝ))
    (u : ℝ → ℝ)
    (hint : IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ)))
    (hhead : ∀ A : ℝ, 0 ≤ A →
      Tendsto (fun k : ℕ ↦ scaledDiscreteMomentHead
        (positiveTiltedDensity m (orbit m data.law (generation k)))
        r (scale k) A)
        atTop (nhds (continuumMomentHead u r A))) :
    Tendsto (fun k : ℕ ↦ scaledDiscreteMoment
      (positiveTiltedDensity m (orbit m data.law (generation k)))
      r (scale k))
      atTop (nhds (continuumMoment u r)) := by
  let rhoK : ℕ → Seq := fun k ↦
    positiveTiltedDensity m (orbit m data.law (generation k))
  have hrho : ∀ k j : ℕ, 0 ≤ rhoK k j := by
    intro k j
    apply positiveTiltedDensity_nonneg m (orbit m data.law (generation k))
      (le_trans (by norm_num) data.arity)
    exact orbit_critical m data.law (le_trans (by norm_num) data.arity)
      data.critical (generation k)
  have hmoment : ∀ k : ℕ,
      Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rhoK k j) := by
    intro k
    have hpCrit := orbit_critical m data.law
      (le_trans (by norm_num) data.arity) data.critical (generation k)
    have hpThird := orbit_tiltSummable_three m data.law
      (le_trans (by norm_num) data.arity) data.critical data.third (generation k)
    have hzero : Summable (rhoK k) :=
      (positiveTiltedDensity_hasSum m (orbit m data.law (generation k))
        (le_trans (by norm_num) data.arity) hpCrit).summable
    have hthree : Summable (fun j : ℕ ↦ (j : ℝ) ^ 3 * rhoK k j) :=
      positiveTiltedDensity_third_summable m (orbit m data.law (generation k))
        (le_trans (by norm_num) data.arity) hpCrit hpThird
    exact moment_summable_of_zero_and_third (rhoK k) r hr (hrho k)
      hzero hthree
  have htail : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ k : ℕ in atTop,
        scaledDiscreteMomentTail (rhoK k) r (scale k) A ≤ ε := by
    intro ε hε
    have hUI := profileDensityMomentTail_uniform_integrability_of_spineTail
      m data hnonconstant hProduct hsharp r hr T hT ε hε
    filter_upwards [hUI] with A hUIA
    have hUIscale : ∀ᶠ k : ℕ in atTop,
        ∀ n : ℕ, (n : ℝ) ≤ T * (scale k : ℝ) →
          scaledDiscreteMomentTail
            (positiveTiltedDensity m (orbit m data.law n)) r (scale k) A ≤ ε :=
      hscale hUIA
    filter_upwards [hUIscale, hgeneration] with k htailAtScale htime
    exact htailAtScale (generation k) htime
  apply scaledDiscreteMoment_tendsto_of_heads_and_uniform_tails_along
    rhoK scale r (continuumMomentHead u r) (continuumMoment u r)
      hrho hmoment
  · intro A hA
    simpa only [rhoK] using hhead A hA
  · exact continuumMomentHead_tendsto_continuumMoment u r hint
  · exact htail

end

end DerridaRetaux
