import DerridaRetaux.Spine.IncrementBound
import DerridaRetaux.Model.TransportCoefficient
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-!
# Factorial-moment Cauchy bound

This file proves, rather than assumes, the size-biased Cauchy--Schwarz line used
in the cubic-spine increment estimate.
-/

/-- Variance nonnegativity for a countable real probability weight. -/
theorem weightedMean_sq_le_secondMoment
    (w X : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwOne : HasSum w 1)
    (hfirst : Summable (fun k ↦ w k * X k))
    (hsecond : Summable (fun k ↦ w k * X k ^ 2)) :
    (∑' k, w k * X k) ^ 2 ≤ ∑' k, w k * X k ^ 2 := by
  let mu : ℝ := ∑' k, w k * X k
  let second : ℝ := ∑' k, w k * X k ^ 2
  have hcombined :=
    (hsecond.hasSum.sub (hfirst.hasSum.mul_left (2 * mu))).add
      (hwOne.mul_left (mu ^ 2))
  have hvariance :
      HasSum (fun k ↦ w k * (X k - mu) ^ 2) (second - mu ^ 2) := by
    convert hcombined using 1
    · funext k
      ring
    · ring
  have hnonneg : 0 ≤ second - mu ^ 2 := by
    rw [← hvariance.tsum_eq]
    exact tsum_nonneg fun k ↦ mul_nonneg (hw k) (sq_nonneg (X k - mu))
  change mu ^ 2 ≤ second
  linarith

/-- Second falling-factorial moment of the normalized tilt. -/
def normalizedFactorialTwo (m : ℕ) (p : ProbabilityMass) : ℝ :=
  ∑' k, fallingFactorialTwo k * normalizedTilt m p k

/-- Third falling-factorial moment of the normalized tilt. -/
def normalizedFactorialThree (m : ℕ) (p : ProbabilityMass) : ℝ :=
  ∑' k, fallingFactorialThree k * normalizedTilt m p k

theorem normalizedFactorialTwo_summable
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hthird : TiltSummable m 3 p) :
    Summable (fun k ↦ fallingFactorialTwo k * normalizedTilt m p k) := by
  have hsquare := normalizedTilt_square_summable m p hthird
  have hmean := (normalizedTilt_mean_hasSum m p hm hcrit).summable
  apply (hsquare.sub hmean).congr
  intro k
  simp only [fallingFactorialTwo]
  ring

theorem normalizedFactorialThree_summable
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hthird : TiltSummable m 3 p) :
    Summable (fun k ↦ fallingFactorialThree k * normalizedTilt m p k) := by
  have hcube := normalizedTilt_cube_summable m p hthird
  have hsquare := normalizedTilt_square_summable m p hthird
  have hmean := (normalizedTilt_mean_hasSum m p hm hcrit).summable
  apply ((hcube.sub (hsquare.mul_left 3)).add (hmean.mul_left 2)).congr
  intro k
  simp only [fallingFactorialThree]
  ring

theorem normalizedFactorialTwo_nonneg
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    0 ≤ normalizedFactorialTwo m p := by
  unfold normalizedFactorialTwo
  exact tsum_nonneg fun k ↦
    mul_nonneg (fallingFactorialTwo_nonneg k)
      (normalizedTilt_nonneg m p hm hcrit k)

theorem normalizedFactorialThree_nonneg
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    0 ≤ normalizedFactorialThree m p := by
  unfold normalizedFactorialThree
  exact tsum_nonneg fun k ↦
    mul_nonneg (fallingFactorialThree_nonneg k)
      (normalizedTilt_nonneg m p hm hcrit k)

/-- Cauchy--Schwarz for the `k q(k)` size-biased law, in source notation. -/
theorem normalizedFactorialTwo_sq_le
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    normalizedFactorialTwo m p ^ 2 ≤
      (normalizedFactorialThree m p + normalizedFactorialTwo m p) /
        ((m : ℝ) - 1) := by
  let q := criticalTiltLaw m p hm hcrit
  let d : ℝ := (m : ℝ) - 1
  let w : ℕ → ℝ := fun k ↦ d * (k : ℝ) * q k
  let X : ℕ → ℝ := fun k ↦ (k : ℝ) - 1
  have hd : 0 < d := by
    dsimp only [d]
    have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hwNonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact mul_nonneg (mul_nonneg hd.le (Nat.cast_nonneg k)) (q.nonneg k)
  have hmean := normalizedTilt_mean_hasSum m p (by omega) hcrit
  have hwOneRaw := hmean.mul_left d
  have hwOne : HasSum w 1 := by
    convert hwOneRaw using 1
    · funext k
      simp only [w, q, criticalTiltLaw_apply]
      ring
    · dsimp only [d]
      field_simp
  have hb := (normalizedFactorialTwo_summable m p (by omega) hcrit hthird).hasSum
  have hg := (normalizedFactorialThree_summable m p (by omega) hcrit hthird).hasSum
  have hfirst :
      HasSum (fun k ↦ w k * X k) (d * normalizedFactorialTwo m p) := by
    convert hb.mul_left d using 1
    funext k
    simp only [w, X, q, criticalTiltLaw_apply, fallingFactorialTwo]
    ring
  have hgb :
      HasSum
        (fun k ↦
          fallingFactorialThree k * normalizedTilt m p k +
            fallingFactorialTwo k * normalizedTilt m p k)
        (normalizedFactorialThree m p + normalizedFactorialTwo m p) :=
    hg.add hb
  have hsecond :
      HasSum (fun k ↦ w k * X k ^ 2)
        (d * (normalizedFactorialThree m p + normalizedFactorialTwo m p)) := by
    convert hgb.mul_left d using 1
    funext k
    simp only [w, X, q, criticalTiltLaw_apply, fallingFactorialTwo,
      fallingFactorialThree]
    ring
  have hcauchy := weightedMean_sq_le_secondMoment w X hwNonneg hwOne
    hfirst.summable hsecond.summable
  rw [hfirst.tsum_eq, hsecond.tsum_eq] at hcauchy
  apply (le_div_iff₀ hd).2
  have hcancel :
      d * (normalizedFactorialTwo m p ^ 2 * d) ≤
        d * (normalizedFactorialThree m p + normalizedFactorialTwo m p) := by
    nlinarith
  exact (mul_le_mul_left hd).mp hcancel

/-- The fully model-instantiated arithmetic increment bound. -/
theorem criticalSpineIncrementRatio_le_four
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p) :
    spineIncrementRatio m (zeroTilt m p)
      (normalizedFactorialTwo m p) (normalizedFactorialThree m p) ≤ 4 := by
  apply spineIncrementRatio_le_four m hm
  · exact normalizedTilt_nonneg m p (by omega) hcrit 0
  · exact zeroTilt_le_one m p (by omega) hcrit
  · exact normalizedFactorialTwo_nonneg m p (by omega) hcrit
  · exact normalizedFactorialThree_nonneg m p (by omega) hcrit
  · exact normalizedFactorialTwo_sq_le m p hm hcrit hthird

end

end DerridaRetaux
