import DerridaRetaux.Analysis.ProfileConsequences
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

/-!
# Mean consequences of atomwise profile convergence

This file isolates the dominated-series step used after the profile theorem.  The
atomwise limits and their geometric domination are explicit theorem parameters;
the main compact profile estimate is not repackaged as an assumption.
-/

noncomputable section

/-- The (possibly extended-by-zero, if nonsummable) first moment of a real
probability mass.  Every critical orbit used below is proved summable before this
quantity is evaluated. -/
def probabilityFirstMoment (p : ProbabilityMass) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * p k

/-- Exponential first-moment summability at arity at least one implies ordinary
first-moment summability. -/
theorem probabilityFirstMoment_summable_of_tiltSummable
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (h : TiltSummable m 1 p) :
    Summable (fun k : ℕ ↦ (k : ℝ) * p k) := by
  have hweighted :
      Summable (fun k : ℕ ↦ (k : ℝ) * (m : ℝ) ^ k * p k) := by
    simpa [TiltSummable] using h
  refine Summable.of_norm_bounded
    (fun k : ℕ ↦ ‖(k : ℝ) * (m : ℝ) ^ k * p k‖) hweighted.norm ?_
  intro k
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : (1 : ℝ) ≤ (m : ℝ) ^ k := one_le_pow₀ hmReal
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hp : 0 ≤ p k := p.nonneg k
  change |(k : ℝ) * p k| ≤ |(k : ℝ) * (m : ℝ) ^ k * p k|
  rw [abs_of_nonneg (mul_nonneg hk hp)]
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hk (pow_nonneg (Nat.cast_nonneg m) k)) hp)]
  nlinarith [mul_le_mul_of_nonneg_left hpow hk,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hk) hp]

/-- Every critical orbit has a finite ordinary first moment. -/
theorem probabilityFirstMoment_orbit_summable
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (n : ℕ) :
    Summable (fun k : ℕ ↦ (k : ℝ) * orbit m p₀ n k) := by
  exact probabilityFirstMoment_summable_of_tiltSummable
    m (orbit m p₀ n) (by omega)
      (orbit_tiltSummable_one m p₀ (by omega) hcrit n)

/-- Tannery's theorem converts fixed-atom limits plus one summable geometric
majorant into the first-moment limit in source equation `eq:main2`. -/
theorem probabilityFirstMoment_tendsto_of_atom_limits
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m) (C : ℝ)
    (hfixed : ∀ k : ℕ, 1 ≤ k →
      Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * p n k) atTop
        (𝓝 (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k))))
    (hdom : ∀ n k : ℕ,
      ‖(n : ℝ) ^ 2 * ((k : ℝ) * p n k)‖ ≤
        C * (k : ℝ) * ((m : ℝ)⁻¹) ^ k) :
    Tendsto
      (fun n : ℕ ↦ ∑' k : ℕ, (n : ℝ) ^ 2 * ((k : ℝ) * p n k))
      atTop (𝓝 (4 * (m : ℝ) / ((m : ℝ) - 1) ^ 3)) := by
  have hmReal : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hmReal)
  have hinvNorm : ‖((m : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (lt_trans zero_lt_one hmReal)]
    exact inv_lt_one_of_one_lt₀ hmReal
  have hmajorantBase :
      Summable (fun k : ℕ ↦ (k : ℝ) * ((m : ℝ)⁻¹) ^ k) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hinvNorm)
  have hmajorant :
      Summable (fun k : ℕ ↦ C * (k : ℝ) * ((m : ℝ)⁻¹) ^ k) := by
    simpa [mul_assoc] using hmajorantBase.mul_left C
  let limitTerm : ℕ → ℝ := fun k ↦
    (k : ℝ) * (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k))
  have hpointwise : ∀ k : ℕ,
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) ^ 2 * ((k : ℝ) * p n k))
        atTop (𝓝 (limitTerm k)) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [limitTerm]
    · have hkOne : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hconst : Tendsto (fun _ : ℕ ↦ (k : ℝ)) atTop (𝓝 (k : ℝ)) :=
        tendsto_const_nhds
      have hmul := hconst.mul (hfixed k hkOne)
      convert hmul using 1
      · funext n
        ring
  have htannery := tendsto_tsum_of_dominated_convergence
    hmajorant hpointwise (Eventually.of_forall hdom)
  have hsum : (∑' k : ℕ, limitTerm k) =
      4 * (m : ℝ) / ((m : ℝ) - 1) ^ 3 := by
    have hgeom := tsum_coe_mul_geometric_of_norm_lt_one
      (𝕜 := ℝ) hinvNorm
    have hterm : limitTerm = fun k : ℕ ↦
        (4 / ((m : ℝ) - 1)) * ((k : ℝ) * ((m : ℝ)⁻¹) ^ k) := by
      funext k
      dsimp only [limitTerm]
      rw [inv_pow]
      field_simp only [hm0, pow_ne_zero]
      ring
    rw [hterm, tsum_mul_left, hgeom]
    have hfactor : (m : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hmReal.ne'
    have honeSub : 1 - (m : ℝ)⁻¹ = ((m : ℝ) - 1) / (m : ℝ) := by
      field_simp only [hm0]
      ring
    rw [honeSub]
    field_simp only [hm0, hfactor]
    ring
  rw [hsum] at htannery
  exact htannery

/-- A source-shaped nonnegative atom bound implies the norm majorant required by
Tannery's theorem. -/
theorem probabilityFirstMoment_tendsto_of_atom_limits_and_bound
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m) (C : ℝ)
    (hfixed : ∀ k : ℕ, 1 ≤ k →
      Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * p n k) atTop
        (𝓝 (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k))))
    (hatom : ∀ n k : ℕ, 1 ≤ k →
      (n : ℝ) ^ 2 * p n k ≤ C * ((m : ℝ)⁻¹) ^ k) :
    Tendsto
      (fun n : ℕ ↦ ∑' k : ℕ, (n : ℝ) ^ 2 * ((k : ℝ) * p n k))
      atTop (𝓝 (4 * (m : ℝ) / ((m : ℝ) - 1) ^ 3)) := by
  apply probabilityFirstMoment_tendsto_of_atom_limits m p hm C hfixed
  intro n k
  by_cases hk : k = 0
  · subst k
    simp
  · have hkOne : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hterm : 0 ≤ (n : ℝ) ^ 2 * ((k : ℝ) * p n k) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg k) ((p n).nonneg k))
    rw [Real.norm_eq_abs, abs_of_nonneg hterm]
    calc
      (n : ℝ) ^ 2 * ((k : ℝ) * p n k) =
          (k : ℝ) * ((n : ℝ) ^ 2 * p n k) := by ring
      _ ≤ (k : ℝ) * (C * ((m : ℝ)⁻¹) ^ k) :=
        mul_le_mul_of_nonneg_left (hatom n k hkOne) (Nat.cast_nonneg k)
      _ = C * (k : ℝ) * ((m : ℝ)⁻¹) ^ k := by ring

/-- Orbit form of the first-moment consequence, expressed with the manuscript's
literal expectation and an explicit geometric domination hypothesis. -/
theorem orbit_probabilityFirstMoment_tendsto_of_atom_limits
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (C : ℝ)
    (hfixed : ∀ k : ℕ, 1 ≤ k →
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) ^ 2 * orbit m p₀ n k) atTop
        (𝓝 (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k))))
    (hdom : ∀ n k : ℕ,
      ‖(n : ℝ) ^ 2 * ((k : ℝ) * orbit m p₀ n k)‖ ≤
        C * (k : ℝ) * ((m : ℝ)⁻¹) ^ k) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 *
        probabilityFirstMoment (orbit m p₀ n))
      atTop (𝓝 (4 * (m : ℝ) / ((m : ℝ) - 1) ^ 3)) := by
  have hseries := probabilityFirstMoment_tendsto_of_atom_limits
    m (orbit m p₀) hm C hfixed hdom
  apply hseries.congr'
  filter_upwards with n
  rw [probabilityFirstMoment]
  have hs := probabilityFirstMoment_orbit_summable m p₀ hm hcrit n
  rw [← hs.tsum_mul_left]

/-- Orbit specialization using the manuscript's uniform geometric atom bound. -/
theorem orbit_probabilityFirstMoment_tendsto_of_atom_limits_and_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (C : ℝ)
    (hfixed : ∀ k : ℕ, 1 ≤ k →
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) ^ 2 * orbit m p₀ n k) atTop
        (𝓝 (4 / (((m : ℝ) - 1) * (m : ℝ) ^ k))))
    (hatom : ∀ n k : ℕ, 1 ≤ k →
      (n : ℝ) ^ 2 * orbit m p₀ n k ≤ C * ((m : ℝ)⁻¹) ^ k) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 *
        probabilityFirstMoment (orbit m p₀ n))
      atTop (𝓝 (4 * (m : ℝ) / ((m : ℝ) - 1) ^ 3)) := by
  have hseries := probabilityFirstMoment_tendsto_of_atom_limits_and_bound
    m (orbit m p₀) hm C hfixed hatom
  apply hseries.congr'
  filter_upwards with n
  rw [probabilityFirstMoment]
  have hs := probabilityFirstMoment_orbit_summable m p₀ hm hcrit n
  rw [← hs.tsum_mul_left]

/-- Dividing the first-moment and survival limits yields the conditional-mean
The constant in source equation `eq:atoms`. -/
theorem conditionalFirstMoment_tendsto
    (m : ℕ) (p : ℕ → ProbabilityMass) (hm : 2 ≤ m)
    (hmean : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * probabilityFirstMoment (p n)) atTop
      (𝓝 (4 * (m : ℝ) / ((m : ℝ) - 1) ^ 3)))
    (hsurvival : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * survival (p n)) atTop
      (𝓝 (4 / ((m : ℝ) - 1) ^ 2))) :
    Tendsto
      (fun n : ℕ ↦ probabilityFirstMoment (p n) / survival (p n))
      atTop (𝓝 ((m : ℝ) / ((m : ℝ) - 1))) := by
  have hfactor : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hdenom : 4 / ((m : ℝ) - 1) ^ 2 ≠ 0 := by
    positivity
  have hquot := hmean.div hsurvival hdenom
  have heventual :
      (fun n : ℕ ↦
        ((n : ℝ) ^ 2 * probabilityFirstMoment (p n)) /
          ((n : ℝ) ^ 2 * survival (p n))) =ᶠ[atTop]
      (fun n : ℕ ↦ probabilityFirstMoment (p n) / survival (p n)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast (show n ≠ 0 by omega))
    rw [mul_div_mul_left _ _ hn0]
  have htarget :
      (4 * (m : ℝ) / ((m : ℝ) - 1) ^ 3) /
          (4 / ((m : ℝ) - 1) ^ 2) =
        (m : ℝ) / ((m : ℝ) - 1) := by
    field_simp only [hfactor]
    ring
  rw [htarget] at hquot
  exact hquot.congr' heventual

end

end DerridaRetaux
