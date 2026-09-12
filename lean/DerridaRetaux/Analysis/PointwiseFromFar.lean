import DerridaRetaux.Arrival.SourceDifferenceBound
import DerridaRetaux.Analysis.BoundaryPointwise
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology Set

namespace DerridaRetaux

noncomputable section

/-!
# Closing the far-arrival to pointwise chain

The far-arrival proposition has a bounded error `omega(N)`, whereas the boundary
completion module consumes a single positive constant.  This file performs that
last, elementary conversion and then applies the already verified finite-boundary
argument.
-/

theorem arrivalFarOmega_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (N : ℕ) :
    0 ≤ arrivalFarOmega m p₀ N := by
  unfold arrivalFarOmega
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · exact arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint 0 N
  · unfold coefficientTail
    apply tsum_nonneg
    intro k
    exact arrivalFormulaSource_nonneg
      m p₀ hm hcrit hnotBinaryFixedPoint 0 (k + (N - 1))

/-- The bounded `omega` form of `prop:far` implies the constant form required
by the finite-boundary pointwise theorem. -/
theorem arrivalCoeff_scaled_far_constant_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ B : ℝ, 0 < B ∧ ∀ n j : ℕ, pointwiseBoundaryCutoff m < j →
      ((n + j + 1 : ℕ) : ℝ) ^ 3 * arrivalCoeff m p₀ n (n + j) ≤
        B * ((n + 1 : ℕ) : ℝ) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  rcases arrivalCoeff_far_bound_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨Cfar, hCfar, homegaBounded, _homegaLimit, hfar⟩
  rcases homegaBounded.bddAbove with ⟨W, hW⟩
  have hWnonneg : 0 ≤ W :=
    (arrivalFarOmega_nonneg m p₀ hm hcrit hnotBinaryFixedPoint 0).trans
      (hW ⟨0, rfl⟩)
  let B : ℝ := 8 * (W + Cfar)
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro n j hj
  have hjOne : 1 ≤ j := by
    have hcutNonneg : 0 ≤ pointwiseBoundaryCutoff m := Nat.zero_le _
    omega
  have hNOne : 1 ≤ n + j := le_trans hjOne (Nat.le_add_left j n)
  have hcut : n + SourceMonomialTag.sourceDifferenceCutoff m < n + j := by
    simp only [pointwiseBoundaryCutoff, SourceMonomialTag.sourceDifferenceCutoff] at hj ⊢
    omega
  have hraw := hfar n (n + j) hcut
  have hdenom : 0 < (((n + j : ℕ) : ℝ) ^ 3) := by positivity
  have hscaled :
      (((n + j : ℕ) : ℝ) ^ 3) * arrivalCoeff m p₀ n (n + j) ≤
        arrivalFarOmega m p₀ (n + j) +
          Cfar * ((n + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hdenom] at hraw
    simpa only [mul_comm] using hraw
  have homegaLe : arrivalFarOmega m p₀ (n + j) ≤ W :=
    hW ⟨n + j, rfl⟩
  have htimeOne : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hnumerator :
      arrivalFarOmega m p₀ (n + j) + Cfar * ((n + 1 : ℕ) : ℝ) ≤
        (W + Cfar) * ((n + 1 : ℕ) : ℝ) := by
    calc
      arrivalFarOmega m p₀ (n + j) + Cfar * ((n + 1 : ℕ) : ℝ) ≤
          W + Cfar * ((n + 1 : ℕ) : ℝ) :=
        add_le_add_right homegaLe _
      _ ≤ W * ((n + 1 : ℕ) : ℝ) + Cfar * ((n + 1 : ℕ) : ℝ) := by
        exact add_le_add_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left htimeOne hWnonneg) _
      _ = (W + Cfar) * ((n + 1 : ℕ) : ℝ) := by ring
  have hratio :
      (((n + j + 1 : ℕ) : ℝ) ^ 3) ≤
        8 * (((n + j : ℕ) : ℝ) ^ 3) := by
    have hcastOne : (1 : ℝ) ≤ ((n + j : ℕ) : ℝ) := by exact_mod_cast hNOne
    have hlinear : (((n + j + 1 : ℕ) : ℝ)) ≤
        2 * ((n + j : ℕ) : ℝ) := by
      push_cast at hcastOne ⊢
      linarith
    calc
      (((n + j + 1 : ℕ) : ℝ) ^ 3) ≤
          (2 * ((n + j : ℕ) : ℝ)) ^ 3 := by gcongr
      _ = 8 * (((n + j : ℕ) : ℝ) ^ 3) := by ring
  have harrNonneg : 0 ≤ arrivalCoeff m p₀ n (n + j) :=
    arrivalCoeff_nonneg m p₀ hm hcrit hnotBinaryFixedPoint n (n + j)
  calc
    (((n + j + 1 : ℕ) : ℝ) ^ 3) * arrivalCoeff m p₀ n (n + j) ≤
        (8 * (((n + j : ℕ) : ℝ) ^ 3)) *
          arrivalCoeff m p₀ n (n + j) :=
      mul_le_mul_of_nonneg_right hratio harrNonneg
    _ = 8 * ((((n + j : ℕ) : ℝ) ^ 3) *
          arrivalCoeff m p₀ n (n + j)) := by ring
    _ ≤ 8 * (arrivalFarOmega m p₀ (n + j) +
          Cfar * ((n + 1 : ℕ) : ℝ)) := by gcongr
    _ ≤ 8 * ((W + Cfar) * ((n + 1 : ℕ) : ℝ)) := by gcongr
    _ = B * ((n + 1 : ℕ) : ℝ) := by
      dsimp only [B]
      ring

/-- Core completion of `prop:pointwise` from H1a/H1b supplied as explicit
parameters. -/
theorem positiveTiltedDensity_pointwise_of_H1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j : ℕ,
      positiveTiltedDensity m (orbit m p₀ n) j ≤
        C * ((n + 1 : ℕ) : ℝ) / ((n + j + 1 : ℕ) : ℝ) ^ 3 := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  rcases arrivalCoeff_scaled_far_constant_of_H1
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨B, hB, hfar⟩
  exact positiveTiltedDensity_pointwise_of_arrival_far
    m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint
      hExcess hProduct B hB.le hfar

end

end DerridaRetaux
