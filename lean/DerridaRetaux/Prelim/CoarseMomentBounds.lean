import DerridaRetaux.ExternalSignatures
import DerridaRetaux.Prelim.CubicMoment
import DerridaRetaux.Prelim.AtomTail
import Mathlib.Tactic

/-!
# Coarse normalized moment bounds

This file closes the internal deductions from the published product estimate in
`CDHLSProductFact`.  That fact is always an explicit theorem parameter: this file does
not import `HumanInputs` and introduces no trust primitive.

The binary third-moment comparison retains its atom at one.  The `m ≥ 3` branch uses
direct domination by the cubic carrier.  Thus the two cases in source equation
`eq:lowmoments` are not conflated.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- Convert the published inclusive-endpoint product estimate into a bound for every
half-open product.  The explicit constant also covers the two omitted prefixes `n = 0, 1`. -/
theorem criticalProduct_bound_all_of_published
    (m : ℕ) (p₀ : ProbabilityMass) (A : ℝ) (hA : 0 < A)
    (hpublished : ∀ n : ℕ, 1 ≤ n →
      criticalProduct m p₀ (n + 1) ≤ A * (n : ℝ) ^ 2) :
    ∀ n : ℕ,
      criticalProduct m p₀ n ≤
        (A + criticalProduct m p₀ 1 + 1) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  intro n
  have hPone : 0 ≤ criticalProduct m p₀ 1 :=
    criticalProduct_nonneg m p₀ 1
  have hBpos : 0 < A + criticalProduct m p₀ 1 + 1 := by linarith
  by_cases hnZero : n = 0
  · subst n
    simp only [criticalProduct_zero, Nat.zero_add, Nat.cast_one, one_pow, mul_one]
    linarith
  by_cases hnOne : n = 1
  · subst n
    norm_num
    nlinarith
  · have hnTwo : 2 ≤ n := by omega
    have hsource := hpublished (n - 1) (by omega)
    have hindex : n - 1 + 1 = n := by omega
    rw [hindex] at hsource
    have hAle : A ≤ A + criticalProduct m p₀ 1 + 1 := by linarith
    have hcast : ((n - 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n - 1 ≤ n + 1)
    have hsquare : ((n - 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hcast 2
    calc
      criticalProduct m p₀ n ≤ A * ((n - 1 : ℕ) : ℝ) ^ 2 := hsource
      _ ≤ (A + criticalProduct m p₀ 1 + 1) * ((n - 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hAle (sq_nonneg _)
      _ ≤ (A + criticalProduct m p₀ 1 + 1) * ((n + 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare hBpos.le

/-- `CDHLSProductFact`, kept as an explicit parameter, yields an all-generation product
bound.  The returned witness depends only on its published witness and the first prefix. -/
theorem criticalProduct_bound_all_of_CDHLSProductFact
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      criticalProduct m p₀ n ≤ B * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  rcases hProduct with ⟨A, hA, hpublished⟩
  refine ⟨A + criticalProduct m p₀ 1 + 1, ?_, ?_⟩
  · have hPone := criticalProduct_nonneg m p₀ 1
    linarith
  · exact criticalProduct_bound_all_of_published m p₀ A hA hpublished

/-- Explicit transfer from an all-generation product bound to the cubic moment.
The displayed constant records its dependence on `J₀`, `G₀`, and the product bound. -/
theorem normalizedCubicMoment_orbit_le_of_product_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (B : ℝ) (hB : 0 < B)
    (hproduct : ∀ n : ℕ,
      criticalProduct m p₀ n ≤ B * ((n + 1 : ℕ) : ℝ) ^ 2) :
    0 < normalizedCubicMoment m p₀ * tiltedPartition m p₀ * B + 1 ∧
      ∀ n : ℕ,
        normalizedCubicMoment m (orbit m p₀ n) ≤
          (normalizedCubicMoment m p₀ * tiltedPartition m p₀ * B + 1) *
            ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hJzero := normalizedCubicMoment_nonneg m p₀ hm hcrit
  have hGzero := tiltedPartition_nonneg m p₀
  have hcoefficient :
      0 ≤ normalizedCubicMoment m p₀ * tiltedPartition m p₀ * B :=
    mul_nonneg (mul_nonneg hJzero hGzero) hB.le
  constructor
  · linarith
  intro n
  have hncrit := orbit_critical m p₀ (by omega) hcrit n
  have hnthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n
  have hGone := tiltedPartition_one_le_of_critical m (orbit m p₀ n) (by omega) hncrit
  have hGnpos := tiltedPartition_pos_of_critical m (orbit m p₀ n) (by omega) hncrit
  have hratio :
      tiltedPartition m p₀ / tiltedPartition m (orbit m p₀ n) ≤
        tiltedPartition m p₀ := by
    apply (div_le_iff₀ hGnpos).2
    have := mul_le_mul_of_nonneg_left hGone hGzero
    simpa [mul_comm] using this
  have hPn := criticalProduct_nonneg m p₀ n
  rw [normalizedCubicMoment_orbit_eq m p₀ hm hcrit hthird n]
  calc
    normalizedCubicMoment m p₀ *
          (tiltedPartition m p₀ / tiltedPartition m (orbit m p₀ n)) *
        criticalProduct m p₀ n ≤
        normalizedCubicMoment m p₀ * tiltedPartition m p₀ *
          criticalProduct m p₀ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hJzero) hPn
    _ ≤ normalizedCubicMoment m p₀ * tiltedPartition m p₀ *
          (B * ((n + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (hproduct n) (mul_nonneg hJzero hGzero)
    _ = (normalizedCubicMoment m p₀ * tiltedPartition m p₀ * B) *
          ((n + 1 : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ (normalizedCubicMoment m p₀ * tiltedPartition m p₀ * B + 1) *
          ((n + 1 : ℕ) : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- Quadratic growth of `J_n`, conditional only on the explicitly supplied H1b fact. -/
theorem normalizedCubicMoment_orbit_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      normalizedCubicMoment m (orbit m p₀ n) ≤
        C * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  rcases criticalProduct_bound_all_of_CDHLSProductFact
      m p₀ hm hcrit hnonconstant hProduct with ⟨B, hB, hproduct⟩
  refine ⟨normalizedCubicMoment m p₀ * tiltedPartition m p₀ * B + 1, ?_⟩
  exact normalizedCubicMoment_orbit_le_of_product_bound
    m p₀ hm hcrit hthird B hB hproduct

/-- Non-Dirac critical input removes the binary fixed-point obstruction, while the
`m ≥ 3` branch is positive directly from the carrier comparison. -/
theorem normalizedCubicMoment_orbit_pos_of_not_isDirac
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀) (n : ℕ) :
    0 < normalizedCubicMoment m (orbit m p₀ n) := by
  have hinitial : 0 < normalizedCubicMoment m p₀ := by
    by_cases hmTwo : m = 2
    · subst m
      apply normalizedCubicMoment_two_pos_of_not_fixed p₀ hcrit hthird
      intro hp
      apply hnonconstant
      rw [hp]
      exact isDirac_diracMass 1
    · have hmThree : 3 ≤ m := by omega
      exact normalizedCubicMoment_pos_of_three_le m p₀ hmThree hcrit hthird
  exact normalizedCubicMoment_orbit_pos m p₀ hm hcrit hthird hinitial n

/-- Source-shaped package for equation `eq:J`: positivity, exact one-step recursion,
exact product representation, and the conditional quadratic bound. -/
theorem normalizedCubicMoment_eqJ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 0 < normalizedCubicMoment m (orbit m p₀ n)) ∧
      (∀ n : ℕ,
        tiltDenom m (orbit m p₀ n) *
            normalizedCubicMoment m (orbit m p₀ (n + 1)) =
          (m : ℝ) * normalizedCubicMoment m (orbit m p₀ n)) ∧
      (∀ n : ℕ,
        normalizedCubicMoment m (orbit m p₀ n) =
          normalizedCubicMoment m p₀ *
            (tiltedPartition m p₀ / tiltedPartition m (orbit m p₀ n)) *
              criticalProduct m p₀ n) ∧
      ∀ n : ℕ,
        normalizedCubicMoment m (orbit m p₀ n) ≤
          C * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  rcases normalizedCubicMoment_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hProduct with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_, ?_, ?_, hbound⟩
  · exact normalizedCubicMoment_orbit_pos_of_not_isDirac
      m p₀ hm hcrit hthird hnonconstant
  · exact normalizedCubicMoment_orbit_succ_cross m p₀ hm hcrit hthird
  · exact normalizedCubicMoment_orbit_eq m p₀ hm hcrit hthird

/-- Elementary interpolation inequality used below.  Taking `R = n + 1` gives a
series-safe replacement for the Cauchy--Schwarz step in the manuscript. -/
theorem square_le_cube_div_add_linear (k : ℕ) (R : ℝ) (hR : 0 < R) :
    (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 / R + R * (k : ℝ) := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hquadratic :
      0 ≤ (k : ℝ) ^ 2 - R * (k : ℝ) + R ^ 2 := by
    nlinarith [sq_nonneg (2 * (k : ℝ) - R), sq_nonneg R]
  have hproduct := mul_nonneg hk hquadratic
  apply (sub_le_iff_le_add).1
  apply (le_div_iff₀ hR).2
  nlinarith

/-- Summed interpolation inequality under one normalized critical tilted law. -/
theorem normalizedTilt_square_tsum_le_cube_div_add_mean
    (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p) (hthird : TiltSummable m 3 p)
    (R : ℝ) (hR : 0 < R) :
    (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m p k) ≤
      (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m p k) / R +
        R * (1 / ((m : ℝ) - 1)) := by
  have hsquare := normalizedTilt_square_summable m p hthird
  have hcube := normalizedTilt_cube_summable m p hthird
  have hmean := normalizedTilt_mean_hasSum m p (by omega) hcrit
  have hrhs :
      HasSum
        (fun k : ℕ ↦
          ((k : ℝ) ^ 3 * normalizedTilt m p k) / R +
            R * ((k : ℝ) * normalizedTilt m p k))
        ((∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m p k) / R +
          R * (1 / ((m : ℝ) - 1))) :=
    hcube.hasSum.div_const R |>.add (hmean.mul_left R)
  calc
    (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m p k) ≤
        ∑' k : ℕ, (
          ((k : ℝ) ^ 3 * normalizedTilt m p k) / R +
            R * ((k : ℝ) * normalizedTilt m p k)) := by
      apply hsquare.tsum_le_tsum _ hrhs.summable
      intro k
      have hq := normalizedTilt_nonneg m p (by omega) hcrit k
      calc
        (k : ℝ) ^ 2 * normalizedTilt m p k ≤
            ((k : ℝ) ^ 3 / R + R * (k : ℝ)) * normalizedTilt m p k :=
          mul_le_mul_of_nonneg_right (square_le_cube_div_add_linear k R hR) hq
        _ = ((k : ℝ) ^ 3 * normalizedTilt m p k) / R +
              R * ((k : ℝ) * normalizedTilt m p k) := by ring
    _ = (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m p k) / R +
          R * (1 / ((m : ℝ) - 1)) := hrhs.tsum_eq

/-- Transfer a quadratic `J` bound to the normalized third moment.  The binary branch
uses `4 J / 3 + q(1)` and bounds the explicit `firstTiltedAtom` correction by one;
the `m ≥ 3` branch uses direct carrier domination. -/
theorem normalizedTilt_cube_orbit_bound_of_cubicMoment_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (C : ℝ) (hC : 0 < C)
    (hJ : ∀ n : ℕ,
      normalizedCubicMoment m (orbit m p₀ n) ≤
        C * ((n + 1 : ℕ) : ℝ) ^ 2) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ n : ℕ,
      (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m (orbit m p₀ n) k) ≤
        C₃ * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  by_cases hmTwo : m = 2
  · subst m
    refine ⟨(4 / 3 : ℝ) * C + 1, by positivity, ?_⟩
    intro n
    have hncrit := orbit_critical 2 p₀ (by norm_num) hcrit n
    have hnthird := orbit_tiltSummable_three 2 p₀ (by norm_num) hcrit hthird n
    have hbinary :=
      normalizedTilt_cube_tsum_le_four_thirds_mul_cubicMoment_add_atom_one
        (orbit 2 p₀ n) hncrit hnthird
    have hatom : firstTiltedAtom 2 p₀ n ≤ 1 := by
      simpa [firstTiltedAtom] using
        (normalizedTiltLaw 2 (orbit 2 p₀ n) (by norm_num) hncrit).apply_le_one 1
    have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    have hNsquare : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    calc
      (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt 2 (orbit 2 p₀ n) k) ≤
          (4 / 3 : ℝ) * normalizedCubicMoment 2 (orbit 2 p₀ n) +
            normalizedTilt 2 (orbit 2 p₀ n) 1 := hbinary
      _ ≤ (4 / 3 : ℝ) * (C * ((n + 1 : ℕ) : ℝ) ^ 2) + 1 := by
        simpa [firstTiltedAtom] using
          add_le_add (mul_le_mul_of_nonneg_left (hJ n) (by norm_num)) hatom
      _ ≤ ((4 / 3 : ℝ) * C + 1) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith
  · have hmThree : 3 ≤ m := by omega
    refine ⟨C, hC, ?_⟩
    intro n
    have hncrit := orbit_critical m p₀ (by omega) hcrit n
    have hnthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n
    exact (normalizedTilt_cube_tsum_le_normalizedCubicMoment
      m (orbit m p₀ n) hmThree hncrit hnthird).trans (hJ n)

/-- The third-moment half of source equation `eq:lowmoments`, conditional on the
explicit H1b theorem parameter. -/
theorem normalizedTilt_cube_orbit_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ n : ℕ,
      (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m (orbit m p₀ n) k) ≤
        C₃ * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  rcases normalizedCubicMoment_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hProduct with ⟨C, hC, hJ⟩
  exact normalizedTilt_cube_orbit_bound_of_cubicMoment_bound
    m p₀ hm hcrit hthird C hC hJ

/-- A quadratic third-moment bound implies the linear second-moment bound in
`eq:lowmoments`.  The witness is explicitly `C₃ + 1`; the extra one bounds the
critical normalized mean `1 / (m - 1)`. -/
theorem normalizedTilt_square_orbit_bound_of_cube_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (C₃ : ℝ) (hC₃ : 0 < C₃)
    (hcube : ∀ n : ℕ,
      (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m (orbit m p₀ n) k) ≤
        C₃ * ((n + 1 : ℕ) : ℝ) ^ 2) :
    0 < C₃ + 1 ∧ ∀ n : ℕ,
      (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m (orbit m p₀ n) k) ≤
        (C₃ + 1) * ((n + 1 : ℕ) : ℝ) := by
  constructor
  · linarith
  intro n
  have hncrit := orbit_critical m p₀ (by omega) hcrit n
  have hnthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hinterp := normalizedTilt_square_tsum_le_cube_div_add_mean
    m (orbit m p₀ n) hm hncrit hnthird ((n + 1 : ℕ) : ℝ) hN
  have hmeanLe : 1 / ((m : ℝ) - 1) ≤ 1 := by
    have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    apply (div_le_one (by linarith : (0 : ℝ) < (m : ℝ) - 1)).2
    linarith
  calc
    (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m (orbit m p₀ n) k) ≤
        (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m (orbit m p₀ n) k) /
            ((n + 1 : ℕ) : ℝ) +
          ((n + 1 : ℕ) : ℝ) * (1 / ((m : ℝ) - 1)) := hinterp
    _ ≤ (C₃ * ((n + 1 : ℕ) : ℝ) ^ 2) / ((n + 1 : ℕ) : ℝ) +
          ((n + 1 : ℕ) : ℝ) * 1 := by
      exact add_le_add (div_le_div_of_nonneg_right (hcube n) hN.le)
        (mul_le_mul_of_nonneg_left hmeanLe hN.le)
    _ = (C₃ + 1) * ((n + 1 : ℕ) : ℝ) := by
      field_simp [hN.ne']
      ring

/-- The second-moment half of source equation `eq:lowmoments`. -/
theorem normalizedTilt_square_orbit_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ,
      (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m (orbit m p₀ n) k) ≤
        C₂ * ((n + 1 : ℕ) : ℝ) := by
  rcases normalizedTilt_cube_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hProduct with ⟨C₃, hC₃, hcube⟩
  refine ⟨C₃ + 1, ?_⟩
  exact normalizedTilt_square_orbit_bound_of_cube_bound
    m p₀ hm hcrit hthird C₃ hC₃ hcube

/-- Source-shaped combined form of `eq:lowmoments`, with one positive constant for both
bounds. -/
theorem normalizedTilt_lowMoments_orbit
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑' k : ℕ, (k : ℝ) ^ 3 * normalizedTilt m (orbit m p₀ n) k) ≤
          C * ((n + 1 : ℕ) : ℝ) ^ 2 ∧
        (∑' k : ℕ, (k : ℝ) ^ 2 * normalizedTilt m (orbit m p₀ n) k) ≤
          C * ((n + 1 : ℕ) : ℝ) := by
  rcases normalizedTilt_cube_orbit_bound
      m p₀ hm hcrit hthird hnonconstant hProduct with ⟨C₃, hC₃, hcube⟩
  have hsquarePackage := normalizedTilt_square_orbit_bound_of_cube_bound
    m p₀ hm hcrit hthird C₃ hC₃ hcube
  rcases hsquarePackage with ⟨hC₂, hsquare⟩
  refine ⟨C₃ + 1, hC₂, ?_⟩
  intro n
  constructor
  · exact (hcube n).trans <|
      mul_le_mul_of_nonneg_right (by linarith : C₃ ≤ C₃ + 1) (sq_nonneg _)
  · exact hsquare n

end

end DerridaRetaux
