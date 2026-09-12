import DerridaRetaux.Analysis.SmoothingOrbitBounds
import DerridaRetaux.Arrival.ArrivalRecursion
import DerridaRetaux.Model.TransportLimit
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Boundary completion of the cubic pointwise estimate

This file isolates `U27`, the finite-boundary part of `prop:pointwise`.  The far-region
estimate remains an explicit upstream premise.  The nonlinear source bound is derived
from the actual critical orbit and the cubic weighted `l1` estimate; the global
pointwise estimate is never assumed.
-/

/-- The nonlinear part of the exact density recursion `eq:rhor`. -/
def densityNonlinearSource
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  fun j : ℕ ↦
    ∑ r ∈ Finset.Ico 2 (m + 1),
      densityCoeff m r (orbit m p₀ s) *
        shiftRightPow (r - 2)
          (convPow r (positiveTiltedDensity m (orbit m p₀ s))) j

/-- The exact orbit recursion, with its nonlinear source named separately. -/
theorem positiveTiltedDensity_orbit_succ_eq_transport_add_source
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (s j : ℕ) :
    positiveTiltedDensity m (orbit m p₀ (s + 1)) j =
      transportCoeff m (orbit m p₀ s) *
          positiveTiltedDensity m (orbit m p₀ s) (j + 1) +
        densityNonlinearSource m p₀ s j := by
  have h := congrFun (positiveTiltedDensity_orbit_succ m p₀ hm hcrit s) j
  simpa only [densityNonlinearSource, shiftLeft_apply] using h

/-- A summable nonnegative sequence dominates each of its terms. -/
theorem apply_le_tsum_of_nonneg
    (a : Seq) (ha : ∀ k : ℕ, 0 ≤ a k) (hsum : Summable a) (j : ℕ) :
    a j ≤ ∑' k : ℕ, a k := by
  simpa using hsum.sum_le_tsum {j} (fun k _ ↦ ha k)

/-- Every coefficient is bounded by the cubic weighted `l1` mass. -/
theorem abs_apply_le_weightedL1Three
    (L : ℝ) (hL : 0 < L) (a : Seq)
    (hsum : Summable (weightedAbs L a)) (j : ℕ) :
    |a j| ≤ weightedL1Three L a := by
  have hweight : 1 ≤ cubicWeight L j := by
    unfold cubicWeight
    have hj : 0 ≤ (j : ℝ) / L := div_nonneg (Nat.cast_nonneg j) hL.le
    nlinarith [sq_nonneg (1 + (j : ℝ) / L)]
  calc
    |a j| ≤ cubicWeight L j * |a j| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight (abs_nonneg (a j))
    _ = weightedAbs L a j := rfl
    _ ≤ ∑' k : ℕ, weightedAbs L a k :=
      apply_le_tsum_of_nonneg (weightedAbs L a) (weightedAbs_nonneg L hL a) hsum j
    _ = weightedL1Three L a := by rw [weightedL1Three_eq_tsum_weightedAbs]

/-- A zero-extending right shift preserves a uniform pointwise upper bound. -/
theorem shiftRightPow_apply_le
    (t : ℕ) (a : Seq) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ k : ℕ, a k ≤ B) (j : ℕ) :
    shiftRightPow t a j ≤ B := by
  induction t generalizing a j with
  | zero => exact ha j
  | succ t ih =>
      rw [shiftRightPow_succ]
      apply ih (shiftRight a)
      intro k
      cases k with
      | zero => simpa using hB
      | succ k => simpa using ha k

/-- Iterated zero-extending right shifts preserve pointwise nonnegativity. -/
theorem shiftRightPow_nonneg
    (t : ℕ) (a : Seq) (ha : ∀ k : ℕ, 0 ≤ a k) (j : ℕ) :
    0 ≤ shiftRightPow t a j := by
  induction t generalizing a j with
  | zero => exact ha j
  | succ t ih =>
      rw [shiftRightPow_succ]
      apply ih (shiftRight a)
      intro k
      cases k with
      | zero => simp
      | succ k => simpa using ha k

/-- The finite constant that controls every nonlinear source coefficient. -/
def densitySourceMajorant (m : ℕ) (A : ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 2 (m + 1), (Nat.choose m r : ℝ) * A ^ r

theorem densitySourceMajorant_nonneg
    (m : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ densitySourceMajorant m A := by
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hA r)

/-- The actual nonlinear source is `O((s+1)^-2)` from weighted `l1` alone.
No pointwise density estimate is used. -/
theorem densityNonlinearSource_orbit_le_of_weightedL1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A : ℝ) (hA : 0 ≤ A)
    (hL1 : ∀ s : ℕ,
      weightedL1Three ((s + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / ((s + 1 : ℕ) : ℝ))
    (s j : ℕ) :
    densityNonlinearSource m p₀ s j ≤
      densitySourceMajorant m A / ((s + 1 : ℕ) : ℝ) ^ 2 := by
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  let rhoS : Seq := positiveTiltedDensity m (orbit m p₀ s)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le s))
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  have hsthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird s
  have hrhoNonneg : ∀ k : ℕ, 0 ≤ rhoS k := by
    intro k
    exact positiveTiltedDensity_nonneg m (orbit m p₀ s) (by omega) hscrit k
  have hrhoSum : Summable (weightedAbs L rhoS) := by
    simpa only [L, rhoS] using
      weightedL1Three_positiveTiltedDensity_summable
        m (orbit m p₀ s) L (by omega) hscrit hsthird hLpos
  rw [densityNonlinearSource]
  calc
    ∑ r ∈ Finset.Ico 2 (m + 1),
        densityCoeff m r (orbit m p₀ s) *
          shiftRightPow (r - 2) (convPow r rhoS) j ≤
        ∑ r ∈ Finset.Ico 2 (m + 1),
          (Nat.choose m r : ℝ) * (A ^ r / L ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrLower : 2 ≤ r := (Finset.mem_Ico.mp hr).1
      have hrhoPowSum : Summable (weightedAbs L (convPow r rhoS)) :=
        weightedAbs_convPow_summable L hL rhoS hrhoSum r
      have hpowNonneg : ∀ k : ℕ, 0 ≤ convPow r rhoS k :=
        convPow_nonneg r rhoS hrhoNonneg
      have hmassNonneg : 0 ≤ weightedL1Three L rhoS :=
        weightedL1Three_nonneg L hLpos rhoS
      have hmassBound : weightedL1Three L rhoS ≤ A / L := by
        simpa only [L, rhoS] using hL1 s
      have hdivNonneg : 0 ≤ A / L := div_nonneg hA hLpos.le
      have hcoeffBound : ∀ k : ℕ, convPow r rhoS k ≤ A ^ r / L ^ 2 := by
        intro k
        calc
          convPow r rhoS k ≤ |convPow r rhoS k| := le_abs_self _
          _ ≤ weightedL1Three L (convPow r rhoS) :=
            abs_apply_le_weightedL1Three L hLpos (convPow r rhoS) hrhoPowSum k
          _ ≤ weightedL1Three L rhoS ^ r :=
            weightedL1Three_convPow_le_pow L hL rhoS hrhoSum r
          _ ≤ (A / L) ^ r := by gcongr
          _ = A ^ r / L ^ r := by rw [div_pow]
          _ ≤ A ^ r / L ^ 2 := by
            rw [div_le_div_iff₀ (pow_pos hLpos r) (pow_pos hLpos 2)]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hL hrLower) (pow_nonneg hA r)
      have hshiftBound :
          shiftRightPow (r - 2) (convPow r rhoS) j ≤ A ^ r / L ^ 2 :=
        shiftRightPow_apply_le (r - 2) (convPow r rhoS) (A ^ r / L ^ 2)
          (div_nonneg (pow_nonneg hA r) (pow_nonneg hLpos.le 2)) hcoeffBound j
      have hcoeff := densityCoeff_nonneg_and_le_choose
        m r (orbit m p₀ s) hm hscrit
      have hshiftNonneg :
          0 ≤ shiftRightPow (r - 2) (convPow r rhoS) j := by
        exact shiftRightPow_nonneg (r - 2) (convPow r rhoS) hpowNonneg j
      exact mul_le_mul hcoeff.2 hshiftBound hshiftNonneg (Nat.cast_nonneg _)
    _ = densitySourceMajorant m A / L ^ 2 := by
      rw [densitySourceMajorant, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = densitySourceMajorant m A / ((s + 1 : ℕ) : ℝ) ^ 2 := rfl

/-- One density step is bounded by pure left transport plus the quadratic source
majorant obtained from weighted mass. -/
theorem positiveTiltedDensity_orbit_succ_le_shift_add_majorant
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A : ℝ) (hA : 0 ≤ A)
    (hL1 : ∀ s : ℕ,
      weightedL1Three ((s + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / ((s + 1 : ℕ) : ℝ))
    (s j : ℕ) :
    positiveTiltedDensity m (orbit m p₀ (s + 1)) j ≤
      positiveTiltedDensity m (orbit m p₀ s) (j + 1) +
        densitySourceMajorant m A / ((s + 1 : ℕ) : ℝ) ^ 2 := by
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  have hrho : 0 ≤ positiveTiltedDensity m (orbit m p₀ s) (j + 1) :=
    positiveTiltedDensity_nonneg m (orbit m p₀ s) (by omega) hscrit (j + 1)
  have hc : transportCoeff m (orbit m p₀ s) ≤ 1 :=
    transportCoeff_le_one m (orbit m p₀ s) (by omega) hscrit
  have htransport :
      transportCoeff m (orbit m p₀ s) *
          positiveTiltedDensity m (orbit m p₀ s) (j + 1) ≤
        positiveTiltedDensity m (orbit m p₀ s) (j + 1) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hrho
  rw [positiveTiltedDensity_orbit_succ_eq_transport_add_source
    m p₀ hm hcrit s j]
  exact add_le_add htransport
    (densityNonlinearSource_orbit_le_of_weightedL1
      m p₀ hm hcrit hthird A hA hL1 s j)

/-- Iterating along a transport diagonal for a fixed number of steps produces
only a finite quadratic source error. -/
theorem positiveTiltedDensity_orbit_add_le_shift_add_majorant
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A : ℝ) (hA : 0 ≤ A)
    (hL1 : ∀ s : ℕ,
      weightedL1Three ((s + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / ((s + 1 : ℕ) : ℝ))
    (a t j : ℕ) :
    positiveTiltedDensity m (orbit m p₀ (a + t)) j ≤
      positiveTiltedDensity m (orbit m p₀ a) (j + t) +
        densitySourceMajorant m A * (t : ℝ) /
          ((a + 1 : ℕ) : ℝ) ^ 2 := by
  induction t generalizing j with
  | zero => simp
  | succ t ih =>
      let D := densitySourceMajorant m A
      let L₀ : ℝ := ((a + 1 : ℕ) : ℝ)
      let Lₜ : ℝ := ((a + t + 1 : ℕ) : ℝ)
      have hD : 0 ≤ D := densitySourceMajorant_nonneg m A hA
      have hL₀ : 0 < L₀ := by positivity
      have hLₜ : 0 < Lₜ := by positivity
      have hscale : L₀ ≤ Lₜ := by
        dsimp [L₀, Lₜ]
        exact_mod_cast (show a + 1 ≤ a + t + 1 by omega)
      have hdenom : D / Lₜ ^ 2 ≤ D / L₀ ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hLₜ 2) (pow_pos hL₀ 2)]
        exact mul_le_mul_of_nonneg_left (by gcongr) hD
      have hstep := positiveTiltedDensity_orbit_succ_le_shift_add_majorant
        m p₀ hm hcrit hthird A hA hL1 (a + t) j
      have hind := ih (j + 1)
      rw [show a + (t + 1) = (a + t) + 1 by omega]
      calc
        positiveTiltedDensity m (orbit m p₀ ((a + t) + 1)) j ≤
            positiveTiltedDensity m (orbit m p₀ (a + t)) (j + 1) +
              D / Lₜ ^ 2 := by
          simpa only [D, Lₜ, Nat.cast_add, Nat.cast_one] using hstep
        _ ≤
            (positiveTiltedDensity m (orbit m p₀ a) (j + 1 + t) +
                D * (t : ℝ) / L₀ ^ 2) + D / Lₜ ^ 2 := by
          exact add_le_add_right (by simpa only [D, L₀] using hind) _
        _ ≤
            positiveTiltedDensity m (orbit m p₀ a) (j + (t + 1)) +
              D * ((t + 1 : ℕ) : ℝ) / L₀ ^ 2 := by
          calc
            (positiveTiltedDensity m (orbit m p₀ a) (j + 1 + t) +
                D * (t : ℝ) / L₀ ^ 2) + D / Lₜ ^ 2 ≤
                (positiveTiltedDensity m (orbit m p₀ a) (j + 1 + t) +
                  D * (t : ℝ) / L₀ ^ 2) + D / L₀ ^ 2 :=
              add_le_add_left hdenom _
            _ = positiveTiltedDensity m (orbit m p₀ a) (j + (t + 1)) +
                D * ((t + 1 : ℕ) : ℝ) / L₀ ^ 2 := by
              rw [show j + 1 + t = j + (t + 1) by omega]
              push_cast
              ring
        _ = positiveTiltedDensity m (orbit m p₀ a) (j + (t + 1)) +
              densitySourceMajorant m A * ((t + 1 : ℕ) : ℝ) /
                ((a + 1 : ℕ) : ℝ) ^ 2 := rfl

/-- At each generation, a density coefficient is bounded by the corresponding
cubic weighted `l1` mass. -/
theorem positiveTiltedDensity_apply_le_weightedL1Three
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (n j : ℕ) :
    positiveTiltedDensity m (orbit m p₀ n) j ≤
      weightedL1Three ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n)) := by
  let L : ℝ := ((n + 1 : ℕ) : ℝ)
  let rhoN : Seq := positiveTiltedDensity m (orbit m p₀ n)
  have hL : 0 < L := by positivity
  have hncrit := orbit_critical m p₀ (by omega) hcrit n
  have hnthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird n
  have hsum : Summable (weightedAbs L rhoN) := by
    simpa only [L, rhoN] using
      weightedL1Three_positiveTiltedDensity_summable
        m (orbit m p₀ n) L (by omega) hncrit hnthird hL
  calc
    positiveTiltedDensity m (orbit m p₀ n) j ≤
        |positiveTiltedDensity m (orbit m p₀ n) j| := le_abs_self _
    _ ≤ weightedL1Three L rhoN :=
      abs_apply_le_weightedL1Three L hL rhoN hsum j
    _ = weightedL1Three ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n)) := rfl

/-- A far-region cubic bound completes to all boundary offsets and all small
generations.  The conclusion is written without division for convenient finite
arithmetic; the source-shaped quotient form follows below. -/
theorem positiveTiltedDensity_scaledPointwise_of_far_and_weightedL1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A F : ℝ) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hL1 : ∀ s : ℕ,
      weightedL1Three ((s + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / ((s + 1 : ℕ) : ℝ))
    (K : ℕ)
    (hfar : ∀ n j : ℕ, K < j →
      ((n + j + 1 : ℕ) : ℝ) ^ 3 *
          positiveTiltedDensity m (orbit m p₀ n) j ≤
        F * ((n + 1 : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j : ℕ,
      ((n + j + 1 : ℕ) : ℝ) ^ 3 *
          positiveTiltedDensity m (orbit m p₀ n) j ≤
        C * ((n + 1 : ℕ) : ℝ) := by
  let R : ℕ := K + 2
  let D : ℝ := densitySourceMajorant m A
  let C : ℝ :=
    F + 32 * D * (R : ℝ) + A * (3 * (R : ℝ)) ^ 3 + 1
  have hD : 0 ≤ D := densitySourceMajorant_nonneg m A hA
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n j
  let L : ℝ := ((n + 1 : ℕ) : ℝ)
  let M : ℝ := ((n + j + 1 : ℕ) : ℝ)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  by_cases hj : K < j
  · have hfarNow := hfar n j hj
    have hFC : F ≤ C := by
      dsimp [C]
      have hrest :
          0 ≤ 32 * D * (R : ℝ) + A * (3 * (R : ℝ)) ^ 3 + 1 := by
        positivity
      linarith
    exact hfarNow.trans
      (mul_le_mul_of_nonneg_right hFC (Nat.cast_nonneg (n + 1)))
  · have hjle : j ≤ K := by omega
    by_cases hn : 2 * R ≤ n
    · have hRn : R ≤ n := by omega
      let a : ℕ := n - R
      let Lₐ : ℝ := ((a + 1 : ℕ) : ℝ)
      have haEq : a + R = n := by
        dsimp [a]
        exact Nat.sub_add_cancel hRn
      have hLa : 0 < Lₐ := by positivity
      have hiter := positiveTiltedDensity_orbit_add_le_shift_add_majorant
        m p₀ hm hcrit hthird A hA hL1 a R j
      rw [haEq] at hiter
      have hjFar : K < j + R := by
        dsimp [R]
        omega
      have hfarBase := hfar a (j + R) hjFar
      have hindex : a + (j + R) + 1 = n + j + 1 := by omega
      have hbaseScaled :
          M ^ 3 * positiveTiltedDensity m (orbit m p₀ a) (j + R) ≤
            F * L := by
        calc
          M ^ 3 * positiveTiltedDensity m (orbit m p₀ a) (j + R) =
              ((a + (j + R) + 1 : ℕ) : ℝ) ^ 3 *
                positiveTiltedDensity m (orbit m p₀ a) (j + R) := by
            rw [hindex]
          _ ≤ F * ((a + 1 : ℕ) : ℝ) := hfarBase
          _ ≤ F * L := by
            apply mul_le_mul_of_nonneg_left _ hF
            dsimp [L, a]
            exact_mod_cast (show n - R + 1 ≤ n + 1 by omega)
      have hMLNat : n + j + 1 ≤ 2 * (n + 1) := by
        have hKn : K ≤ n + 1 := by
          dsimp [R] at hn
          omega
        omega
      have hML : M ≤ 2 * L := by
        dsimp [M, L]
        exact_mod_cast hMLNat
      have hMNonneg : 0 ≤ M := by positivity
      have hM3 : M ^ 3 ≤ 8 * L ^ 3 := by
        calc
          M ^ 3 ≤ (2 * L) ^ 3 := by gcongr
          _ = 8 * L ^ 3 := by ring
      have hLLaNat : n + 1 ≤ 2 * (a + 1) := by
        dsimp [a]
        omega
      have hLLa : L ≤ 2 * Lₐ := by
        dsimp [L, Lₐ]
        exact_mod_cast hLLaNat
      have hL2 : L ^ 2 ≤ 4 * Lₐ ^ 2 := by
        calc
          L ^ 2 ≤ (2 * Lₐ) ^ 2 := by gcongr
          _ = 4 * Lₐ ^ 2 := by ring
      have hratio : M ^ 3 / Lₐ ^ 2 ≤ 32 * L := by
        rw [div_le_iff₀ (pow_pos hLa 2)]
        calc
          M ^ 3 ≤ 8 * L ^ 3 := hM3
          _ = 8 * L * L ^ 2 := by ring
          _ ≤ 8 * L * (4 * Lₐ ^ 2) := by
            exact mul_le_mul_of_nonneg_left hL2 (mul_nonneg (by norm_num) hLpos.le)
          _ = 32 * L * Lₐ ^ 2 := by ring
      have hDR : 0 ≤ D * (R : ℝ) :=
        mul_nonneg hD (Nat.cast_nonneg R)
      have hsourceScaled :
          M ^ 3 * (D * (R : ℝ) / Lₐ ^ 2) ≤
            32 * D * (R : ℝ) * L := by
        calc
          M ^ 3 * (D * (R : ℝ) / Lₐ ^ 2) =
              (D * (R : ℝ)) * (M ^ 3 / Lₐ ^ 2) := by ring
          _ ≤ (D * (R : ℝ)) * (32 * L) :=
            mul_le_mul_of_nonneg_left hratio hDR
          _ = 32 * D * (R : ℝ) * L := by ring
      have hscaledIter := mul_le_mul_of_nonneg_left hiter (pow_nonneg hMNonneg 3)
      have hcore :
          M ^ 3 * positiveTiltedDensity m (orbit m p₀ n) j ≤
            (F + 32 * D * (R : ℝ)) * L := by
        calc
          M ^ 3 * positiveTiltedDensity m (orbit m p₀ n) j ≤
              M ^ 3 *
                (positiveTiltedDensity m (orbit m p₀ a) (j + R) +
                  D * (R : ℝ) / Lₐ ^ 2) := by
            simpa only [D, Lₐ] using hscaledIter
          _ = M ^ 3 * positiveTiltedDensity m (orbit m p₀ a) (j + R) +
                M ^ 3 * (D * (R : ℝ) / Lₐ ^ 2) := by ring
          _ ≤ F * L + 32 * D * (R : ℝ) * L :=
            add_le_add hbaseScaled hsourceScaled
          _ = (F + 32 * D * (R : ℝ)) * L := by ring
      have hcoreC : F + 32 * D * (R : ℝ) ≤ C := by
        dsimp [C]
        have hrest : 0 ≤ A * (3 * (R : ℝ)) ^ 3 + 1 := by positivity
        linarith
      exact hcore.trans (mul_le_mul_of_nonneg_right hcoreC hLpos.le)
    · have hnlt : n < 2 * R := by omega
      have hrhoNonneg :
          0 ≤ positiveTiltedDensity m (orbit m p₀ n) j :=
        positiveTiltedDensity_nonneg m (orbit m p₀ n) (by omega)
          (orbit_critical m p₀ (by omega) hcrit n) j
      have hrhoMass := positiveTiltedDensity_apply_le_weightedL1Three
        m p₀ hm hcrit hthird n j
      have hrhoDiv : positiveTiltedDensity m (orbit m p₀ n) j ≤ A / L :=
        hrhoMass.trans (by simpa only [L] using hL1 n)
      have hdiv : A / L ≤ A * L := by
        rw [div_le_iff₀ hLpos]
        have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hL
        calc
          A ≤ A * L ^ 2 := by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hLsq hA
          _ = A * L * L := by ring
      have hrhoLinear : positiveTiltedDensity m (orbit m p₀ n) j ≤ A * L :=
        hrhoDiv.trans hdiv
      have hMRNat : n + j + 1 ≤ 3 * R := by
        dsimp [R] at hjle ⊢
        omega
      have hMR : M ≤ 3 * (R : ℝ) := by
        dsimp [M]
        exact_mod_cast hMRNat
      have hM3R : M ^ 3 ≤ (3 * (R : ℝ)) ^ 3 := by gcongr
      have hsmall :
          M ^ 3 * positiveTiltedDensity m (orbit m p₀ n) j ≤
            A * (3 * (R : ℝ)) ^ 3 * L := by
        calc
          M ^ 3 * positiveTiltedDensity m (orbit m p₀ n) j ≤
              (3 * (R : ℝ)) ^ 3 * (A * L) :=
            mul_le_mul hM3R hrhoLinear hrhoNonneg (by positivity)
          _ = A * (3 * (R : ℝ)) ^ 3 * L := by ring
      have hsmallC : A * (3 * (R : ℝ)) ^ 3 ≤ C := by
        dsimp [C]
        have hrest : 0 ≤ F + 32 * D * (R : ℝ) + 1 := by positivity
        linarith
      exact hsmall.trans (mul_le_mul_of_nonneg_right hsmallC hLpos.le)

/-- Quotient form of the completed cubic pointwise bound. -/
theorem positiveTiltedDensity_pointwise_of_far_and_weightedL1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A F : ℝ) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hL1 : ∀ s : ℕ,
      weightedL1Three ((s + 1 : ℕ) : ℝ)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / ((s + 1 : ℕ) : ℝ))
    (K : ℕ)
    (hfar : ∀ n j : ℕ, K < j →
      ((n + j + 1 : ℕ) : ℝ) ^ 3 *
          positiveTiltedDensity m (orbit m p₀ n) j ≤
        F * ((n + 1 : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j : ℕ,
      positiveTiltedDensity m (orbit m p₀ n) j ≤
        C * ((n + 1 : ℕ) : ℝ) / ((n + j + 1 : ℕ) : ℝ) ^ 3 := by
  rcases positiveTiltedDensity_scaledPointwise_of_far_and_weightedL1
    m p₀ hm hcrit hthird A F hA hF hL1 K hfar with ⟨C, hC, hscaled⟩
  refine ⟨C, hC, ?_⟩
  intro n j
  have hden : 0 < ((n + j + 1 : ℕ) : ℝ) ^ 3 := by positivity
  rw [le_div_iff₀ hden]
  simpa only [mul_comm] using hscaled n j

/-- The fixed source cutoff `K_m = 2m(m-1)+1`. -/
def pointwiseBoundaryCutoff (m : ℕ) : ℕ :=
  2 * m * (m - 1) + 1

/-- At arrival index `N=n+j`, the normalized arrival coefficient dominates the
shifted positive density up to the literal factor `m-1`. -/
theorem positiveTiltedDensity_le_factor_mul_arrivalCoeff
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (n j : ℕ) :
    positiveTiltedDensity m (orbit m p₀ n) j ≤
      ((m : ℝ) - 1) * arrivalCoeff m p₀ n (n + j) := by
  have hncrit := orbit_critical m p₀ (by omega) hcrit n
  have hfactor : 0 ≤ (m : ℝ) - 1 :=
    (critical_tiltFactor_pos m (orbit m p₀ n) (by omega) hncrit).le
  have hq : 0 ≤ normalizedTilt m (orbit m p₀ n) (j + 1) :=
    normalizedTilt_nonneg m (orbit m p₀ n) (by omega) hncrit (j + 1)
  have hCpos : 0 < arrivalProduct m p₀ n :=
    transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint n
  have hCle : arrivalProduct m p₀ n ≤ 1 := by
    simpa only [arrivalProduct, transportProduct_zero] using
      (antitone_transportProduct m p₀ (by omega) hcrit (Nat.zero_le n))
  rw [positiveTiltedDensity_apply,
    arrivalCoeff_eq_of_le m p₀ n (n + j) (by omega)]
  have hindex : n + j - n + 1 = j + 1 := by omega
  rw [hindex]
  simp only [orbitTilt]
  apply mul_le_mul_of_nonneg_left _ hfactor
  rw [le_div_iff₀ hCpos]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hCle hq

/-- Source-shaped completion of `prop:pointwise`.  The sole upstream analytic
premise is the far-arrival estimate beyond `K_m`; H1a/H1b provide weighted mass.
The finite boundary offsets and all small generations are discharged here. -/
theorem positiveTiltedDensity_pointwise_of_arrival_far
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (hProduct : CDHLSProductFact m p₀ hm hcrit hnonconstant)
    (B : ℝ) (hB : 0 ≤ B)
    (hfar : ∀ n j : ℕ, pointwiseBoundaryCutoff m < j →
      ((n + j + 1 : ℕ) : ℝ) ^ 3 * arrivalCoeff m p₀ n (n + j) ≤
        B * ((n + 1 : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j : ℕ,
      positiveTiltedDensity m (orbit m p₀ n) j ≤
        C * ((n + 1 : ℕ) : ℝ) / ((n + j + 1 : ℕ) : ℝ) ^ 3 := by
  rcases positiveTiltedDensity_weightedMass_orbit
      m p₀ hm hcrit hthird hnonconstant hExcess hProduct with
    ⟨A, hA, hL1, _hfirst⟩
  have hfactor : 0 ≤ (m : ℝ) - 1 := by
    have hmReal : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hfarDensity : ∀ n j : ℕ, pointwiseBoundaryCutoff m < j →
      ((n + j + 1 : ℕ) : ℝ) ^ 3 *
          positiveTiltedDensity m (orbit m p₀ n) j ≤
        (((m : ℝ) - 1) * B) * ((n + 1 : ℕ) : ℝ) := by
    intro n j hj
    have hdensity := positiveTiltedDensity_le_factor_mul_arrivalCoeff
      m p₀ hm hcrit hnotBinaryFixedPoint n j
    have hscale : 0 ≤ ((n + j + 1 : ℕ) : ℝ) ^ 3 := by positivity
    calc
      ((n + j + 1 : ℕ) : ℝ) ^ 3 *
          positiveTiltedDensity m (orbit m p₀ n) j ≤
          ((n + j + 1 : ℕ) : ℝ) ^ 3 *
            (((m : ℝ) - 1) * arrivalCoeff m p₀ n (n + j)) :=
        mul_le_mul_of_nonneg_left hdensity hscale
      _ = ((m : ℝ) - 1) *
          (((n + j + 1 : ℕ) : ℝ) ^ 3 *
            arrivalCoeff m p₀ n (n + j)) := by ring
      _ ≤ ((m : ℝ) - 1) * (B * ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hfar n j hj) hfactor
      _ = (((m : ℝ) - 1) * B) * ((n + 1 : ℕ) : ℝ) := by ring
  exact positiveTiltedDensity_pointwise_of_far_and_weightedL1
    m p₀ hm hcrit hthird A (((m : ℝ) - 1) * B) hA.le
      (mul_nonneg hfactor hB) hL1 (pointwiseBoundaryCutoff m) hfarDensity

end

end DerridaRetaux
