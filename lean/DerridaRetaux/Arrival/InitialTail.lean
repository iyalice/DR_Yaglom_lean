import DerridaRetaux.Arrival.ArrivalRecursion
import DerridaRetaux.Model.MomentPropagation
import DerridaRetaux.Prelim.FarTail
import Mathlib.Tactic

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace DerridaRetaux

noncomputable section

/-!
# Initial arrival tails

This file supplies the elementary `s = 0` input to the far-arrival estimate `U24`.
The paper's coefficient `φ₀,N` is `arrivalCoeff m p₀ 0 N`; `arrivalBoundary m p₀ 0`
is only the scalar `φ₀,0` and therefore is not itself an `N`-indexed tail.  The source
series `A₀` is represented literally by `arrivalFormulaSource m p₀ 0`.
-/

/-- A natural number is bounded by one plus its cube. -/
theorem natCast_le_one_add_cube (n : ℕ) :
    (n : ℝ) ≤ 1 + (n : ℝ) ^ 3 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hnonneg : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := le_trans (by norm_num) hone
      have hsquare : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
        calc
          ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) * 1 := by ring
          _ ≤ ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hone hnonneg
          _ = ((n + 1 : ℕ) : ℝ) ^ 2 := by ring
      have hcube : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := by
        calc
          ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) ^ 2 * 1 := by ring
          _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hone (sq_nonneg _)
          _ = ((n + 1 : ℕ) : ℝ) ^ 3 := by ring
      linarith

/-- The squared natural index is bounded by one plus its cube. -/
theorem natCast_square_le_one_add_cube (n : ℕ) :
    (n : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 3 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hcube : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := by
        calc
          ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) ^ 2 * 1 := by ring
          _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hone (sq_nonneg _)
          _ = ((n + 1 : ℕ) : ℝ) ^ 3 := by ring
      linarith

/-- For a nonnegative sequence, a finite cubic moment controls the first moment. -/
theorem summable_nat_mul_of_summable_nat_cube
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Summable (fun n : ℕ ↦ (n : ℝ) * a n) := by
  have hzero : Summable a := summable_of_summable_nat_cube a ha hthree
  have hmajor : Summable (fun n : ℕ ↦ a n + (n : ℝ) ^ 3 * a n) :=
    hzero.add hthree
  apply Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (Nat.cast_nonneg n) (ha n))
    ?_ hmajor
  intro n
  calc
    (n : ℝ) * a n ≤ (1 + (n : ℝ) ^ 3) * a n :=
      mul_le_mul_of_nonneg_right (natCast_le_one_add_cube n) (ha n)
    _ = a n + (n : ℝ) ^ 3 * a n := by ring

/-- For a nonnegative sequence, a finite cubic moment controls the second moment. -/
theorem summable_nat_square_mul_of_summable_nat_cube
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * a n) := by
  have hzero : Summable a := summable_of_summable_nat_cube a ha hthree
  have hmajor : Summable (fun n : ℕ ↦ a n + (n : ℝ) ^ 3 * a n) :=
    hzero.add hthree
  apply Summable.of_nonneg_of_le
    (fun n : ℕ ↦ mul_nonneg (sq_nonneg (n : ℝ)) (ha n))
    ?_ hmajor
  intro n
  calc
    (n : ℝ) ^ 2 * a n ≤ (1 + (n : ℝ) ^ 3) * a n :=
      mul_le_mul_of_nonneg_right (natCast_square_le_one_add_cube n) (ha n)
    _ = a n + (n : ℝ) ^ 3 * a n := by ring

/-- A finite convolution power preserves finiteness of the un-tilted cubic moment. -/
theorem convPow_cubic_summable
    (r : ℕ) (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * convPow r a n) := by
  have hzero : Summable (powerScale 1 a) := by
    change Summable (fun n : ℕ ↦ (1 : ℝ) ^ n * a n)
    simpa using summable_of_summable_nat_cube a ha hthree
  have hone : Summable (firstMomentScale 1 a) := by
    change Summable (fun n : ℕ ↦ (n : ℝ) * (1 : ℝ) ^ n * a n)
    simpa using summable_nat_mul_of_summable_nat_cube a ha hthree
  have htwo : Summable (secondMomentScale 1 a) := by
    change Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 : ℝ) ^ n * a n)
    simpa using
      summable_nat_square_mul_of_summable_nat_cube a ha hthree
  have hthreeScale : Summable (thirdMomentScale 1 a) := by
    change Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * (1 : ℝ) ^ n * a n)
    simpa using hthree
  have hout :=
    (momentScales_convPow_summable r 1 a hzero hone htwo hthreeScale).2.2.2
  change Summable
    (fun n : ℕ ↦ (n : ℝ) ^ 3 * (1 : ℝ) ^ n * convPow r a n) at hout
  simpa using hout

/-- Removing a fixed initial block preserves a finite cubic moment. -/
theorem natAdd_cubic_summable
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) (d : ℕ) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a (n + d)) := by
  have htail :
      Summable (fun n : ℕ ↦ ((n + d : ℕ) : ℝ) ^ 3 * a (n + d)) :=
    (summable_nat_add_iff d).2 hthree
  apply Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (pow_nonneg (Nat.cast_nonneg n) 3) (ha (n + d)))
    ?_ htail
  intro n
  have hpow : (n : ℝ) ^ 3 ≤ ((n + d : ℕ) : ℝ) ^ 3 := by
    gcongr
    exact_mod_cast (show n ≤ n + d by omega)
  exact mul_le_mul_of_nonneg_right hpow (ha (n + d))

/-- A fixed nonnegative integer coefficient shift preserves a finite cubic moment. -/
theorem shiftByInt_ofNat_cubic_summable
    (d : ℕ) (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * shiftByInt (d : ℤ) a n) := by
  have hzero : Summable a := summable_of_summable_nat_cube a ha hthree
  have hone := summable_nat_mul_of_summable_nat_cube a ha hthree
  have htwo := summable_nat_square_mul_of_summable_nat_cube a ha hthree
  have htranslated :
      Summable (fun n : ℕ ↦ ((n + d : ℕ) : ℝ) ^ 3 * a n) := by
    convert (((hthree.add (htwo.mul_left (3 * (d : ℝ)))).add
      (hone.mul_left (3 * (d : ℝ) ^ 2))).add
        (hzero.mul_left ((d : ℝ) ^ 3))) using 1
    funext n
    simp only [Nat.cast_add]
    ring
  apply (summable_nat_add_iff d).1
  convert htranslated using 1
  funext n
  rw [shiftByInt_of_le d (n + d) a (by omega)]
  congr 2
  omega

/-- Finite coefficientwise sums preserve cubic summability. -/
theorem finsetSum_cubic_summable
    {ι : Type*} (s : Finset ι) (a : ι → Seq)
    (ha : ∀ i ∈ s, Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a i n)) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * ∑ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  | @insert i s hi ih =>
      have hiSummable := ha i (by simp)
      have hsSummable := ih (fun j hj ↦ ha j (by simp [hj]))
      simpa [Finset.sum_insert hi, mul_add] using hiSummable.add hsSummable

/-- The literal initial source `A₀` has a finite cubic moment whenever the initial
arrival coefficients do.  This is exactly the finite-convolution observation used
in the proof of `prop:far`. -/
theorem arrivalFormulaSource_zero_cubic_summable
    (m : ℕ) (p₀ : ProbabilityMass)
    (hphiNonneg : ∀ N : ℕ, 0 ≤ arrivalCoeff m p₀ 0 N)
    (hphiThree :
      Summable (fun N : ℕ ↦ (N : ℝ) ^ 3 * arrivalCoeff m p₀ 0 N)) :
    Summable
      (fun N : ℕ ↦ (N : ℝ) ^ 3 * arrivalFormulaSource m p₀ 0 N) := by
  simp only [arrivalFormulaSource]
  apply finsetSum_cubic_summable
  intro r hr
  have hrTwo : 2 ≤ r := (Finset.mem_Icc.mp hr).1
  have hpower := convPow_cubic_summable r (arrivalCoeff m p₀ 0) hphiNonneg hphiThree
  have hshift := shiftByInt_ofNat_cubic_summable (r - 2)
    (convPow r (arrivalCoeff m p₀ 0))
    (convPow_nonneg r (arrivalCoeff m p₀ 0) hphiNonneg) hpower
  norm_num only [Nat.cast_zero, sub_zero, mul_one]
  rw [show (r : ℤ) - 2 = ((r - 2 : ℕ) : ℤ) by omega]
  convert hshift.mul_left (arrivalAlpha m p₀ 0 r) using 1
  funext N
  ring

/-- At generation zero, the boundary is the single coefficient `φ₀,0 = q₀,1`.
It is not an `N`-dependent tail. -/
theorem arrivalBoundary_zero_eq_positiveTilt_one
    (m : ℕ) (p₀ : ProbabilityMass) :
    arrivalBoundary m p₀ 0 = orbitPositiveTilt m p₀ 0 1 := by
  simp [arrivalBoundary, orbitPositiveTilt]

/-- The paper's initial coefficient array inherits cubic summability from the
positive normalized tilted density. -/
theorem arrivalCoeff_zero_cubic_summable_of_positiveTilt
    (m : ℕ) (p₀ : ProbabilityMass)
    (hqNonneg : ∀ k : ℕ, 0 ≤ orbitPositiveTilt m p₀ 0 k)
    (hqThree :
      Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * orbitPositiveTilt m p₀ 0 k)) :
    Summable (fun N : ℕ ↦ (N : ℝ) ^ 3 * arrivalCoeff m p₀ 0 N) := by
  have hshift := natAdd_cubic_summable (orbitPositiveTilt m p₀ 0) hqNonneg hqThree 1
  simpa only [arrivalCoeff_zero_generation, orbitPositiveTilt, removeZeroCoeff_succ]
    using hshift

/-- Pointwise nonnegativity likewise transfers from the positive tilted density
to the initial arrival coefficients. -/
theorem arrivalCoeff_zero_nonneg_of_positiveTilt
    (m : ℕ) (p₀ : ProbabilityMass)
    (hqNonneg : ∀ k : ℕ, 0 ≤ orbitPositiveTilt m p₀ 0 k) (N : ℕ) :
    0 ≤ arrivalCoeff m p₀ 0 N := by
  simpa only [arrivalCoeff_zero_generation, orbitPositiveTilt, removeZeroCoeff_succ]
    using hqNonneg (N + 1)

/-- The ordinary tail of a summable sequence tends to zero. -/
theorem coefficientTail_tendsto_zero_of_summable
    (a : Seq) (ha : Summable a) :
    Tendsto (coefficientTail a) atTop (𝓝 0) := by
  have hprefix :
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, a n) atTop (𝓝 (∑' n, a n)) :=
    ha.hasSum.tendsto_sum_nat
  have htailEq : ∀ N : ℕ,
      coefficientTail a N = (∑' n, a n) - ∑ n ∈ Finset.range N, a n := by
    intro N
    rw [coefficientTail]
    rw [← ha.sum_add_tsum_nat_add N]
    ring
  have hdiff :
      Tendsto
        (fun N : ℕ ↦ (∑' n, a n) - ∑ n ∈ Finset.range N, a n)
        atTop (𝓝 0) := by
    simpa only [sub_self] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ ∑' n, a n) atTop (𝓝 (∑' n, a n))).sub hprefix)
  exact Tendsto.congr' (Eventually.of_forall fun N ↦ (htailEq N).symm) hdiff

/-- Uniform polynomial comparison used to replace a tail at `N` by the paper's
tail at `N - 1`. -/
theorem natSucc_cube_le_eight_mul_cube_add_one (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) ^ 3) ≤ 8 * ((n : ℝ) ^ 3 + 1) := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hlin :
          (((n + 1 : ℕ) + 1 : ℕ) : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show (n + 1) + 1 ≤ 2 * (n + 1) by omega)
      calc
        (((n + 1 : ℕ) + 1 : ℕ) : ℝ) ^ 3 ≤
            (2 * ((n + 1 : ℕ) : ℝ)) ^ 3 := by
          gcongr
        _ = 8 * ((n + 1 : ℕ) : ℝ) ^ 3 := by ring

        _ ≤ 8 * (((n + 1 : ℕ) : ℝ) ^ 3 + 1) := by linarith

/-- The `N - 1` version of the cubic tail limit used verbatim in `prop:far`. -/
theorem nat_cube_mul_coefficientTail_natPred_tendsto_zero
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Tendsto
      (fun N : ℕ ↦ (N : ℝ) ^ 3 * coefficientTail a (N - 1))
      atTop (𝓝 0) := by
  have hsum : Summable a := summable_of_summable_nat_cube a ha hthree
  have hcubic := nat_cube_mul_coefficientTail_tendsto_zero a ha hthree
  have htail := coefficientTail_tendsto_zero_of_summable a hsum
  have hmajor :
      Tendsto
        (fun n : ℕ ↦
          8 * ((n : ℝ) ^ 3 * coefficientTail a n + coefficientTail a n))
        atTop (𝓝 0) := by
    have hadd := hcubic.add htail
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (8 : ℝ)) atTop (𝓝 8)).mul hadd)
  have hshifted :
      Tendsto
        (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ 3 * coefficientTail a n)
        atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
        (tsum_nonneg fun k ↦ ha (k + n))
    · intro n
      have htailNonneg : 0 ≤ coefficientTail a n :=
        tsum_nonneg fun k ↦ ha (k + n)
      calc
        ((n + 1 : ℕ) : ℝ) ^ 3 * coefficientTail a n ≤
            (8 * ((n : ℝ) ^ 3 + 1)) * coefficientTail a n :=
          mul_le_mul_of_nonneg_right
            (natSucc_cube_le_eight_mul_cube_add_one n) htailNonneg
        _ = 8 * ((n : ℝ) ^ 3 * coefficientTail a n + coefficientTail a n) := by
          ring
    · exact hmajor
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  simpa using hshifted

/-- The manuscript third tilted moment implies the cubic summability of the
initial positive normalized tilted density. -/
theorem orbitPositiveTilt_zero_cubic_summable_of_tiltSummable
    (m : ℕ) (p₀ : ProbabilityMass) (hthird : TiltSummable m 3 p₀) :
    Summable
      (fun k : ℕ ↦ (k : ℝ) ^ 3 * orbitPositiveTilt m p₀ 0 k) := by
  have hnormalized :
      Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * normalizedTilt m p₀ k) := by
    simpa only [normalizedTilt, div_eq_mul_inv, mul_assoc] using
      hthird.div_const (tiltedPartition m p₀)
  convert hnormalized using 1
  funext k
  cases k <;> simp [orbitPositiveTilt, orbitTilt]

/-- Abstract initial single-coefficient limit, stated directly for the positive
tilted density used by the arrival coordinates. -/
theorem initialArrivalCoeff_cubic_tendsto_zero_of_positiveTilt
    (m : ℕ) (p₀ : ProbabilityMass)
    (hqNonneg : ∀ k : ℕ, 0 ≤ orbitPositiveTilt m p₀ 0 k)
    (hqThree :
      Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * orbitPositiveTilt m p₀ 0 k)) :
    Tendsto
      (fun N : ℕ ↦ (N : ℝ) ^ 3 * arrivalCoeff m p₀ 0 N)
      atTop (𝓝 0) := by
  exact nat_cube_mul_tendsto_zero (arrivalCoeff m p₀ 0)
    (arrivalCoeff_zero_cubic_summable_of_positiveTilt m p₀ hqNonneg hqThree)

/-- Abstract initial `A₀` tail limit, with the standard tail beginning at `N`. -/
theorem initialArrivalFormulaSource_cubic_tail_tendsto_zero_of_positiveTilt
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (hqNonneg : ∀ k : ℕ, 0 ≤ orbitPositiveTilt m p₀ 0 k)
    (hqThree :
      Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * orbitPositiveTilt m p₀ 0 k)) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ) ^ 3 * coefficientTail (arrivalFormulaSource m p₀ 0) N)
      atTop (𝓝 0) := by
  have hphiNonneg := arrivalCoeff_zero_nonneg_of_positiveTilt m p₀ hqNonneg
  have hphiThree :=
    arrivalCoeff_zero_cubic_summable_of_positiveTilt m p₀ hqNonneg hqThree
  exact nat_cube_mul_coefficientTail_tendsto_zero
    (arrivalFormulaSource m p₀ 0)
    (arrivalFormulaSource_nonneg m p₀ hm hcrit hnotBinaryFixedPoint 0)
    (arrivalFormulaSource_zero_cubic_summable m p₀ hphiNonneg hphiThree)

/-- Abstract initial `A₀` tail limit in the exact `N - 1` indexing of `prop:far`. -/
theorem initialArrivalFormulaSource_cubic_natPred_tail_tendsto_zero_of_positiveTilt
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (hqNonneg : ∀ k : ℕ, 0 ≤ orbitPositiveTilt m p₀ 0 k)
    (hqThree :
      Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * orbitPositiveTilt m p₀ 0 k)) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ) ^ 3 * coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1))
      atTop (𝓝 0) := by
  have hphiNonneg := arrivalCoeff_zero_nonneg_of_positiveTilt m p₀ hqNonneg
  have hphiThree :=
    arrivalCoeff_zero_cubic_summable_of_positiveTilt m p₀ hqNonneg hqThree
  exact nat_cube_mul_coefficientTail_natPred_tendsto_zero
    (arrivalFormulaSource m p₀ 0)
    (arrivalFormulaSource_nonneg m p₀ hm hcrit hnotBinaryFixedPoint 0)
    (arrivalFormulaSource_zero_cubic_summable m p₀ hphiNonneg hphiThree)

/-- The complete initial `U24` quantity under direct hypotheses on the positive
tilted density. -/
theorem initialArrivalU24_tendsto_zero_of_positiveTilt
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (hqNonneg : ∀ k : ℕ, 0 ≤ orbitPositiveTilt m p₀ 0 k)
    (hqThree :
      Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * orbitPositiveTilt m p₀ 0 k)) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ) ^ 3 *
          (arrivalCoeff m p₀ 0 N +
            coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1)))
      atTop (𝓝 0) := by
  have hcoeff :=
    initialArrivalCoeff_cubic_tendsto_zero_of_positiveTilt m p₀ hqNonneg hqThree
  have htail :=
    initialArrivalFormulaSource_cubic_natPred_tail_tendsto_zero_of_positiveTilt
      m p₀ hm hcrit hnotBinaryFixedPoint hqNonneg hqThree
  simpa only [mul_add, add_zero] using hcoeff.add htail

/-- Source-shaped `s = 0` far-arrival initialization from the manuscript's
criticality and finite third tilted moment assumptions. -/
theorem initialArrival_tail_limits
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (hthird : TiltSummable m 3 p₀) :
    Tendsto
        (fun N : ℕ ↦ (N : ℝ) ^ 3 * arrivalCoeff m p₀ 0 N)
        atTop (𝓝 0) ∧
      Tendsto
        (fun N : ℕ ↦
          (N : ℝ) ^ 3 * coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1))
        atTop (𝓝 0) := by
  have hqNonneg := orbitPositiveTilt_nonneg m p₀ (by omega) hcrit 0
  have hqThree := orbitPositiveTilt_zero_cubic_summable_of_tiltSummable m p₀ hthird
  exact ⟨initialArrivalCoeff_cubic_tendsto_zero_of_positiveTilt
      m p₀ hqNonneg hqThree,
    initialArrivalFormulaSource_cubic_natPred_tail_tendsto_zero_of_positiveTilt
      m p₀ hm hcrit hnotBinaryFixedPoint hqNonneg hqThree⟩

/-- The exact initial `ω(N)` expression from `prop:far` tends to zero. -/
theorem initialArrivalU24_tendsto_zero
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    (hthird : TiltSummable m 3 p₀) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ) ^ 3 *
          (arrivalCoeff m p₀ 0 N +
            coefficientTail (arrivalFormulaSource m p₀ 0) (N - 1)))
      atTop (𝓝 0) := by
  have hqNonneg := orbitPositiveTilt_nonneg m p₀ (by omega) hcrit 0
  have hqThree := orbitPositiveTilt_zero_cubic_summable_of_tiltSummable m p₀ hthird
  exact initialArrivalU24_tendsto_zero_of_positiveTilt
    m p₀ hm hcrit hnotBinaryFixedPoint hqNonneg hqThree

end

end DerridaRetaux
