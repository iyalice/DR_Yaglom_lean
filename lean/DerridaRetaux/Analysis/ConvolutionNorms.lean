import DerridaRetaux.Analysis.WeightedNorm
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Weighted convolution-power bounds

This file lifts the cubic weighted Young inequality to all fixed convolution
powers and supplies the mixed weighted-supremum/weighted-`l1` estimate used in
`eq:convnorms`.
-/

@[simp]
theorem weightedAbs_diracSeq_zero (L : ℝ) :
    weightedAbs L (diracSeq 0) = diracSeq 0 := by
  funext n
  cases n <;> simp [weightedAbs, cubicWeight, diracSeq]

theorem weightedAbs_diracSeq_zero_summable (L : ℝ) :
    Summable (weightedAbs L (diracSeq 0)) := by
  rw [weightedAbs_diracSeq_zero]
  simpa only [diracSeq] using (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable

@[simp]
theorem weightedL1Three_diracSeq_zero (L : ℝ) :
    weightedL1Three L (diracSeq 0) = 1 := by
  rw [weightedL1Three_eq_tsum_weightedAbs, weightedAbs_diracSeq_zero]
  simp [diracSeq]

theorem weightedL1Three_nonneg (L : ℝ) (hL : 0 < L) (a : Seq) :
    0 ≤ weightedL1Three L a := by
  rw [weightedL1Three_eq_tsum_weightedAbs]
  exact tsum_nonneg (weightedAbs_nonneg L hL a)

/-- Absolute cubic weights of a convolution are summable whenever those of both
factors are summable. -/
theorem weightedAbs_conv_summable
    (L : ℝ) (hL : 1 ≤ L) (a b : Seq)
    (ha : Summable (weightedAbs L a)) (hb : Summable (weightedAbs L b)) :
    Summable (weightedAbs L (conv a b)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  apply Summable.of_nonneg_of_le
    (f := conv (weightedAbs L a) (weightedAbs L b))
  · exact weightedAbs_nonneg L hLpos (conv a b)
  · exact weightedAbs_conv_le_conv L hL a b
  · exact conv_summable (weightedAbs L a) (weightedAbs L b) ha hb

/-- Every fixed convolution power retains finite cubic weighted `l1` mass. -/
theorem weightedAbs_convPow_summable
    (L : ℝ) (hL : 1 ≤ L) (a : Seq)
    (ha : Summable (weightedAbs L a)) (r : ℕ) :
    Summable (weightedAbs L (convPow r a)) := by
  induction r with
  | zero => simpa using weightedAbs_diracSeq_zero_summable L
  | succ r ih =>
      simpa only [convPow_succ] using weightedAbs_conv_summable L hL (convPow r a) a ih ha

/-- Cubic weighted `l1` Young inequality for every convolution power. -/
theorem weightedL1Three_convPow_le_pow
    (L : ℝ) (hL : 1 ≤ L) (a : Seq)
    (ha : Summable (weightedAbs L a)) (r : ℕ) :
    weightedL1Three L (convPow r a) ≤ weightedL1Three L a ^ r := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hmass : 0 ≤ weightedL1Three L a := weightedL1Three_nonneg L hLpos a
  induction r with
  | zero => simp
  | succ r ih =>
      rw [convPow_succ, pow_succ]
      calc
        weightedL1Three L (conv (convPow r a) a) ≤
            weightedL1Three L (convPow r a) * weightedL1Three L a :=
          weightedL1Three_conv_le L hL (convPow r a) a
            (weightedAbs_convPow_summable L hL a ha r) ha
        _ ≤ weightedL1Three L a ^ r * weightedL1Three L a :=
          mul_le_mul_of_nonneg_right ih hmass

/-- Mixed Young inequality: a weighted pointwise supremum on the first factor
and weighted `l1` mass on the second control the convolution supremum. -/
theorem weightedSupThree_conv_le
    (L A : ℝ) (hL : 1 ≤ L) (hA : 0 ≤ A) (a b : Seq)
    (ha : WeightedSupThreeLE L a A)
    (hb : Summable (weightedAbs L b)) :
    WeightedSupThreeLE L (conv a b) (A * weightedL1Three L b) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro n
  change weightedAbs L (conv a b) n ≤ A * weightedL1Three L b
  calc
    weightedAbs L (conv a b) n ≤
        conv (weightedAbs L a) (weightedAbs L b) n :=
      weightedAbs_conv_le_conv L hL a b n
    _ = ∑ k ∈ Finset.range (n + 1),
        weightedAbs L a k * weightedAbs L b (n - k) := rfl
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        A * weightedAbs L b (n - k) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact mul_le_mul_of_nonneg_right (ha k) (weightedAbs_nonneg L hLpos b (n - k))
    _ = A * ∑ k ∈ Finset.range (n + 1), weightedAbs L b (n - k) := by
      rw [Finset.mul_sum]
    _ = A * ∑ k ∈ Finset.range (n + 1), weightedAbs L b k := by
      congr 1
      simpa using Finset.sum_range_reflect (weightedAbs L b) (n + 1)
    _ ≤ A * ∑' k : ℕ, weightedAbs L b k := by
      exact mul_le_mul_of_nonneg_left
        (hb.sum_le_tsum (Finset.range (n + 1))
          (fun k _ ↦ weightedAbs_nonneg L hLpos b k)) hA
    _ = A * weightedL1Three L b := by
      rw [weightedL1Three_eq_tsum_weightedAbs]

/-- A source-shaped mixed bound for positive convolution powers. -/
theorem weightedSupThree_convPow_succ_le
    (L A : ℝ) (hL : 1 ≤ L) (hA : 0 ≤ A) (a : Seq)
    (haSup : WeightedSupThreeLE L a A)
    (haSum : Summable (weightedAbs L a)) (r : ℕ) :
    WeightedSupThreeLE L (convPow (r + 1) a)
      (A * weightedL1Three L a ^ r) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hmass : 0 ≤ weightedL1Three L a := weightedL1Three_nonneg L hLpos a
  induction r with
  | zero => simpa using haSup
  | succ r ih =>
      rw [convPow_succ]
      have hconv := weightedSupThree_conv_le L
        (A * weightedL1Three L a ^ r) hL
        (mul_nonneg hA (pow_nonneg hmass r)) (convPow (r + 1) a) a ih haSum
      simpa only [pow_succ, mul_assoc] using hconv

end

end DerridaRetaux
