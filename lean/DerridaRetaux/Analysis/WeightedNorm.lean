import DerridaRetaux.Arrival.IntegerShift
import DerridaRetaux.Basic.Convolution
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Cubic weighted sequence estimates

These are the reusable deterministic inequalities from the smoothing preliminaries
(`U28`).  Supremum estimates use the pointwise predicate `WeightedSupThreeLE` fixed in
`Basic.Sequence`; no conditionally complete infinite supremum is introduced.
-/

/-- The summand whose total is `weightedL1Three`. -/
def weightedAbs (L : ℝ) (f : Seq) : Seq :=
  fun j ↦ cubicWeight L j * |f j|

theorem cubicWeight_nonneg (L : ℝ) (hL : 0 < L) (j : ℕ) : 0 ≤ cubicWeight L j := by
  unfold cubicWeight
  positivity

theorem cubicWeight_pos (L : ℝ) (hL : 0 < L) (j : ℕ) : 0 < cubicWeight L j := by
  unfold cubicWeight
  positivity

/-- The cubic weight is increasing in its index when `L>0`. -/
theorem cubicWeight_mono (L : ℝ) (hL : 0 < L) {i j : ℕ} (hij : i ≤ j) :
    cubicWeight L i ≤ cubicWeight L j := by
  unfold cubicWeight
  gcongr

/-- The source weight is submultiplicative under addition of indices. -/
theorem cubicWeight_add_le_mul (L : ℝ) (hL : 1 ≤ L) (i j : ℕ) :
    cubicWeight L (i + j) ≤ cubicWeight L i * cubicWeight L j := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hi : 0 ≤ (i : ℝ) / L := div_nonneg (Nat.cast_nonneg i) hLpos.le
  have hj : 0 ≤ (j : ℝ) / L := div_nonneg (Nat.cast_nonneg j) hLpos.le
  have hcross : 0 ≤ ((i : ℝ) / L) * ((j : ℝ) / L) := mul_nonneg hi hj
  have hbase :
      1 + ((i + j : ℕ) : ℝ) / L ≤
        (1 + (i : ℝ) / L) * (1 + (j : ℝ) / L) := by
    calc
      1 + ((i + j : ℕ) : ℝ) / L =
          1 + (i : ℝ) / L + (j : ℝ) / L := by
        push_cast
        ring
      _ ≤ 1 + (i : ℝ) / L + (j : ℝ) / L +
          ((i : ℝ) / L) * ((j : ℝ) / L) := le_add_of_nonneg_right hcross
      _ = (1 + (i : ℝ) / L) * (1 + (j : ℝ) / L) := by ring
  unfold cubicWeight
  calc
    (1 + ((i + j : ℕ) : ℝ) / L) ^ 3 ≤
        ((1 + (i : ℝ) / L) * (1 + (j : ℝ) / L)) ^ 3 := by gcongr
    _ = (1 + (i : ℝ) / L) ^ 3 * (1 + (j : ℝ) / L) ^ 3 := by ring

theorem weightedAbs_nonneg (L : ℝ) (hL : 0 < L) (f : Seq) (j : ℕ) :
    0 ≤ weightedAbs L f j :=
  mul_nonneg (cubicWeight_nonneg L hL j) (abs_nonneg _)

@[simp]
theorem weightedL1Three_eq_tsum_weightedAbs (L : ℝ) (f : Seq) :
    weightedL1Three L f = ∑' j : ℕ, weightedAbs L f j :=
  rfl

/-- Coefficientwise weighted domination of a convolution by the convolution of the
weighted absolute-value sequences. -/
theorem weightedAbs_conv_le_conv
    (L : ℝ) (hL : 1 ≤ L) (a b : Seq) (n : ℕ) :
    weightedAbs L (conv a b) n ≤ conv (weightedAbs L a) (weightedAbs L b) n := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hw := cubicWeight_nonneg L hLpos n
  rw [weightedAbs, conv_apply, conv_apply]
  calc
    cubicWeight L n * |∑ k ∈ Finset.range (n + 1), a k * b (n - k)| ≤
        cubicWeight L n *
          ∑ k ∈ Finset.range (n + 1), |a k * b (n - k)| := by
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw
    _ = ∑ k ∈ Finset.range (n + 1),
        cubicWeight L n * |a k * b (n - k)| := by
      rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        weightedAbs L a k * weightedAbs L b (n - k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hadd : k + (n - k) = n := Nat.add_sub_of_le hkn
      have hweight := cubicWeight_add_le_mul L hL k (n - k)
      rw [hadd] at hweight
      rw [abs_mul, weightedAbs, weightedAbs]
      have habs : 0 ≤ |a k| * |b (n - k)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      calc
        cubicWeight L n * (|a k| * |b (n - k)|) ≤
            (cubicWeight L k * cubicWeight L (n - k)) *
              (|a k| * |b (n - k)|) :=
          mul_le_mul_of_nonneg_right hweight habs
        _ = (cubicWeight L k * |a k|) *
            (cubicWeight L (n - k) * |b (n - k)|) := by ring

/-- Cubic weighted Young inequality in `ℓ¹`. -/
theorem weightedL1Three_conv_le
    (L : ℝ) (hL : 1 ≤ L) (a b : Seq)
    (ha : Summable (weightedAbs L a)) (hb : Summable (weightedAbs L b)) :
    weightedL1Three L (conv a b) ≤
      weightedL1Three L a * weightedL1Three L b := by
  have hconv := conv_summable (weightedAbs L a) (weightedAbs L b) ha hb
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hleft : Summable (weightedAbs L (conv a b)) := by
    apply Summable.of_nonneg_of_le
      (f := conv (weightedAbs L a) (weightedAbs L b))
    · exact weightedAbs_nonneg L hLpos (conv a b)
    · exact weightedAbs_conv_le_conv L hL a b
    · exact hconv
  rw [weightedL1Three_eq_tsum_weightedAbs, weightedL1Three_eq_tsum_weightedAbs,
    weightedL1Three_eq_tsum_weightedAbs]
  calc
    (∑' n : ℕ, weightedAbs L (conv a b) n) ≤
        ∑' n : ℕ, conv (weightedAbs L a) (weightedAbs L b) n :=
      Summable.tsum_le_tsum (weightedAbs_conv_le_conv L hL a b) hleft hconv
    _ = (∑' k : ℕ, weightedAbs L a k) *
        ∑' k : ℕ, weightedAbs L b k := tsum_conv _ _ ha hb

/-- Left shift is a contraction for the weighted pointwise supremum predicate. -/
theorem weightedSupThree_shiftLeft
    (L C : ℝ) (hL : 0 < L) (f : Seq)
    (hf : WeightedSupThreeLE L f C) :
    WeightedSupThreeLE L (shiftLeft f) C := by
  intro j
  calc
    cubicWeight L j * |shiftLeft f j| ≤ cubicWeight L (j + 1) * |f (j + 1)| := by
      rw [shiftLeft_apply]
      exact mul_le_mul_of_nonneg_right (cubicWeight_mono L hL (Nat.le_succ j))
        (abs_nonneg _)
    _ ≤ C := hf (j + 1)

/-- Left shift is a contraction for the cubic weighted `ℓ¹` quantity. -/
theorem weightedL1Three_shiftLeft_le
    (L : ℝ) (hL : 0 < L) (f : Seq) (hf : Summable (weightedAbs L f)) :
    weightedL1Three L (shiftLeft f) ≤ weightedL1Three L f := by
  have htail : Summable (fun j : ℕ ↦ weightedAbs L f (j + 1)) :=
    (summable_nat_add_iff 1).2 hf
  have hshift : Summable (weightedAbs L (shiftLeft f)) := by
    apply Summable.of_nonneg_of_le (f := fun j : ℕ ↦ weightedAbs L f (j + 1))
    · exact weightedAbs_nonneg L hL (shiftLeft f)
    · intro j
      rw [weightedAbs, weightedAbs, shiftLeft_apply]
      exact mul_le_mul_of_nonneg_right (cubicWeight_mono L hL (Nat.le_succ j))
        (abs_nonneg _)
    · exact htail
  have htailLe :
      (∑' j : ℕ, weightedAbs L (shiftLeft f) j) ≤
        ∑' j : ℕ, weightedAbs L f (j + 1) := by
    apply Summable.tsum_le_tsum _ hshift htail
    intro j
    rw [weightedAbs, weightedAbs, shiftLeft_apply]
    exact mul_le_mul_of_nonneg_right (cubicWeight_mono L hL (Nat.le_succ j))
      (abs_nonneg _)
  rw [weightedL1Three_eq_tsum_weightedAbs, weightedL1Three_eq_tsum_weightedAbs]
  calc
    (∑' j : ℕ, weightedAbs L (shiftLeft f) j) ≤
        ∑' j : ℕ, weightedAbs L f (j + 1) := htailLe
    _ ≤ ∑' j : ℕ, weightedAbs L f j := by
      rw [hf.tsum_eq_zero_add]
      exact le_add_of_nonneg_left (weightedAbs_nonneg L hL f 0)

/-- A fixed positive coefficient shift has weighted pointwise norm at most
`(1+d)^3`, uniformly for every `L≥1`. -/
theorem weightedSupThree_shiftByInt_nat
    (L C : ℝ) (d : ℕ) (hL : 1 ≤ L) (hC : 0 ≤ C) (f : Seq)
    (hf : WeightedSupThreeLE L f C) :
    WeightedSupThreeLE L (shiftByInt (d : ℤ) f) (((1 + d : ℕ) : ℝ) ^ 3 * C) := by
  intro n
  by_cases hnd : n < d
  · rw [shiftByInt_eq_zero_of_lt d n f hnd, abs_zero, mul_zero]
    exact mul_nonneg (pow_nonneg (by positivity) 3) hC
  · have hdn : d ≤ n := Nat.le_of_not_gt hnd
    rw [shiftByInt_of_le d n f hdn]
    let j := n - d
    have hn : n = j + d := by
      dsimp [j]
      omega
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hj : 0 ≤ (j : ℝ) / L := div_nonneg (Nat.cast_nonneg j) hLpos.le
    have hddiv : (d : ℝ) / L ≤ (d : ℝ) := by
      apply (div_le_iff₀ hLpos).2
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg d))
    have hbase :
        1 + (n : ℝ) / L ≤
          ((1 + d : ℕ) : ℝ) * (1 + (j : ℝ) / L) := by
      have hcross : 0 ≤ (d : ℝ) * ((j : ℝ) / L) :=
        mul_nonneg (Nat.cast_nonneg d) hj
      rw [hn]
      calc
        1 + ((j + d : ℕ) : ℝ) / L =
            1 + (j : ℝ) / L + (d : ℝ) / L := by
          push_cast
          ring
        _ ≤ 1 + (j : ℝ) / L + (d : ℝ) := add_le_add_left hddiv _
        _ ≤ 1 + (j : ℝ) / L + (d : ℝ) + (d : ℝ) * ((j : ℝ) / L) :=
          le_add_of_nonneg_right hcross
        _ = ((1 + d : ℕ) : ℝ) * (1 + (j : ℝ) / L) := by
          push_cast
          ring
    have hweight :
        cubicWeight L n ≤ ((1 + d : ℕ) : ℝ) ^ 3 * cubicWeight L j := by
      unfold cubicWeight
      calc
        (1 + (n : ℝ) / L) ^ 3 ≤
            (((1 + d : ℕ) : ℝ) * (1 + (j : ℝ) / L)) ^ 3 := by gcongr
        _ = ((1 + d : ℕ) : ℝ) ^ 3 * (1 + (j : ℝ) / L) ^ 3 := by ring
    calc
      cubicWeight L n * |f (n - d)| = cubicWeight L n * |f j| := rfl
      _ ≤ (((1 + d : ℕ) : ℝ) ^ 3 * cubicWeight L j) * |f j| :=
        mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
      _ = ((1 + d : ℕ) : ℝ) ^ 3 * (cubicWeight L j * |f j|) := by ring
      _ ≤ ((1 + d : ℕ) : ℝ) ^ 3 * C := by
        exact mul_le_mul_of_nonneg_left (hf j) (pow_nonneg (by positivity) 3)

/-- Iterating the left shift moves a coefficient by the same natural amount. -/
@[simp]
theorem shiftLeft_iterate_apply (d : ℕ) (f : Seq) (j : ℕ) :
    (shiftLeft^[d]) f j = f (j + d) := by
  induction d generalizing f j with
  | zero => simp
  | succ d ih =>
      rw [Function.iterate_succ_apply, ih, shiftLeft_apply]
      congr 1

/-- Literal form of the source shift-gain estimate `eq:shiftgain`, with
`L_s=s+1` and `L_n=n+1`.  The constant `27` comes from cubing the exact
weight-ratio bound by `3`. -/
theorem weightedSupThree_shiftLeft_iterate_gain
    (s n d : ℕ) (C : ℝ) (hn : 2 ≤ n) (hd : n - 2 - s ≤ d) (f : Seq)
    (hf : WeightedSupThreeLE ((s + 1 : ℕ) : ℝ) f C) :
    WeightedSupThreeLE ((n + 1 : ℕ) : ℝ) ((shiftLeft^[d]) f)
      (27 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 3 * C) := by
  intro j
  have hLs : 0 < ((s + 1 : ℕ) : ℝ) := by positivity
  have hLn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcoreNat : n + 1 + j ≤ 3 * (s + 1 + j + d) := by omega
  have hcore :
      ((n + 1 + j : ℕ) : ℝ) ≤ 3 * ((s + 1 + j + d : ℕ) : ℝ) := by
    exact_mod_cast hcoreNat
  have hbase :
      1 + (j : ℝ) / ((n + 1 : ℕ) : ℝ) ≤
        3 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
          (1 + ((j + d : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ)) := by
    calc
      1 + (j : ℝ) / ((n + 1 : ℕ) : ℝ) =
          (((n + 1 + j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
        push_cast
        field_simp
      _ ≤ 3 * ((s + 1 + j + d : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
        (div_le_div_iff_of_pos_right hLn).2 hcore
      _ = 3 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
          (1 + ((j + d : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ)) := by
        push_cast
        field_simp
        ring
  have hbaseNonneg :
      0 ≤ 1 + (j : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
  have hweight :
      cubicWeight ((n + 1 : ℕ) : ℝ) j ≤
        27 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 3 *
          cubicWeight ((s + 1 : ℕ) : ℝ) (j + d) := by
    unfold cubicWeight
    calc
      (1 + (j : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 3 ≤
          (3 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
            (1 + ((j + d : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ))) ^ 3 := by
        exact pow_le_pow_left₀ hbaseNonneg hbase 3
      _ = 27 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 3 *
          (1 + ((j + d : ℕ) : ℝ) / ((s + 1 : ℕ) : ℝ)) ^ 3 := by ring
  rw [shiftLeft_iterate_apply]
  calc
    cubicWeight ((n + 1 : ℕ) : ℝ) j * |f (j + d)| ≤
        (27 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 3 *
          cubicWeight ((s + 1 : ℕ) : ℝ) (j + d)) * |f (j + d)| :=
      mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
    _ = 27 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 3 *
        (cubicWeight ((s + 1 : ℕ) : ℝ) (j + d) * |f (j + d)|) := by ring
    _ ≤ 27 * (((s + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ 3 * C := by
      exact mul_le_mul_of_nonneg_left (hf (j + d)) (by positivity)

end

end DerridaRetaux
