import DerridaRetaux.Basic.Sequence
import Mathlib.Tactic

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace DerridaRetaux

noncomputable section

/-!
# Cubic coefficient tails

This file isolates the elementary implication used at `U24`: for a nonnegative
coefficient sequence, finiteness of the third weighted moment forces both the
individual cubic coefficient and the cubically rescaled coefficient tail to
vanish.  No probabilistic or external input is involved.
-/

/-- The ordinary coefficient tail beginning at `N`. -/
def coefficientTail (a : Seq) (N : ℕ) : ℝ :=
  ∑' k : ℕ, a (k + N)

/-- The tail of the third weighted coefficient sequence beginning at `N`. -/
def cubicMomentTail (a : Seq) (N : ℕ) : ℝ :=
  ∑' k : ℕ, ((k + N : ℕ) : ℝ) ^ 3 * a (k + N)

/-- A nonnegative sequence with finite third weighted moment is summable.  The
index zero is harmless and the comparison starts at index one. -/
theorem summable_of_summable_nat_cube
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Summable a := by
  have hthreeShift :
      Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ 3 * a (k + 1)) :=
    (summable_nat_add_iff 1).2 hthree
  have haShift : Summable (fun k : ℕ ↦ a (k + 1)) := by
    apply Summable.of_nonneg_of_le
      (f := fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ 3 * a (k + 1))
    · exact fun k ↦ ha (k + 1)
    · intro k
      have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
      have hak : 0 ≤ a (k + 1) := ha (k + 1)
      have hpow : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hk
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hak
    · exact hthreeShift
  exact (summable_nat_add_iff 1).1 haShift

/-- The individual cubic coefficient tends to zero. -/
theorem nat_cube_mul_tendsto_zero
    (a : Seq) (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n) atTop (𝓝 0) :=
  hthree.tendsto_atTop_zero

/-- The cubically rescaled ordinary tail is bounded by the tail of the third
weighted sequence. -/
theorem nat_cube_mul_coefficientTail_le_cubicMomentTail
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) (N : ℕ) :
    (N : ℝ) ^ 3 * coefficientTail a N ≤ cubicMomentTail a N := by
  have hsumA : Summable a := summable_of_summable_nat_cube a ha hthree
  have htailA : Summable (fun k : ℕ ↦ a (k + N)) :=
    (summable_nat_add_iff N).2 hsumA
  have htailThree :
      Summable (fun k : ℕ ↦ ((k + N : ℕ) : ℝ) ^ 3 * a (k + N)) :=
    (summable_nat_add_iff N).2 hthree
  have hleft : Summable (fun k : ℕ ↦ (N : ℝ) ^ 3 * a (k + N)) :=
    htailA.mul_left ((N : ℝ) ^ 3)
  rw [coefficientTail, cubicMomentTail, ← htailA.tsum_mul_left]
  apply Summable.tsum_le_tsum _ hleft htailThree
  intro k
  have hpow : (N : ℝ) ^ 3 ≤ ((k + N : ℕ) : ℝ) ^ 3 := by
    gcongr
    exact_mod_cast (show N ≤ k + N by omega)
  exact mul_le_mul_of_nonneg_right hpow (ha (k + N))

/-- The tail of the summable third weighted sequence tends to zero. -/
theorem cubicMomentTail_tendsto_zero
    (a : Seq) (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Tendsto (cubicMomentTail a) atTop (𝓝 0) := by
  let f : Seq := fun n : ℕ ↦ (n : ℝ) ^ 3 * a n
  have hprefix :
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, f n) atTop (𝓝 (∑' n, f n)) :=
    hthree.hasSum.tendsto_sum_nat
  have htailEq : ∀ N : ℕ,
      cubicMomentTail a N = (∑' n, f n) - ∑ n ∈ Finset.range N, f n := by
    intro N
    rw [cubicMomentTail]
    change (∑' k : ℕ, f (k + N)) = _
    rw [← hthree.sum_add_tsum_nat_add N]
    ring
  have hdiff :
      Tendsto
        (fun N : ℕ ↦ (∑' n, f n) - ∑ n ∈ Finset.range N, f n)
        atTop (𝓝 0) := by
    simpa only [sub_self] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ ∑' n, f n) atTop (𝓝 (∑' n, f n))).sub hprefix)
  exact Tendsto.congr' (Eventually.of_forall fun N ↦ (htailEq N).symm) hdiff

/-- Finite nonnegative third moment implies the cubic coefficient-tail limit
required in the far-arrival initialization. -/
theorem nat_cube_mul_coefficientTail_tendsto_zero
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) ^ 3 * coefficientTail a N) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro N
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg N) 3)
      (tsum_nonneg fun k ↦ ha (k + N))
  · intro N
    exact nat_cube_mul_coefficientTail_le_cubicMomentTail a ha hthree N
  · exact cubicMomentTail_tendsto_zero a hthree

/-- Both coefficient-tail limits used in `U24`, packaged together. -/
theorem finiteThirdMoment_implies_cubic_tail_limits
    (a : Seq) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hthree : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 3 * a n) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ ↦ (N : ℝ) ^ 3 * coefficientTail a N) atTop (𝓝 0) :=
  ⟨nat_cube_mul_tendsto_zero a hthree,
    nat_cube_mul_coefficientTail_tendsto_zero a ha hthree⟩

end

end DerridaRetaux
