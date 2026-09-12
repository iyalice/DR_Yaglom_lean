import DerridaRetaux.Analysis.WeightedNorm
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Finite spatial telescoping

This file isolates the elementary full-shift identity
`f - S^h f = ∑ i < h, S^i (Δf)` and its cubic weighted supremum consequences.
It does not assert the logarithmically improved modulus `eq:spmod`, whose proof also
uses the early/late decomposition, and it does not address a truncated telescope.
-/

/-- The finite sum of the first `h` left shifts of a coefficient sequence. -/
def shiftLeftPartialSum (h : ℕ) (f : Seq) : Seq :=
  fun j ↦ ∑ i ∈ Finset.range h, (shiftLeft^[i]) f j

@[simp]
theorem shiftLeftPartialSum_apply (h : ℕ) (f : Seq) (j : ℕ) :
    shiftLeftPartialSum h f j = ∑ i ∈ Finset.range h, (shiftLeft^[i]) f j :=
  rfl

/-- Coefficientwise finite telescoping for the forward difference `Δ = I - S`. -/
theorem sub_shiftLeft_iterate_apply
    (f : Seq) (h j : ℕ) :
    f j - (shiftLeft^[h]) f j =
      shiftLeftPartialSum h (discreteDerivative f) j := by
  simp only [shiftLeftPartialSum_apply, shiftLeft_iterate_apply,
    discreteDerivative_apply]
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hindex : j + (h + 1) = j + h + 1 := by omega
      rw [hindex]
      ring

/-- Sequence-level form of `f - S^h f = ∑ i < h, S^i (Δf)`. -/
theorem sub_shiftLeft_iterate_eq_shiftLeftPartialSum
    (f : Seq) (h : ℕ) :
    f - (shiftLeft^[h]) f = shiftLeftPartialSum h (discreteDerivative f) := by
  funext j
  exact sub_shiftLeft_iterate_apply f h j

/-- Repeated left shifts preserve the same cubic weighted pointwise bound. -/
theorem weightedSupThree_shiftLeft_iterate
    (L C : ℝ) (h : ℕ) (hL : 0 < L) (f : Seq)
    (hf : WeightedSupThreeLE L f C) :
    WeightedSupThreeLE L ((shiftLeft^[h]) f) C := by
  induction h with
  | zero => simpa
  | succ h ih =>
      rw [Function.iterate_succ_apply']
      exact weightedSupThree_shiftLeft L C hL ((shiftLeft^[h]) f) ih

/-- The weighted full spatial difference is bounded by `h` times the weighted
bound on the discrete derivative. -/
theorem weightedSupThree_sub_shiftLeft_iterate
    (L C : ℝ) (h : ℕ) (hL : 0 < L) (f : Seq)
    (hdelta : WeightedSupThreeLE L (discreteDerivative f) C) :
    WeightedSupThreeLE L (f - (shiftLeft^[h]) f) ((h : ℝ) * C) := by
  intro j
  have hweight : 0 ≤ cubicWeight L j := cubicWeight_nonneg L hL j
  rw [Pi.sub_apply, sub_shiftLeft_iterate_apply]
  calc
    cubicWeight L j * |shiftLeftPartialSum h (discreteDerivative f) j| ≤
        cubicWeight L j *
          ∑ i ∈ Finset.range h, |(shiftLeft^[i]) (discreteDerivative f) j| := by
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hweight
    _ = ∑ i ∈ Finset.range h,
        cubicWeight L j * |(shiftLeft^[i]) (discreteDerivative f) j| := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range h, C := by
      apply Finset.sum_le_sum
      intro i hi
      exact weightedSupThree_shiftLeft_iterate L C i hL
        (discreteDerivative f) hdelta j
    _ = (h : ℝ) * C := by simp

/-- Taking one forward difference costs at most a factor two in the cubic
weighted pointwise supremum bound. -/
theorem weightedSupThree_discreteDerivative
    (L C : ℝ) (hL : 0 < L) (f : Seq)
    (hf : WeightedSupThreeLE L f C) :
    WeightedSupThreeLE L (discreteDerivative f) (2 * C) := by
  have hshift : WeightedSupThreeLE L (shiftLeft f) C :=
    weightedSupThree_shiftLeft L C hL f hf
  intro j
  have hweight : 0 ≤ cubicWeight L j := cubicWeight_nonneg L hL j
  calc
    cubicWeight L j * |discreteDerivative f j| =
        cubicWeight L j * |f j - shiftLeft f j| := by
      rw [discreteDerivative_apply, shiftLeft_apply]
    _ ≤ cubicWeight L j * (|f j| + |shiftLeft f j|) := by
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) hweight
    _ = cubicWeight L j * |f j| + cubicWeight L j * |shiftLeft f j| := by ring
    _ ≤ C + C := add_le_add (hf j) (hshift j)
    _ = 2 * C := by ring

end DerridaRetaux
