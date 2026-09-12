import DerridaRetaux.Spine.FactorialCauchy
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Finite-path positive-increment tail bound

This file isolates the deterministic telescope and weighted Markov argument in
`eq:sharptail`.  It applies to any countable-support path law once its one-step
positive increments have expectation at most four.
-/

def positivePathIncrement (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  max (u (i + 1) - u i) 0

def positivePathVariation (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, positivePathIncrement u i

def strictTailIndicator (R x : ℝ) : ℝ :=
  if R < x then 1 else 0

def weightedPathTail
    {Ω : Type*} (w : Ω → ℝ) (K : Ω → ℕ → ℝ) (n : ℕ) (R : ℝ) : ℝ :=
  ∑' ω, w ω * strictTailIndicator R (K ω n)

theorem positivePathVariation_nonneg (u : ℕ → ℝ) (n : ℕ) :
    0 ≤ positivePathVariation u n := by
  exact Finset.sum_nonneg fun i _ ↦ le_max_right _ _

theorem endpoint_sub_le_positivePathVariation (u : ℕ → ℝ) (n : ℕ) :
    u n - u 0 ≤ positivePathVariation u n := by
  induction n with
  | zero =>
      simp [positivePathVariation]
  | succ n ih =>
      rw [positivePathVariation, Finset.sum_range_succ]
      change u (n + 1) - u 0 ≤
        positivePathVariation u n + max (u (n + 1) - u n) 0
      have hstep : u (n + 1) - u n ≤ max (u (n + 1) - u n) 0 :=
        le_max_left _ _
      linarith

theorem strictTailIndicator_path_bound
    (u : ℕ → ℝ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    strictTailIndicator R (u n) ≤
      strictTailIndicator (R / 2) (u 0) +
        (2 / R) * positivePathVariation u n := by
  have hvar := positivePathVariation_nonneg u n
  by_cases hn : R < u n
  · rw [strictTailIndicator, if_pos hn]
    by_cases hzero : R / 2 < u 0
    · rw [strictTailIndicator, if_pos hzero]
      have hscale : 0 ≤ (2 / R) * positivePathVariation u n := by
        exact mul_nonneg (by positivity) hvar
      linarith
    · rw [strictTailIndicator, if_neg hzero, zero_add]
      have hend := endpoint_sub_le_positivePathVariation u n
      have hdouble : R ≤ 2 * positivePathVariation u n := by
        have hu0 : u 0 ≤ R / 2 := le_of_not_gt hzero
        nlinarith
      calc
        1 ≤ (2 * positivePathVariation u n) / R :=
          (le_div_iff₀ hR).2 (by simpa using hdouble)
        _ = (2 / R) * positivePathVariation u n := by ring
  · rw [strictTailIndicator, if_neg hn]
    have hinitial : 0 ≤ strictTailIndicator (R / 2) (u 0) := by
      unfold strictTailIndicator
      split_ifs <;> norm_num
    exact add_nonneg hinitial (mul_nonneg (by positivity) hvar)

theorem weightedPathTail_le_initial_add
    {Ω : Type*} (w : Ω → ℝ) (K : Ω → ℕ → ℝ) (n : ℕ) (R : ℝ)
    (hR : 0 < R) (hw : ∀ ω, 0 ≤ w ω) (hwOne : HasSum w 1)
    (hincSummable : ∀ i ∈ Finset.range n,
      Summable (fun ω ↦ w ω * positivePathIncrement (K ω) i))
    (hincLe : ∀ i ∈ Finset.range n,
      (∑' ω, w ω * positivePathIncrement (K ω) i) ≤ 4) :
    weightedPathTail w K n R ≤
      weightedPathTail w K 0 (R / 2) + 8 * (n : ℝ) / R := by
  have hindicatorNonneg (a x : ℝ) : 0 ≤ strictTailIndicator a x := by
    unfold strictTailIndicator
    split_ifs <;> norm_num
  have hindicatorLeOne (a x : ℝ) : strictTailIndicator a x ≤ 1 := by
    unfold strictTailIndicator
    split_ifs <;> norm_num
  have htailSummable :
      Summable (fun ω ↦ w ω * strictTailIndicator R (K ω n)) := by
    apply hwOne.summable.of_nonneg_of_le
    · intro ω
      exact mul_nonneg (hw ω) (hindicatorNonneg R (K ω n))
    · intro ω
      simpa using mul_le_mul_of_nonneg_left (hindicatorLeOne R (K ω n)) (hw ω)
  have hinitialSummable :
      Summable (fun ω ↦ w ω * strictTailIndicator (R / 2) (K ω 0)) := by
    apply hwOne.summable.of_nonneg_of_le
    · intro ω
      exact mul_nonneg (hw ω) (hindicatorNonneg (R / 2) (K ω 0))
    · intro ω
      simpa using
        mul_le_mul_of_nonneg_left (hindicatorLeOne (R / 2) (K ω 0)) (hw ω)
  have hvariation :
      HasSum (fun ω ↦ w ω * positivePathVariation (K ω) n)
        (∑ i ∈ Finset.range n,
          ∑' ω, w ω * positivePathIncrement (K ω) i) := by
    have h := hasSum_sum (s := Finset.range n) (fun i hi ↦ (hincSummable i hi).hasSum)
    convert h using 1
    funext ω
    simp [positivePathVariation, Finset.mul_sum]
  have hvariationLe :
      (∑ i ∈ Finset.range n,
        ∑' ω, w ω * positivePathIncrement (K ω) i) ≤ 4 * (n : ℝ) := by
    calc
      (∑ i ∈ Finset.range n,
          ∑' ω, w ω * positivePathIncrement (K ω) i) ≤
          ∑ _i ∈ Finset.range n, (4 : ℝ) :=
        Finset.sum_le_sum fun i hi ↦ hincLe i hi
      _ = 4 * (n : ℝ) := by simp [mul_comm]
  have hpoint (ω : Ω) :
      w ω * strictTailIndicator R (K ω n) ≤
        w ω * strictTailIndicator (R / 2) (K ω 0) +
          (2 / R) * (w ω * positivePathVariation (K ω) n) := by
    have h := mul_le_mul_of_nonneg_left
      (strictTailIndicator_path_bound (K ω) n R hR) (hw ω)
    nlinarith
  have htailBound :
      weightedPathTail w K n R ≤
        weightedPathTail w K 0 (R / 2) +
          (2 / R) *
            (∑ i ∈ Finset.range n,
              ∑' ω, w ω * positivePathIncrement (K ω) i) := by
    unfold weightedPathTail
    have hrhsSummable := hinitialSummable.add (hvariation.summable.mul_left (2 / R))
    calc
      (∑' ω, w ω * strictTailIndicator R (K ω n)) ≤
          ∑' ω, (w ω * strictTailIndicator (R / 2) (K ω 0) +
            (2 / R) * (w ω * positivePathVariation (K ω) n)) :=
        htailSummable.tsum_le_tsum hpoint hrhsSummable
      _ = (∑' ω, w ω * strictTailIndicator (R / 2) (K ω 0)) +
          (2 / R) *
            (∑ i ∈ Finset.range n,
              ∑' ω, w ω * positivePathIncrement (K ω) i) := by
        rw [hinitialSummable.tsum_add (hvariation.summable.mul_left (2 / R)),
          hvariation.summable.tsum_mul_left, hvariation.tsum_eq]
  calc
    weightedPathTail w K n R ≤
        weightedPathTail w K 0 (R / 2) +
          (2 / R) *
            (∑ i ∈ Finset.range n,
              ∑' ω, w ω * positivePathIncrement (K ω) i) := htailBound
    _ ≤ weightedPathTail w K 0 (R / 2) + (2 / R) * (4 * (n : ℝ)) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hvariationLe (by positivity)) _
    _ = weightedPathTail w K 0 (R / 2) + 8 * (n : ℝ) / R := by ring

end

end DerridaRetaux
