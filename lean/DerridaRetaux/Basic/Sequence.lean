import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Real sequences on the natural numbers

This file fixes the unbundled sequence type used for signed coefficient arrays in the
Derrida--Retaux formalization.  It also records the elementary shift, finite-difference,
summation-by-parts, and integer-scale regular-variation facts needed downstream.

The notions of slow and regular variation below quantify over positive *integer* dilations.
They are deliberately named accordingly: they are not presented as a replacement for the
full Karamata theory with arbitrary positive real dilations.
-/

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace DerridaRetaux

/-- A possibly signed real sequence indexed by the natural numbers. -/
abbrev Seq := ℕ → ℝ

/-- The source scale `L_n = n + 1`, regarded as a positive real number. -/
def profileScale (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

@[simp]
theorem profileScale_pos (n : ℕ) : 0 < profileScale n := by
  simp only [profileScale]
  positivity

/-- The source's left shift `S`: discard the zeroth entry. -/
def shiftLeft (f : Seq) : Seq := fun k ↦ f (k + 1)

/-- The source's right shift `T`, with zero extension at the boundary. -/
def shiftRight (f : Seq) : Seq
  | 0 => 0
  | k + 1 => f k

/-- The forward discrete derivative `Δ = I - S` from the source. -/
def discreteDerivative (f : Seq) : Seq := fun k ↦ f k - f (k + 1)

/-- The cubic weight `(1 + j/L)^3` from the source. -/
noncomputable def cubicWeight (L : ℝ) (j : ℕ) : ℝ :=
  (1 + (j : ℝ) / L) ^ 3

/-- The source's cubic weighted `ℓ¹` quantity.  It is total as a `tsum`; finiteness is
proved separately at each use. -/
noncomputable def weightedL1Three (L : ℝ) (f : Seq) : ℝ :=
  ∑' j : ℕ, cubicWeight L j * |f j|

/-- Pointwise form of the source's cubic weighted supremum bound.  Using a predicate
instead of a real-valued infinite supremum avoids conditional-completeness side
conditions while retaining the literal estimate needed downstream. -/
def WeightedSupThreeLE (L : ℝ) (f : Seq) (C : ℝ) : Prop :=
  ∀ j : ℕ, cubicWeight L j * |f j| ≤ C

/-- Pointwise form of an unweighted supremum bound. -/
def SupLE (f : Seq) (C : ℝ) : Prop := ∀ j : ℕ, |f j| ≤ C

@[simp]
theorem shiftLeft_apply (f : Seq) (k : ℕ) : shiftLeft f k = f (k + 1) := rfl

@[simp]
theorem shiftRight_zero (f : Seq) : shiftRight f 0 = 0 := rfl

@[simp]
theorem shiftRight_succ (f : Seq) (k : ℕ) : shiftRight f (k + 1) = f k := rfl

@[simp]
theorem discreteDerivative_apply (f : Seq) (k : ℕ) :
    discreteDerivative f k = f k - f (k + 1) := rfl

/-- A finite sum of forward differences telescopes exactly. -/
theorem sum_discreteDerivative (f : Seq) (n : ℕ) :
    ∑ k ∈ Finset.range n, discreteDerivative f k = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [discreteDerivative_apply]
      ring

/-- Split an absolutely summable natural-indexed tail into its first term and
the next tail. -/
theorem tsum_nat_add_eq_self_add_succ (f : Seq) (hf : Summable f) (n : ℕ) :
    (∑' j : ℕ, f (n + j)) = f n + ∑' j : ℕ, f (n + (j + 1)) := by
  have hshift : Summable (fun j : ℕ ↦ f (n + j)) :=
    by simpa only [Nat.add_comm n] using (summable_nat_add_iff n).2 hf
  simpa only [Nat.add_zero] using hshift.tsum_eq_zero_add

/-- Finite Abel summation for a sequence and the forward difference of another sequence.

The `n + 1` indexing makes the formula valid without a nonempty-range hypothesis and avoids
truncated subtraction at the right endpoint.
-/
theorem summationByParts (weight tail : Seq) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), weight k * discreteDerivative tail k =
      weight 0 * tail 0 +
        ∑ k ∈ Finset.range n, (weight (k + 1) - weight k) * tail (k + 1) -
          weight n * tail (n + 1) := by
  induction n with
  | zero =>
      simp [discreteDerivative]
      ring
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [discreteDerivative_apply]
      ring

/-- Reindex a range starting at one as a range starting at zero. -/
theorem sum_Ico_one_eq_sum_range_shift (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Ico 1 (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Ico_succ_top (Nat.succ_le_succ (Nat.zero_le n)),
        Finset.sum_range_succ, ih]

/-- The exact square-weight Abel identity used in the far-arrival estimate.

Writing the source endpoint as `s = n + 1`, this is
`sum_{v < s} (v+1)^2 q_v = T_0 + sum_{1 ≤ v < s} (2v+1) T_v - s^2 T_s`.
-/
theorem squareWeightSummationByParts (q tail : Seq) (n : ℕ)
    (hq : ∀ k : ℕ, q k = discreteDerivative tail k) :
    ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℝ) ^ 2 * q k =
      tail 0 +
        ∑ k ∈ Finset.range n, ((2 * (k + 1) + 1 : ℕ) : ℝ) * tail (k + 1) -
          ((n + 1 : ℕ) : ℝ) ^ 2 * tail (n + 1) := by
  rw [show (∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℝ) ^ 2 * q k) =
      ∑ k ∈ Finset.range (n + 1),
        ((k + 1 : ℕ) : ℝ) ^ 2 * discreteDerivative tail k by
    apply Finset.sum_congr rfl
    intro k _
    rw [hq k]]
  rw [summationByParts]
  have hsum :
      (∑ k ∈ Finset.range n, (((k + 1 + 1 : ℕ) : ℝ) ^ 2 -
          ((k + 1 : ℕ) : ℝ) ^ 2) * tail (k + 1)) =
        ∑ k ∈ Finset.range n, ((2 * (k + 1) + 1 : ℕ) : ℝ) * tail (k + 1) := by
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [hsum]
  norm_num

/-- The same square-weight identity with the manuscript's endpoint `s` and literal
`1 ≤ v < s` indexing. -/
theorem squareWeightSummationByParts_source (q tail : Seq) (s : ℕ) (hs : 0 < s)
    (hq : ∀ k : ℕ, q k = discreteDerivative tail k) :
    ∑ k ∈ Finset.range s, ((k + 1 : ℕ) : ℝ) ^ 2 * q k =
      tail 0 + ∑ k ∈ Finset.Ico 1 s, ((2 * k + 1 : ℕ) : ℝ) * tail k -
        (s : ℝ) ^ 2 * tail s := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simpa only [sum_Ico_one_eq_sum_range_shift] using
    squareWeightSummationByParts q tail n hq

/-- The square-weight Abel identity turns a `C / (v+1)` tail bound into a linear bound.
This is the generic estimate behind the manuscript's `O(s)` conclusion in U26. -/
theorem squareWeightSum_le (q tail : Seq) (n : ℕ) (C : ℝ)
    (hq : ∀ k : ℕ, q k = discreteDerivative tail k) (hC : 0 ≤ C)
    (htail_nonneg : ∀ k : ℕ, 0 ≤ tail k)
    (htail_le : ∀ k : ℕ, tail k ≤ C / ((k + 1 : ℕ) : ℝ)) :
    ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℝ) ^ 2 * q k ≤
      C + 2 * C * n := by
  rw [squareWeightSummationByParts q tail n hq]
  have hzero : tail 0 ≤ C := by simpa using htail_le 0
  have hend : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * tail (n + 1) :=
    mul_nonneg (sq_nonneg _) (htail_nonneg _)
  have hsum :
      (∑ k ∈ Finset.range n, ((2 * (k + 1) + 1 : ℕ) : ℝ) * tail (k + 1)) ≤
        ∑ _k ∈ Finset.range n, 2 * C := by
    apply Finset.sum_le_sum
    intro k _
    have hden : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
    have hcoef : 0 ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) := by positivity
    have hcoef_le :
        ((2 * (k + 1) + 1 : ℕ) : ℝ) ≤ 2 * ((k + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * (k + 1) + 1 ≤ 2 * (k + 2) by omega)
    calc
      ((2 * (k + 1) + 1 : ℕ) : ℝ) * tail (k + 1) ≤
          ((2 * (k + 1) + 1 : ℕ) : ℝ) * (C / ((k + 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (htail_le (k + 1)) hcoef
      _ ≤ 2 * ((k + 2 : ℕ) : ℝ) * (C / ((k + 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef_le (div_nonneg hC hden.le)
      _ = 2 * C := by
        field_simp
        ring
  calc
    tail 0 +
          ∑ k ∈ Finset.range n, ((2 * (k + 1) + 1 : ℕ) : ℝ) * tail (k + 1) -
        ((n + 1 : ℕ) : ℝ) ^ 2 * tail (n + 1) ≤
        tail 0 +
          ∑ k ∈ Finset.range n, ((2 * (k + 1) + 1 : ℕ) : ℝ) * tail (k + 1) :=
      sub_le_self _ hend
    _ ≤ C + ∑ _k ∈ Finset.range n, 2 * C := add_le_add hzero hsum
    _ = C + 2 * C * n := by simp [mul_comm]

/-- A sequence converging to a nonzero constant is slowly varying under positive integer
dilations. -/
def IsIntegerSlowlyVarying (a : Seq) : Prop :=
  ∀ d : ℕ, 0 < d →
    Tendsto (fun n : ℕ ↦ a (d * n) / a n) atTop (𝓝 1)

/-- A concrete sequence version of regular variation with exponent `-1`, restricted to
positive integer dilations. -/
def IsIntegerRegularlyVaryingNegOne (a : Seq) : Prop :=
  ∀ d : ℕ, 0 < d →
    Tendsto (fun n : ℕ ↦ a (d * n) / a n) atTop (𝓝 (1 / (d : ℝ)))

/-- The explicit inverse-linear asymptotic used to obtain regular variation.  The `n + 1`
normalization avoids a special value at zero. -/
def HasInverseLinearAsymptotic (a : Seq) (c : ℝ) : Prop :=
  Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) * a n) atTop (𝓝 c)

/-- A positive integer dilation tends to infinity. -/
theorem tendsto_nat_mul_atTop (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ d * n) atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro a b hab
  exact (Nat.mul_lt_mul_left hd).2 hab

/-- A nonzero finite limit transfers to ratios along every positive integer dilation. -/
theorem tendsto_dilation_ratio_one (a : Seq) (c : ℝ) (hc : c ≠ 0)
    (ha : Tendsto a atTop (𝓝 c)) : IsIntegerSlowlyVarying a := by
  intro d hd
  have had : Tendsto (fun n : ℕ ↦ a (d * n)) atTop (𝓝 c) :=
    ha.comp (tendsto_nat_mul_atTop d hd)
  simpa only [Pi.div_apply, div_self hc] using had.div ha hc

/-- Ratio transfer: an inverse-linear asymptotic with nonzero coefficient forces the
successive-term ratio to converge to one. -/
theorem successor_ratio_tendsto_one (a : Seq) (c : ℝ) (hc : c ≠ 0)
    (ha : HasInverseLinearAsymptotic a c) :
    Tendsto (fun n : ℕ ↦ a (n + 1) / a n) atTop (𝓝 1) := by
  let scaled : Seq := fun n ↦ ((n + 1 : ℕ) : ℝ) * a n
  have hscaled : Tendsto scaled atTop (𝓝 c) := ha
  have hscaled_succ : Tendsto (fun n : ℕ ↦ scaled (n + 1)) atTop (𝓝 c) :=
    hscaled.comp (tendsto_add_atTop_nat 1)
  have hratio :
      Tendsto (fun n : ℕ ↦ scaled (n + 1) / scaled n) atTop (𝓝 (c / c)) :=
    hscaled_succ.div hscaled hc
  have hindex :
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))
        atTop (𝓝 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_mul, one_div, inv_one,
      add_comm] using
      RCLike.tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 2 1 one_ne_zero
  have hnonzero : ∀ᶠ n : ℕ in atTop, scaled n ≠ 0 := hscaled.eventually_ne hc
  have heq :
      (fun n : ℕ ↦ scaled (n + 1) / scaled n *
        (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))) =ᶠ[atTop]
        (fun n : ℕ ↦ a (n + 1) / a n) := by
    filter_upwards [hnonzero] with n hn
    have han : a n ≠ 0 := by
      intro h
      apply hn
      simp [scaled, h]
    dsimp [scaled]
    field_simp
    ring
  simpa [hc] using Tendsto.congr' heq (hratio.mul hindex)

/-- Inverse-linear asymptotics imply integer-scale regular variation of exponent `-1`.
This is the fixed-integer scaling statement actually justified by the hypotheses. -/
theorem inverseLinear_isIntegerRegularlyVaryingNegOne (a : Seq) (c : ℝ) (hc : c ≠ 0)
    (ha : HasInverseLinearAsymptotic a c) : IsIntegerRegularlyVaryingNegOne a := by
  intro d hd
  let scaled : Seq := fun n ↦ ((n + 1 : ℕ) : ℝ) * a n
  have hscaled : Tendsto scaled atTop (𝓝 c) := ha
  have hscaled_dilate : Tendsto (fun n : ℕ ↦ scaled (d * n)) atTop (𝓝 c) :=
    hscaled.comp (tendsto_nat_mul_atTop d hd)
  have hratio :
      Tendsto (fun n : ℕ ↦ scaled (d * n) / scaled n) atTop (𝓝 (c / c)) :=
    hscaled_dilate.div hscaled hc
  have hdreal : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hindex :
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / ((d * n + 1 : ℕ) : ℝ))
        atTop (𝓝 (1 / (d : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, one_mul, add_comm] using
      RCLike.tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 1 1 hdreal
  have hnonzero : ∀ᶠ n : ℕ in atTop, scaled n ≠ 0 := hscaled.eventually_ne hc
  have heq :
      (fun n : ℕ ↦ scaled (d * n) / scaled n *
        (((n + 1 : ℕ) : ℝ) / ((d * n + 1 : ℕ) : ℝ))) =ᶠ[atTop]
        (fun n : ℕ ↦ a (d * n) / a n) := by
    filter_upwards [hnonzero] with n hn
    have han : a n ≠ 0 := by
      intro h
      apply hn
      simp [scaled, h]
    dsimp [scaled]
    field_simp
    ring
  simpa [hc] using Tendsto.congr' heq (hratio.mul hindex)

/-- A convergent sequence has an unscaled discrete derivative tending to zero. -/
theorem discreteDerivative_tendsto_zero (a : Seq) (c : ℝ)
    (ha : Tendsto a atTop (𝓝 c)) : Tendsto (discreteDerivative a) atTop (𝓝 0) := by
  have ha_succ : Tendsto (fun n : ℕ ↦ a (n + 1)) atTop (𝓝 c) :=
    ha.comp (tendsto_add_atTop_nat 1)
  simpa [discreteDerivative] using ha.sub ha_succ

end DerridaRetaux
