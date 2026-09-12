import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# The double-zero transport polynomial

The coefficient estimate following source equation `eq:c` uses that

`1 + (m - 1) x^m - m x^(m-1)`

has a double zero at `x = 1` and is nonnegative on `[0,1]`.  The finite factorization
below makes both facts literal and supplies an explicit arity-dependent quadratic
bound; no asymptotic notation or external estimate is used.
-/

/-- The defect polynomial in the linear transport coefficient. -/
def transportDefect (m : ℕ) (x : ℝ) : ℝ :=
  1 + ((m : ℝ) - 1) * x ^ m - (m : ℝ) * x ^ (m - 1)

/-- The finite polynomial left after removing the double root at one. -/
def transportWeightSum (r : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range r, ((i + 1 : ℕ) : ℝ) * x ^ i

/-- Successor-arity form of the exact double-root factorization. -/
theorem transportDefect_succ_factor (r : ℕ) (x : ℝ) :
    transportDefect (r + 1) x = (1 - x) ^ 2 * transportWeightSum r x := by
  induction r with
  | zero => simp [transportDefect, transportWeightSum]
  | succ r ih =>
      rw [transportWeightSum, Finset.sum_range_succ, ← transportWeightSum, mul_add,
        ← ih]
      simp only [transportDefect, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
        pow_succ]
      ring

/-- Source-arity form of the exact factorization. -/
theorem transportDefect_factor (m : ℕ) (x : ℝ) (hm : 1 ≤ m) :
    transportDefect m x =
      (1 - x) ^ 2 * transportWeightSum (m - 1) x := by
  have h := transportDefect_succ_factor (m - 1) x
  simpa only [Nat.sub_add_cancel hm] using h

/-- The remaining finite polynomial is nonnegative on the nonnegative half-line. -/
theorem transportWeightSum_nonneg (r : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ transportWeightSum r x := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg (i + 1)) (pow_nonneg hx i)

/-- The defect is nonnegative on `[0,∞)` at every positive arity. -/
theorem transportDefect_nonneg (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx : 0 ≤ x) :
    0 ≤ transportDefect m x := by
  rw [transportDefect_factor m x hm]
  exact mul_nonneg (sq_nonneg (1 - x))
    (transportWeightSum_nonneg (m - 1) x hx)

/-- Closed form for the coefficient sum at `x = 1`. -/
theorem transportWeightSum_one (r : ℕ) :
    transportWeightSum r 1 = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
  induction r with
  | zero => simp [transportWeightSum]
  | succ r ih =>
      rw [transportWeightSum, Finset.sum_range_succ, ← transportWeightSum, ih]
      norm_num
      ring

/-- On `[0,1]`, the remaining factor is bounded by its value at one. -/
theorem transportWeightSum_le_one (r : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    transportWeightSum r x ≤ transportWeightSum r 1 := by
  apply Finset.sum_le_sum
  intro i hi
  have hpow : x ^ i ≤ 1 := pow_le_one₀ hx0 hx1
  simpa only [one_pow, mul_one] using
    mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (i + 1))

/-- Explicit quadratic upper bound expressing the `O((1-x)^2)` source statement. -/
theorem transportDefect_le_quadratic
    (m : ℕ) (x : ℝ) (hm : 1 ≤ m) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    transportDefect m x ≤
      ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 * (1 - x) ^ 2 := by
  rw [transportDefect_factor m x hm]
  have hsum := transportWeightSum_le_one (m - 1) x hx0 hx1
  rw [transportWeightSum_one] at hsum
  nlinarith [sq_nonneg (1 - x)]

/-- The defect and its first-order change both vanish at `x = 1`; the displayed
factorization records the double zero without invoking derivatives. -/
@[simp]
theorem transportDefect_one (m : ℕ) (hm : 1 ≤ m) : transportDefect m 1 = 0 := by
  rw [transportDefect_factor m 1 hm]
  norm_num

end DerridaRetaux
