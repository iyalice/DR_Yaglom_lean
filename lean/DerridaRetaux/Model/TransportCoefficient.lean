import DerridaRetaux.Analysis.TransportPolynomial
import DerridaRetaux.Model.ZeroAtom
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Linear transport coefficients

This file formalizes the finite, purely algebraic part of source equations `eq:c` and
`eq:C`.  The infinite-product limit is deliberately not asserted here: its strict
positivity additionally needs the later summable-defect estimate.
-/

noncomputable section

/-- The source coefficient `c = m x^(m-1) / D`. -/
def transportCoeff (m : ℕ) (p : ProbabilityMass) : ℝ :=
  (m : ℝ) * zeroTilt m p ^ (m - 1) / tiltDenom m p

/-- The exclusive finite product `C_n = product_{j<n} c_j`. -/
def transportProduct (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, transportCoeff m (orbit m p₀ j)

@[simp]
theorem transportProduct_zero (m : ℕ) (p₀ : ProbabilityMass) :
    transportProduct m p₀ 0 = 1 := by
  simp [transportProduct]

theorem transportProduct_succ (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    transportProduct m p₀ (n + 1) =
      transportProduct m p₀ n * transportCoeff m (orbit m p₀ n) := by
  simp [transportProduct, Finset.prod_range_succ]

/-- A normalized tilted atom is at most one. -/
theorem zeroTilt_le_one
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    zeroTilt m p ≤ 1 := by
  simpa [zeroTilt] using (normalizedTiltLaw m p hm hcrit).apply_le_one 0

/-- The transport coefficient is nonnegative for every critical law. -/
theorem transportCoeff_nonneg
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    0 ≤ transportCoeff m p := by
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg m)
      (pow_nonneg (normalizedTilt_nonneg m p hm hcrit 0) (m - 1)))
    (le_trans zero_le_one (tiltDenom_one_le m p hm hcrit))

/-- A positive zero atom makes the transport coefficient strictly positive. -/
theorem transportCoeff_pos
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p)
    (hx : 0 < zeroTilt m p) :
    0 < transportCoeff m p := by
  apply div_pos _ (tiltDenom_pos m p hm hcrit)
  exact mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm))
    (pow_pos hx (m - 1))

/-- Exact quotient form of the defect `1-c`. -/
theorem one_sub_transportCoeff_eq
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    1 - transportCoeff m p =
      transportDefect m (zeroTilt m p) / tiltDenom m p := by
  have hD := tiltDenom_pos m p hm hcrit
  apply (eq_div_iff hD.ne').2
  rw [transportCoeff, sub_mul, one_mul, div_mul_cancel₀ _ hD.ne']
  rw [transportDefect, tiltDenom]

/-- The linear transport coefficient is at most one. -/
theorem transportCoeff_le_one
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    transportCoeff m p ≤ 1 := by
  have hdefect := transportDefect_nonneg m (zeroTilt m p) hm
    (normalizedTilt_nonneg m p hm hcrit 0)
  have honeSub : 0 ≤ 1 - transportCoeff m p := by
    rw [one_sub_transportCoeff_eq m p hm hcrit]
    exact div_nonneg hdefect (tiltDenom_pos m p hm hcrit).le
  linarith

/-- The exact defect is bounded by an explicit multiple of `(1-x)^2`. -/
theorem one_subCoeff_le_quadratic
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p) :
    1 - transportCoeff m p ≤
      ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 *
        (1 - zeroTilt m p) ^ 2 := by
  have hx0 := normalizedTilt_nonneg m p hm hcrit 0
  have hx1 := zeroTilt_le_one m p hm hcrit
  have hdefect := transportDefect_nonneg m (zeroTilt m p) hm hx0
  have hbound := transportDefect_le_quadratic m (zeroTilt m p) hm hx0 hx1
  have hDpos := tiltDenom_pos m p hm hcrit
  have hDone := tiltDenom_one_le m p hm hcrit
  rw [one_sub_transportCoeff_eq m p hm hcrit]
  calc
    transportDefect m (zeroTilt m p) / tiltDenom m p ≤
        transportDefect m (zeroTilt m p) := by
      apply (div_le_iff₀ hDpos).2
      nlinarith
    _ ≤ ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 *
        (1 - zeroTilt m p) ^ 2 := hbound

/-- Every finite transport product is nonnegative along a critical orbit. -/
theorem transportProduct_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    0 ≤ transportProduct m p₀ n := by
  apply Finset.prod_nonneg
  intro j hj
  exact transportCoeff_nonneg m (orbit m p₀ j) hm
    (orbit_critical m p₀ hm hcrit j)

/-- Under the source admissibility condition every finite transport product is
strictly positive. -/
theorem transportProduct_pos
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1)) (n : ℕ) :
    0 < transportProduct m p₀ n := by
  apply Finset.prod_pos
  intro j hj
  exact transportCoeff_pos m (orbit m p₀ j) (by omega)
    (orbit_critical m p₀ (by omega) hcrit j)
    (orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint j)

/-- The finite products decrease one step at a time. -/
theorem transportProduct_succ_le
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (hcrit : Critical m p₀)
    (n : ℕ) :
    transportProduct m p₀ (n + 1) ≤ transportProduct m p₀ n := by
  rw [transportProduct_succ]
  exact mul_le_of_le_one_right (transportProduct_nonneg m p₀ hm hcrit n)
    (transportCoeff_le_one m (orbit m p₀ n) hm
      (orbit_critical m p₀ hm hcrit n))

end

end DerridaRetaux
