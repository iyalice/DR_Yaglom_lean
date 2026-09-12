import DerridaRetaux.Basic.Sequence
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

/-!
# Zero-extended integer coefficient shifts

The arrival-coordinate formulas use Laurent-style exponent shifts, but only their
coefficients are needed.  This file embeds natural-indexed sequences into integer
indices by zero extension and defines a total integer shift.  It therefore avoids
both truncated-subtraction ambiguity and an unnecessary formal Laurent-series layer.
-/

/-- Extend a natural-indexed coefficient sequence by zero on negative integers. -/
def zeroExtend (f : Seq) (z : ℤ) : ℝ :=
  if 0 ≤ z then f z.toNat else 0

/-- Coefficient shift corresponding to multiplication by a formal monomial `z^d`. -/
def shiftByInt (d : ℤ) (f : Seq) (n : ℕ) : ℝ :=
  zeroExtend f ((n : ℤ) - d)

@[simp]
theorem zeroExtend_ofNat (f : Seq) (n : ℕ) : zeroExtend f (n : ℤ) = f n := by
  simp [zeroExtend]

theorem zeroExtend_eq_zero_of_neg (f : Seq) (z : ℤ) (hz : z < 0) :
    zeroExtend f z = 0 := by
  simp [zeroExtend, not_le.mpr hz]

@[simp]
theorem zeroExtend_negSucc (f : Seq) (n : ℕ) :
    zeroExtend f (-((n + 1 : ℕ) : ℤ)) = 0 := by
  apply zeroExtend_eq_zero_of_neg
  omega

theorem zeroExtend_eq_of_nonneg (f : Seq) (z : ℤ) (hz : 0 ≤ z) :
    zeroExtend f z = f z.toNat := by
  simp [zeroExtend, hz]

@[simp]
theorem shiftByInt_zero (f : Seq) : shiftByInt 0 f = f := by
  funext n
  simp [shiftByInt]

/-- A positive shift has zero coefficients below its new support boundary. -/
theorem shiftByInt_eq_zero_of_lt
    (d n : ℕ) (f : Seq) (hn : n < d) :
    shiftByInt (d : ℤ) f n = 0 := by
  apply zeroExtend_eq_zero_of_neg
  exact sub_neg.mpr (by exact_mod_cast hn)

/-- At or above a positive shift, coefficient lookup uses ordinary subtraction. -/
theorem shiftByInt_of_le
    (d n : ℕ) (f : Seq) (hn : d ≤ n) :
    shiftByInt (d : ℤ) f n = f (n - d) := by
  rw [shiftByInt, zeroExtend_eq_of_nonneg]
  · congr
    omega
  · exact sub_nonneg.mpr (by exact_mod_cast hn)

/-- A negative integer shift is an ordinary left shift. -/
@[simp]
theorem shiftByInt_neg_ofNat (d n : ℕ) (f : Seq) :
    shiftByInt (-(d : ℤ)) f n = f (n + d) := by
  have hnonneg : 0 ≤ (n : ℤ) - (-(d : ℤ)) := by omega
  rw [shiftByInt, zeroExtend_eq_of_nonneg _ _ hnonneg]
  congr
  omega

/-- Pointwise support formulation for an arbitrary integer shift. -/
theorem shiftByInt_support (d : ℤ) (f : Seq) (n : ℕ) (hn : (n : ℤ) < d) :
    shiftByInt d f n = 0 := by
  apply zeroExtend_eq_zero_of_neg
  exact sub_neg.mpr hn

/-- Shifting by a natural amount agrees with `shiftRight` at one step. -/
@[simp]
theorem shiftByInt_one (f : Seq) : shiftByInt 1 f = shiftRight f := by
  funext n
  cases n with
  | zero => simp [shiftByInt, zeroExtend]
  | succ n => simp [shiftByInt, shiftRight]

/-- Shifting left by one agrees with `shiftLeft`. -/
@[simp]
theorem shiftByInt_neg_one (f : Seq) : shiftByInt (-1) f = shiftLeft f := by
  funext n
  simpa [shiftLeft] using shiftByInt_neg_ofNat 1 n f

end DerridaRetaux
