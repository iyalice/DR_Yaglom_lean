import DerridaRetaux.Basic.Convolution
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

/-!
# Power-weighted Cauchy convolution

Coefficient scaling by `s^k` turns ordinary Cauchy convolution into convolution of
the scaled sequences.  These lemmas provide the summability-safe algebra behind all
later generating-function evaluations, including evaluation at the boundary `s = m`.
-/

/-- Multiply coefficient `k` by `s^k`. -/
def powerScale (s : ℝ) (a : Seq) : Seq :=
  fun k : ℕ ↦ s ^ k * a k

@[simp]
theorem powerScale_apply (s : ℝ) (a : Seq) (k : ℕ) :
    powerScale s a k = s ^ k * a k :=
  rfl

@[simp]
theorem powerScale_diracSeq_zero (s : ℝ) :
    powerScale s (diracSeq 0) = diracSeq 0 := by
  funext k
  cases k <;> simp [powerScale, diracSeq]

/-- Scaling by powers commutes with the finite Cauchy product. -/
theorem conv_powerScale (s : ℝ) (a b : Seq) :
    conv (powerScale s a) (powerScale s b) = powerScale s (conv a b) := by
  funext n
  rw [conv_apply, powerScale_apply, conv_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  change (s ^ k * a k) * (s ^ (n - k) * b (n - k)) =
    s ^ n * (a k * b (n - k))
  calc
    (s ^ k * a k) * (s ^ (n - k) * b (n - k)) =
        (s ^ k * s ^ (n - k)) * (a k * b (n - k)) := by ring
    _ = s ^ (k + (n - k)) * (a k * b (n - k)) := by rw [pow_add]
    _ = s ^ n * (a k * b (n - k)) := by rw [Nat.add_sub_of_le hkn]

/-- Scaling by powers commutes with every convolution power, including power zero. -/
theorem convPow_powerScale (r : ℕ) (s : ℝ) (a : Seq) :
    convPow r (powerScale s a) = powerScale s (convPow r a) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [convPow_succ, convPow_succ, ih, conv_powerScale]

@[simp]
theorem convPow_apply_zero (r : ℕ) (a : Seq) :
    convPow r a 0 = a 0 ^ r := by
  induction r with
  | zero => simp
  | succ r ih => simp [convPow_succ, conv_zero, ih, pow_succ]

/-- The Cauchy product theorem after evaluation at a real parameter. -/
theorem powerScale_conv_hasSum (s : ℝ) (a b : Seq) (A B : ℝ)
    (ha : HasSum (powerScale s a) A) (hb : HasSum (powerScale s b) B) :
    HasSum (powerScale s (conv a b)) (A * B) := by
  rw [← conv_powerScale]
  exact conv_hasSum (powerScale s a) (powerScale s b) A B ha hb

/-- Evaluation of a convolution power is the corresponding power of the evaluation. -/
theorem powerScale_convPow_hasSum (r : ℕ) (s : ℝ) (a : Seq) (A : ℝ)
    (ha : HasSum (powerScale s a) A) :
    HasSum (powerScale s (convPow r a)) (A ^ r) := by
  rw [← convPow_powerScale]
  exact convPow_hasSum r (powerScale s a) A ha

end DerridaRetaux
