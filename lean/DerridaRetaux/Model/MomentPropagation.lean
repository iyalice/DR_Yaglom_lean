import DerridaRetaux.Model.Criticality
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

/-!
# Finite-step propagation of the third tilted moment

The manuscript uses third derivatives only after observing that a finite third
exponentially tilted moment survives every finite Derrida--Retaux step.  This file
proves that fact coefficientwise.  The convolution calculation is kept separate from
the later cubic carrier `h_m`: it is only a finiteness result and uses no published
input.
-/

noncomputable section

/-- Coefficients weighted by their squared index and by a geometric parameter. -/
def secondMomentScale (s : ℝ) (a : Seq) : Seq :=
  fun k : ℕ ↦ (k : ℝ) ^ 2 * s ^ k * a k

/-- Coefficients weighted by their cubed index and by a geometric parameter. -/
def thirdMomentScale (s : ℝ) (a : Seq) : Seq :=
  fun k : ℕ ↦ (k : ℝ) ^ 3 * s ^ k * a k

@[simp]
theorem secondMomentScale_apply (s : ℝ) (a : Seq) (k : ℕ) :
    secondMomentScale s a k = (k : ℝ) ^ 2 * s ^ k * a k :=
  rfl

@[simp]
theorem thirdMomentScale_apply (s : ℝ) (a : Seq) (k : ℕ) :
    thirdMomentScale s a k = (k : ℝ) ^ 3 * s ^ k * a k :=
  rfl

/-- The squared-index weight obeys the quadratic Cauchy-product rule. -/
theorem secondMomentScale_conv (s : ℝ) (a b : Seq) :
    secondMomentScale s (conv a b) =
      fun n : ℕ ↦
        conv (secondMomentScale s a) (powerScale s b) n +
          2 * conv (firstMomentScale s a) (firstMomentScale s b) n +
            conv (powerScale s a) (secondMomentScale s b) n := by
  funext n
  rw [secondMomentScale_apply, conv_apply, Finset.mul_sum]
  calc
    ∑ k ∈ Finset.range (n + 1),
        ((n : ℝ) ^ 2 * s ^ n) * (a k * b (n - k)) =
      ∑ k ∈ Finset.range (n + 1),
        (secondMomentScale s a k * powerScale s b (n - k) +
          2 * (firstMomentScale s a k * firstMomentScale s b (n - k)) +
            powerScale s a k * secondMomentScale s b (n - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpow : s ^ n = s ^ k * s ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      simp only [secondMomentScale_apply, firstMomentScale_apply, powerScale_apply]
      rw [hpow, Nat.cast_sub hkn]
      ring
    _ = conv (secondMomentScale s a) (powerScale s b) n +
          2 * conv (firstMomentScale s a) (firstMomentScale s b) n +
            conv (powerScale s a) (secondMomentScale s b) n := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, conv_apply]

/-- The cubed-index weight obeys the cubic Cauchy-product rule. -/
theorem thirdMomentScale_conv (s : ℝ) (a b : Seq) :
    thirdMomentScale s (conv a b) =
      fun n : ℕ ↦
        conv (thirdMomentScale s a) (powerScale s b) n +
          3 * conv (secondMomentScale s a) (firstMomentScale s b) n +
            3 * conv (firstMomentScale s a) (secondMomentScale s b) n +
              conv (powerScale s a) (thirdMomentScale s b) n := by
  funext n
  rw [thirdMomentScale_apply, conv_apply, Finset.mul_sum]
  calc
    ∑ k ∈ Finset.range (n + 1),
        ((n : ℝ) ^ 3 * s ^ n) * (a k * b (n - k)) =
      ∑ k ∈ Finset.range (n + 1),
        (thirdMomentScale s a k * powerScale s b (n - k) +
          3 * (secondMomentScale s a k * firstMomentScale s b (n - k)) +
            3 * (firstMomentScale s a k * secondMomentScale s b (n - k)) +
              powerScale s a k * thirdMomentScale s b (n - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpow : s ^ n = s ^ k * s ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      simp only [thirdMomentScale_apply, secondMomentScale_apply,
        firstMomentScale_apply, powerScale_apply]
      rw [hpow, Nat.cast_sub hkn]
      ring
    _ = conv (thirdMomentScale s a) (powerScale s b) n +
          3 * conv (secondMomentScale s a) (firstMomentScale s b) n +
            3 * conv (firstMomentScale s a) (secondMomentScale s b) n +
              conv (powerScale s a) (thirdMomentScale s b) n := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, conv_apply]

/-- Second tilted summability is summability of `secondMomentScale` at `s = m`. -/
theorem tiltSummable_two_iff_secondMomentScale_summable
    (m : ℕ) (p : ProbabilityMass) :
    TiltSummable m 2 p ↔ Summable (secondMomentScale (m : ℝ) p) := by
  rfl

/-- Third tilted summability is summability of `thirdMomentScale` at `s = m`. -/
theorem tiltSummable_three_iff_thirdMomentScale_summable
    (m : ℕ) (p : ProbabilityMass) :
    TiltSummable m 3 p ↔ Summable (thirdMomentScale (m : ℝ) p) := by
  rfl

/-- A finite third tilted moment implies a finite second tilted moment. -/
theorem tiltSummable_two_of_three (m : ℕ) (p : ProbabilityMass)
    (hthree : TiltSummable m 3 p) : TiltSummable m 2 p := by
  apply Summable.of_nonneg_of_le
    (fun k : ℕ ↦ mul_nonneg
      (mul_nonneg (sq_nonneg (k : ℝ)) (pow_nonneg (Nat.cast_nonneg m) k))
      (p.nonneg k))
    ?_ hthree
  intro k
  have hkpow : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
    cases k with
    | zero => norm_num
    | succ k =>
        have hkone : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        nlinarith [sq_nonneg ((k + 1 : ℕ) : ℝ)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hkpow (pow_nonneg (Nat.cast_nonneg m) k))
    (p.nonneg k)

/-- All geometric moments through order three remain summable under a convolution
power when they are summable for the input sequence. -/
theorem momentScales_convPow_summable
    (r : ℕ) (s : ℝ) (a : Seq)
    (hzero : Summable (powerScale s a))
    (hone : Summable (firstMomentScale s a))
    (htwo : Summable (secondMomentScale s a))
    (hthree : Summable (thirdMomentScale s a)) :
    Summable (powerScale s (convPow r a)) ∧
      Summable (firstMomentScale s (convPow r a)) ∧
        Summable (secondMomentScale s (convPow r a)) ∧
          Summable (thirdMomentScale s (convPow r a)) := by
  induction r with
  | zero =>
      have hfirstZero :
          firstMomentScale s (convPow 0 a) = fun _ : ℕ ↦ 0 := by
        funext k
        cases k <;> simp [firstMomentScale, convPow, diracSeq]
      have hsecondZero :
          secondMomentScale s (convPow 0 a) = fun _ : ℕ ↦ 0 := by
        funext k
        cases k <;> simp [secondMomentScale, convPow, diracSeq]
      have hthirdZero :
          thirdMomentScale s (convPow 0 a) = fun _ : ℕ ↦ 0 := by
        funext k
        cases k <;> simp [thirdMomentScale, convPow, diracSeq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using diracSeq_summable 0
      · rw [hfirstZero]
        exact summable_zero
      · rw [hsecondZero]
        exact summable_zero
      · rw [hthirdZero]
        exact summable_zero
  | succ r ih =>
      rcases ih with ⟨ihzero, ihone, ihtwo, ihthree⟩
      rw [convPow_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← conv_powerScale]
        exact conv_summable (powerScale s (convPow r a)) (powerScale s a)
          ihzero hzero
      · rw [firstMomentScale_conv]
        have hleft := conv_summable (firstMomentScale s (convPow r a))
          (powerScale s a) ihone hzero
        have hright := conv_summable (powerScale s (convPow r a))
          (firstMomentScale s a) ihzero hone
        exact hleft.add hright
      · rw [secondMomentScale_conv]
        have hleft := conv_summable (secondMomentScale s (convPow r a))
          (powerScale s a) ihtwo hzero
        have hmiddle := conv_summable (firstMomentScale s (convPow r a))
          (firstMomentScale s a) ihone hone
        have hright := conv_summable (powerScale s (convPow r a))
          (secondMomentScale s a) ihzero htwo
        exact (hleft.add (hmiddle.mul_left 2)).add hright
      · rw [thirdMomentScale_conv]
        have hleft := conv_summable (thirdMomentScale s (convPow r a))
          (powerScale s a) ihthree hzero
        have hmiddleLeft := conv_summable (secondMomentScale s (convPow r a))
          (firstMomentScale s a) ihtwo hone
        have hmiddleRight := conv_summable (firstMomentScale s (convPow r a))
          (secondMomentScale s a) ihone htwo
        have hright := conv_summable (powerScale s (convPow r a))
          (thirdMomentScale s a) ihzero hthree
        exact ((hleft.add (hmiddleLeft.mul_left 3)).add
          (hmiddleRight.mul_left 3)).add hright

/-- A finite third tilted moment propagates through one coefficient-level DR step. -/
theorem tiltSummable_three_drStepProb
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcritical : Critical m p) (hthree : TiltSummable m 3 p) :
    TiltSummable m 3 (drStepProb m p) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hzero : Summable (powerScale (m : ℝ) p) := by
    simpa [powerScale, TiltSummable] using hcritical.1
  have hone : Summable (firstMomentScale (m : ℝ) p) :=
    (tiltSummable_one_iff_firstMomentScale_summable m p).mp hcritical.2.1
  have htwo : Summable (secondMomentScale (m : ℝ) p) :=
    (tiltSummable_two_iff_secondMomentScale_summable m p).mp
      (tiltSummable_two_of_three m p hthree)
  have hthreeScale : Summable (thirdMomentScale (m : ℝ) p) :=
    (tiltSummable_three_iff_thirdMomentScale_summable m p).mp hthree
  have hconv := (momentScales_convPow_summable m (m : ℝ) p hzero hone htwo
    hthreeScale).2.2.2
  have htail :
      Summable (fun n : ℕ ↦ thirdMomentScale (m : ℝ) (convPow m p) (n + 2)) :=
    (summable_nat_add_iff 2).2 hconv
  have hscaled := htail.mul_left (m : ℝ)⁻¹
  have hstepTail :
      Summable
        (fun n : ℕ ↦
          ((n + 1 : ℕ) : ℝ) ^ 3 * (m : ℝ) ^ (n + 1) *
            drStepProb m p (n + 1)) := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
          (pow_nonneg (Nat.cast_nonneg m) (n + 1)))
        ((drStepProb m p).nonneg (n + 1)))
      ?_ hscaled
    intro n
    simp only [drStepProb_apply, drStepSeq_succ]
    have hcubes : (((n + 1 : ℕ) : ℝ) ^ 3) ≤ (((n + 2 : ℕ) : ℝ) ^ 3) := by
      gcongr
      norm_num
    have hweight : 0 ≤ (m : ℝ) ^ (n + 1) * convPow m p (n + 2) :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg m) (n + 1))
        (convPow_nonneg m p p.nonneg (n + 2))
    rw [thirdMomentScale_apply]
    have hscale :
        (m : ℝ)⁻¹ *
            (((n + 2 : ℕ) : ℝ) ^ 3 * (m : ℝ) ^ (n + 2) * convPow m p (n + 2)) =
          ((n + 2 : ℕ) : ℝ) ^ 3 *
            ((m : ℝ) ^ (n + 1) * convPow m p (n + 2)) := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      field_simp
      ring
    rw [hscale]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcubes hweight
  apply (summable_nat_add_iff 1).1
  simpa [TiltSummable] using hstepTail

/-- The same propagation theorem for the PMF-backed paper-facing step. -/
theorem tiltSummable_three_drStep
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hcritical : Critical m p) (hthree : TiltSummable m 3 p) :
    TiltSummable m 3 (drStep m p) := by
  rw [drStep_eq_drStepProb]
  exact tiltSummable_three_drStepProb m p hm hcritical hthree

/-- Every finite generation of a critical orbit inherits the initial third tilted
moment finiteness. -/
theorem orbit_tiltSummable_three
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m)
    (hcritical : Critical m p₀) (hthree : TiltSummable m 3 p₀) (n : ℕ) :
    TiltSummable m 3 (orbit m p₀ n) := by
  induction n with
  | zero => simpa using hthree
  | succ n ih =>
      rw [orbit_succ]
      exact tiltSummable_three_drStep m (orbit m p₀ n) hm
        (orbit_critical m p₀ hm hcritical n) ih

end

end DerridaRetaux
