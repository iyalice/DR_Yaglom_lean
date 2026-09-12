import DerridaRetaux.Basic.WeightedConvolution
import DerridaRetaux.Model.GeneratingFunction
import DerridaRetaux.Basic.RecursionBridge

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Preservation of criticality

This file supplies the coefficient-level first-moment Cauchy identity missing from
the zeroth-order generating-function layer, then proves preservation of the two
tilted summability conditions and of criticality under one Derrida--Retaux step.
-/

noncomputable section

/-- Coefficients weighted by their index and by a geometric parameter. -/
def firstMomentScale (s : ℝ) (a : Seq) : Seq :=
  fun k : ℕ ↦ (k : ℝ) * s ^ k * a k

@[simp]
theorem firstMomentScale_apply (s : ℝ) (a : Seq) (k : ℕ) :
    firstMomentScale s a k = (k : ℝ) * s ^ k * a k :=
  rfl

/-- The first-moment weight obeys the Leibniz rule for Cauchy convolution. -/
theorem firstMomentScale_conv (s : ℝ) (a b : Seq) :
    firstMomentScale s (conv a b) =
      fun n : ℕ ↦
        conv (firstMomentScale s a) (powerScale s b) n +
          conv (powerScale s a) (firstMomentScale s b) n := by
  funext n
  rw [firstMomentScale_apply, conv_apply, Finset.mul_sum]
  rw [conv_apply, conv_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [firstMomentScale_apply, powerScale_apply]
  rw [Nat.cast_sub hkn]
  have hpow : s ^ n = s ^ k * s ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hpow]
  ring

/-- Summing the first-moment convolution identity gives the product rule. -/
theorem firstMomentScale_conv_hasSum
    (s : ℝ) (a b : Seq) (A B A₁ B₁ : ℝ)
    (ha : HasSum (powerScale s a) A) (hb : HasSum (powerScale s b) B)
    (ha₁ : HasSum (firstMomentScale s a) A₁)
    (hb₁ : HasSum (firstMomentScale s b) B₁) :
    HasSum (firstMomentScale s (conv a b)) (A₁ * B + A * B₁) := by
  rw [firstMomentScale_conv]
  exact (conv_hasSum (firstMomentScale s a) (powerScale s b) A₁ B ha₁ hb).add
    (conv_hasSum (powerScale s a) (firstMomentScale s b) A B₁ ha hb₁)

/-- First-moment evaluation of a convolution power. -/
theorem firstMomentScale_convPow_hasSum
    (r : ℕ) (s : ℝ) (a : Seq) (A B : ℝ)
    (ha : HasSum (powerScale s a) A)
    (ha₁ : HasSum (firstMomentScale s a) B) :
    HasSum (firstMomentScale s (convPow r a)) ((r : ℝ) * A ^ (r - 1) * B) := by
  induction r with
  | zero =>
      have hzero : firstMomentScale s (convPow 0 a) = fun _ : ℕ ↦ 0 := by
        funext k
        cases k <;> simp [firstMomentScale, convPow, diracSeq]
      rw [hzero]
      simpa only [Nat.cast_zero, zero_mul] using
        (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0)
  | succ r ih =>
      rw [convPow_succ]
      have h := firstMomentScale_conv_hasSum s (convPow r a) a (A ^ r) A
        ((r : ℝ) * A ^ (r - 1) * B) B
        (powerScale_convPow_hasSum r s a A ha) ha ih ha₁
      convert h using 1
      cases r with
      | zero => simp
      | succ r =>
          simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
          ring

/-- First tilted summability is summability of `firstMomentScale` at `s = m`. -/
theorem tiltSummable_one_iff_firstMomentScale_summable (m : ℕ) (p : ProbabilityMass) :
    TiltSummable m 1 p ↔ Summable (firstMomentScale (m : ℝ) p) := by
  change
    Summable (fun k : ℕ ↦ (k : ℝ) ^ 1 * (m : ℝ) ^ k * p k) ↔
      Summable (fun k : ℕ ↦ (k : ℝ) * (m : ℝ) ^ k * p k)
  simp only [pow_one]

/-- The first-moment scaled coefficients sum to the first tilted moment. -/
theorem firstMomentScale_hasSum_tiltedMoment_one (m : ℕ) (p : ProbabilityMass)
    (h : TiltSummable m 1 p) :
    HasSum (firstMomentScale (m : ℝ) p) (tiltedMoment m 1 p) := by
  have hs := (tiltSummable_one_iff_firstMomentScale_summable m p).mp h
  simpa [firstMomentScale, tiltedMoment] using hs.hasSum

/-- Zeroth tilted summability propagates through one coefficient-level DR step. -/
theorem tiltSummable_zero_drStepProb (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (h : TiltSummable m 0 p) :
    TiltSummable m 0 (drStepProb m p) := by
  have hm0Nat : m ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0Nat
  have hp : GeneratingSummable (m : ℝ) p :=
    (tiltSummable_zero_iff_generatingSummable m p).mp h
  have hconv : Summable (powerScale (m : ℝ) (convPow m p)) :=
    (powerScale_convPow_hasSum m (m : ℝ) p (generatingFunction (m : ℝ) p)
      (generatingFunction_hasSum (m : ℝ) p hp)).summable
  have htail : Summable (fun n : ℕ ↦ powerScale (m : ℝ) (convPow m p) (n + 2)) :=
    (summable_nat_add_iff 2).2 hconv
  have hscaled := htail.mul_left (m : ℝ)⁻¹
  have hstepTail :
      Summable (fun n : ℕ ↦ powerScale (m : ℝ) (drStepProb m p) (n + 1)) := by
    convert hscaled using 1
    funext n
    simp only [powerScale_apply, drStepProb_apply, drStepSeq_succ]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    field_simp
    rw [pow_succ]
    ring
  apply (tiltSummable_zero_iff_generatingSummable m (drStepProb m p)).mpr
  exact (summable_nat_add_iff 1).1 hstepTail

/-- First tilted summability propagates when both criticality-level moments are finite. -/
theorem tiltSummable_one_drStepProb (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hzero : TiltSummable m 0 p) (hone : TiltSummable m 1 p) :
    TiltSummable m 1 (drStepProb m p) := by
  have hm0Nat : m ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0Nat
  have hp : GeneratingSummable (m : ℝ) p :=
    (tiltSummable_zero_iff_generatingSummable m p).mp hzero
  have hpHasSum := generatingFunction_hasSum (m : ℝ) p hp
  have hp₁HasSum := firstMomentScale_hasSum_tiltedMoment_one m p hone
  have hconv : Summable (powerScale (m : ℝ) (convPow m p)) :=
    (powerScale_convPow_hasSum m (m : ℝ) p (generatingFunction (m : ℝ) p)
      hpHasSum).summable
  have hconv₁ : Summable (firstMomentScale (m : ℝ) (convPow m p)) :=
    (firstMomentScale_convPow_hasSum m (m : ℝ) p (generatingFunction (m : ℝ) p)
      (tiltedMoment m 1 p) hpHasSum hp₁HasSum).summable
  have htail : Summable (fun n : ℕ ↦ powerScale (m : ℝ) (convPow m p) (n + 2)) :=
    (summable_nat_add_iff 2).2 hconv
  have htail₁ :
      Summable (fun n : ℕ ↦ firstMomentScale (m : ℝ) (convPow m p) (n + 2)) :=
    (summable_nat_add_iff 2).2 hconv₁
  have hscaled := (htail₁.sub htail).mul_left (m : ℝ)⁻¹
  have hstepTail :
      Summable (fun n : ℕ ↦ firstMomentScale (m : ℝ) (drStepProb m p) (n + 1)) := by
    convert hscaled using 1
    funext n
    simp only [firstMomentScale_apply, drStepProb_apply, drStepSeq_succ,
      powerScale_apply]
    have hpow : (m : ℝ) ^ (n + 2) = (m : ℝ) ^ (n + 1) * (m : ℝ) := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    rw [hpow]
    field_simp
    ring
  apply (tiltSummable_one_iff_firstMomentScale_summable m (drStepProb m p)).mpr
  exact (summable_nat_add_iff 1).1 hstepTail

/-- Cross-multiplied first tilted moment after one DR step. -/
theorem tiltedMoment_one_drStepProb_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hzero : TiltSummable m 0 p) (hone : TiltSummable m 1 p) :
    (m : ℝ) * tiltedMoment m 1 (drStepProb m p) =
      (m : ℝ) * tiltedPartition m p ^ (m - 1) * tiltedMoment m 1 p -
        tiltedPartition m p ^ m + p 0 ^ m := by
  have hp : GeneratingSummable (m : ℝ) p :=
    (tiltSummable_zero_iff_generatingSummable m p).mp hzero
  have hpHasSum : HasSum (powerScale (m : ℝ) p) (tiltedPartition m p) := by
    simpa [tiltedPartition_eq_generatingFunction] using
      generatingFunction_hasSum (m : ℝ) p hp
  have hp₁HasSum := firstMomentScale_hasSum_tiltedMoment_one m p hone
  have hconvHasSum :
      HasSum (powerScale (m : ℝ) (convPow m p)) (tiltedPartition m p ^ m) :=
    powerScale_convPow_hasSum m (m : ℝ) p (tiltedPartition m p) hpHasSum
  have hconv₁HasSum :
      HasSum (firstMomentScale (m : ℝ) (convPow m p))
        ((m : ℝ) * tiltedPartition m p ^ (m - 1) * tiltedMoment m 1 p) :=
    firstMomentScale_convPow_hasSum m (m : ℝ) p (tiltedPartition m p)
      (tiltedMoment m 1 p) hpHasSum hp₁HasSum
  have hstepOne := tiltSummable_one_drStepProb m p hm hzero hone
  have hstepHasSum :=
    firstMomentScale_hasSum_tiltedMoment_one m (drStepProb m p) hstepOne
  have hstepTail :
      HasSum (fun n : ℕ ↦ firstMomentScale (m : ℝ) (drStepProb m p) (n + 1))
        (tiltedMoment m 1 (drStepProb m p)) := by
    have h := (hasSum_nat_add_iff' (f := firstMomentScale (m : ℝ) (drStepProb m p)) 1).2
      hstepHasSum
    simpa [firstMomentScale] using h
  have hconvTail :=
    (hasSum_nat_add_iff' (f := powerScale (m : ℝ) (convPow m p)) 2).2 hconvHasSum
  have hconv₁Tail :=
    (hasSum_nat_add_iff' (f := firstMomentScale (m : ℝ) (convPow m p)) 2).2
      hconv₁HasSum
  have hright := hconv₁Tail.sub hconvTail
  have hpoint :
      (fun n : ℕ ↦
        (m : ℝ) * firstMomentScale (m : ℝ) (drStepProb m p) (n + 1)) =
      fun n : ℕ ↦
        firstMomentScale (m : ℝ) (convPow m p) (n + 2) -
          powerScale (m : ℝ) (convPow m p) (n + 2) := by
    funext n
    simp only [firstMomentScale_apply, drStepProb_apply, drStepSeq_succ,
      powerScale_apply]
    have hpow : (m : ℝ) ^ (n + 2) = (m : ℝ) ^ (n + 1) * (m : ℝ) := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    rw [hpow]
    push_cast
    ring
  have hleft :
      HasSum
        (fun n : ℕ ↦
          firstMomentScale (m : ℝ) (convPow m p) (n + 2) -
            powerScale (m : ℝ) (convPow m p) (n + 2))
        ((m : ℝ) * tiltedMoment m 1 (drStepProb m p)) := by
    rw [← hpoint]
    exact hstepTail.mul_left (m : ℝ)
  have heq := hleft.unique hright
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    firstMomentScale_apply, powerScale_apply, Nat.cast_zero, zero_mul,
    Nat.cast_one, one_mul, pow_zero, convPow_apply_zero] at heq
  linarith

/-- Cross-multiplied zeroth tilted moment after one DR step. -/
theorem tiltedPartition_drStepProb_cross
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (hzero : TiltSummable m 0 p) :
    (m : ℝ) * tiltedPartition m (drStepProb m p) =
      tiltedPartition m p ^ m - p 0 ^ m + (m : ℝ) * p 0 ^ m := by
  have hp : GeneratingSummable (m : ℝ) p :=
    (tiltSummable_zero_iff_generatingSummable m p).mp hzero
  have hstepZero := tiltSummable_zero_drStepProb m p hm hzero
  have hstep : GeneratingSummable (m : ℝ) (drStepProb m p) :=
    (tiltSummable_zero_iff_generatingSummable m (drStepProb m p)).mp hstepZero
  simpa only [← tiltedPartition_eq_generatingFunction] using
    generatingFunction_drStep_cross m (m : ℝ) p hp hstep

/-- Both criticality-level tilted summability conditions propagate through `drStepProb`. -/
theorem criticalTiltSummable_drStepProb
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (h : Critical m p) :
    TiltSummable m 0 (drStepProb m p) ∧ TiltSummable m 1 (drStepProb m p) :=
  ⟨tiltSummable_zero_drStepProb m p hm h.1,
    tiltSummable_one_drStepProb m p hm h.1 h.2.1⟩

/-- Criticality is preserved by the coefficient-level Derrida--Retaux step. -/
theorem critical_drStepProb
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (h : Critical m p) :
    Critical m (drStepProb m p) := by
  have hsum := criticalTiltSummable_drStepProb m p hm h
  refine ⟨hsum.1, hsum.2, ?_⟩
  have hzero := tiltedPartition_drStepProb_cross m p hm h.1
  have hone := tiltedMoment_one_drStepProb_cross m p hm h.1 h.2.1
  have hm0Nat : m ≠ 0 := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0Nat
  have hpow :
      tiltedPartition m p ^ (m - 1) * tiltedPartition m p =
        tiltedPartition m p ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hcritical :
      ((m : ℝ) - 1) * tiltedMoment m 1 p = tiltedPartition m p := by
    exact h.2.2
  have hmiddle :
      ((m : ℝ) - 1) *
          ((m : ℝ) * tiltedPartition m p ^ (m - 1) * tiltedMoment m 1 p -
            tiltedPartition m p ^ m + p 0 ^ m) =
        tiltedPartition m p ^ m - p 0 ^ m + (m : ℝ) * p 0 ^ m := by
    calc
      ((m : ℝ) - 1) *
          ((m : ℝ) * tiltedPartition m p ^ (m - 1) * tiltedMoment m 1 p -
            tiltedPartition m p ^ m + p 0 ^ m) =
          (m : ℝ) * tiltedPartition m p ^ (m - 1) *
              (((m : ℝ) - 1) * tiltedMoment m 1 p) -
            ((m : ℝ) - 1) * tiltedPartition m p ^ m +
              ((m : ℝ) - 1) * p 0 ^ m := by ring
      _ = (m : ℝ) * tiltedPartition m p ^ (m - 1) * tiltedPartition m p -
            ((m : ℝ) - 1) * tiltedPartition m p ^ m +
              ((m : ℝ) - 1) * p 0 ^ m := by rw [hcritical]
      _ = tiltedPartition m p ^ m - p 0 ^ m + (m : ℝ) * p 0 ^ m := by
        calc
          (m : ℝ) * tiltedPartition m p ^ (m - 1) * tiltedPartition m p -
                ((m : ℝ) - 1) * tiltedPartition m p ^ m +
              ((m : ℝ) - 1) * p 0 ^ m =
              (m : ℝ) *
                  (tiltedPartition m p ^ (m - 1) * tiltedPartition m p) -
                ((m : ℝ) - 1) * tiltedPartition m p ^ m +
                  ((m : ℝ) - 1) * p 0 ^ m := by ring
          _ = tiltedPartition m p ^ m - p 0 ^ m + (m : ℝ) * p 0 ^ m := by
            rw [hpow]
            ring
  apply mul_left_cancel₀ hm0
  calc
    (m : ℝ) * (((m : ℝ) - 1) * tiltedMoment m 1 (drStepProb m p)) =
        ((m : ℝ) - 1) * ((m : ℝ) * tiltedMoment m 1 (drStepProb m p)) := by
      ring
    _ = ((m : ℝ) - 1) *
        ((m : ℝ) * tiltedPartition m p ^ (m - 1) * tiltedMoment m 1 p -
          tiltedPartition m p ^ m + p 0 ^ m) := by rw [hone]
    _ = tiltedPartition m p ^ m - p 0 ^ m + (m : ℝ) * p 0 ^ m := hmiddle
    _ = (m : ℝ) * tiltedPartition m (drStepProb m p) := hzero.symm

/-- Zeroth tilted summability also propagates through the PMF-backed step `drStep`. -/
theorem tiltSummable_zero_drStep (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (h : TiltSummable m 0 p) :
    TiltSummable m 0 (drStep m p) := by
  rw [drStep_eq_drStepProb]
  exact tiltSummable_zero_drStepProb m p hm h

/-- First tilted summability also propagates through the PMF-backed step `drStep`. -/
theorem tiltSummable_one_drStep (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (hzero : TiltSummable m 0 p) (hone : TiltSummable m 1 p) :
    TiltSummable m 1 (drStep m p) := by
  rw [drStep_eq_drStepProb]
  exact tiltSummable_one_drStepProb m p hm hzero hone

/-- Criticality is preserved by the PMF-backed Derrida--Retaux step. -/
theorem critical_drStep
    (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m) (h : Critical m p) :
    Critical m (drStep m p) := by
  rw [drStep_eq_drStepProb]
  exact critical_drStepProb m p hm h

/-- Every generation of an initially critical orbit is critical. -/
theorem orbit_critical
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (h : Critical m p₀) (n : ℕ) :
    Critical m (orbit m p₀ n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [orbit_succ]
      exact critical_drStep m (orbit m p₀ n) hm ih

/-- Every generation of an initially critical orbit has a finite tilted partition. -/
theorem orbit_tiltSummable_zero
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (h : Critical m p₀) (n : ℕ) :
    TiltSummable m 0 (orbit m p₀ n) :=
  (orbit_critical m p₀ hm h n).1

/-- Every generation of an initially critical orbit has a finite first tilted moment. -/
theorem orbit_tiltSummable_one
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (h : Critical m p₀) (n : ℕ) :
    TiltSummable m 1 (orbit m p₀ n) :=
  (orbit_critical m p₀ hm h n).2.1

/-- The extensionally equal coefficient orbit is critical at every generation as well. -/
theorem coefficientOrbit_critical
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 1 ≤ m) (h : Critical m p₀) (n : ℕ) :
    Critical m (coefficientOrbit m p₀ n) := by
  rw [← orbit_eq_coefficientOrbit]
  exact orbit_critical m p₀ hm h n

end

end DerridaRetaux
