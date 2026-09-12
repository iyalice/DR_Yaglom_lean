import DerridaRetaux.Basic.Convolution
import DerridaRetaux.Model.Recursion
import Mathlib.Tactic

/-!
# Critical examples and the binary fixed point

This file supplies two non-vacuity gates for the fixed-arity foundation.  First, it proves
that the deterministic binary law `δ₁` is fixed by both the coefficient recursion and the
independent-copy `PMF` recursion.  Second, for every `m ≥ 3`, it constructs an explicit
critical non-Dirac law supported on `{0, 1}` and packages it as profile initial data.
-/

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

private theorem diracSeq_one_eq_shiftRight_zero :
    diracSeq 1 = shiftRight (diracSeq 0) := by
  funext k
  cases k with
  | zero => simp [diracSeq, shiftRight]
  | succ k =>
      cases k with
      | zero => simp [diracSeq, shiftRight]
      | succ k => simp [diracSeq, shiftRight]

private theorem conv_diracSeq_one_one :
    conv (diracSeq 1) (diracSeq 1) = diracSeq 2 := by
  funext n
  cases n with
  | zero => simp [conv, diracSeq]
  | succ k =>
      cases k with
      | zero => norm_num [conv, diracSeq, Finset.sum_range_succ]
      | succ k =>
          rw [diracSeq_one_eq_shiftRight_zero, conv_shiftRight_both,
            conv_diracSeq_zero_left]
          simp [diracSeq]

private theorem convPow_two_diracMass_one :
    convPow 2 (diracMass 1) = diracSeq 2 := by
  simpa [convPow, diracMass_mass_eq_diracSeq] using conv_diracSeq_one_one

private theorem drStepSeq_two_diracMass_one :
    drStepSeq 2 (diracMass 1) = diracSeq 1 := by
  funext k
  cases k with
  | zero =>
      rw [drStepSeq_zero, convPow_two_diracMass_one]
      simp [diracSeq]
  | succ k =>
      rw [drStepSeq_succ, convPow_two_diracMass_one]
      simp [diracSeq]

/-- The binary Dirac law is fixed by the coefficientwise bundled recursion. -/
@[simp]
theorem drStepProb_two_diracMass_one : drStepProb 2 (diracMass 1) = diracMass 1 := by
  apply ProbabilityMass.ext
  intro k
  change drStepSeq 2 (diracMass 1) k = diracMass 1 k
  rw [drStepSeq_two_diracMass_one]
  rfl

/-- Conversion sends a bundled Dirac law to the corresponding mathlib `PMF.pure`. -/
@[simp]
theorem diracMass_toPMF (j : ℕ) : (diracMass j).toPMF = PMF.pure j := by
  apply PMF.ext
  intro k
  by_cases h : k = j <;>
    simp [ProbabilityMass.toPMF_apply_ofReal, diracMass_apply, h]

/-- A sum of independent deterministic inputs is deterministic at the scalar sum. -/
@[simp]
theorem iidSum_pure (r j : ℕ) : iidSum r (PMF.pure j) = PMF.pure (r * j) := by
  induction r with
  | zero =>
      rw [iidSum_zero, zero_mul]
      rfl
  | succ r ih =>
      rw [iidSum_succ, ih]
      change (PMF.pure (r * j)).bind
          (fun previous ↦ (PMF.pure j).map (fun next ↦ previous + next)) =
        PMF.pure ((r + 1) * j)
      rw [PMF.pure_bind, PMF.pure_map]
      rw [Nat.add_mul, one_mul]

/-- The binary deterministic PMF is fixed by the independent-copy law step. -/
@[simp]
theorem lawStep_two_pure_one : lawStep 2 (PMF.pure 1) = PMF.pure 1 := by
  rw [lawStep, iidSum_pure, PMF.pure_map]

/-- The binary Dirac law is fixed by the `PMF`-backed real wrapper. -/
@[simp]
theorem drStep_two_diracMass_one : drStep 2 (diracMass 1) = diracMass 1 := by
  apply (show Function.Injective ProbabilityMass.toPMF by
    intro p q hpq
    simpa using congrArg ProbabilityMass.ofPMF hpq)
  rw [drStep_toPMF, diracMass_toPMF, lawStep_two_pure_one]

/-- Every generation of the coefficient orbit remains at the binary fixed point. -/
@[simp]
theorem coefficientOrbit_two_diracMass_one (n : ℕ) :
    coefficientOrbit 2 (diracMass 1) n = diracMass 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coefficientOrbit_succ, ih]

/-- Every generation of the independent-copy law orbit remains at the binary fixed point. -/
@[simp]
theorem orbit_two_diracMass_one (n : ℕ) : orbit 2 (diracMass 1) n = diracMass 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orbit_succ, ih]

/-- The mass at one in the `{0, 1}` critical family of arity `m`. -/
def zeroOneCriticalMassAtOne (m : ℕ) : ℝ :=
  1 / ((m : ℝ) - 1) ^ 2

/-- The mass at zero in the `{0, 1}` critical family of arity `m`. -/
def zeroOneCriticalMassAtZero (m : ℕ) : ℝ :=
  1 - zeroOneCriticalMassAtOne m

private theorem zeroOneCriticalDenominator_pos (m : ℕ) (hm : 3 ≤ m) :
    0 < ((m : ℝ) - 1) ^ 2 := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  exact pow_pos (by linarith) 2

private theorem one_lt_zeroOneCriticalDenominator (m : ℕ) (hm : 3 ≤ m) :
    1 < ((m : ℝ) - 1) ^ 2 := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith [sq_nonneg ((m : ℝ) - 1)]

theorem zeroOneCriticalMassAtOne_pos (m : ℕ) (hm : 3 ≤ m) :
    0 < zeroOneCriticalMassAtOne m := by
  exact one_div_pos.mpr (zeroOneCriticalDenominator_pos m hm)

theorem zeroOneCriticalMassAtOne_lt_one (m : ℕ) (hm : 3 ≤ m) :
    zeroOneCriticalMassAtOne m < 1 := by
  rw [zeroOneCriticalMassAtOne]
  exact (div_lt_one (zeroOneCriticalDenominator_pos m hm)).mpr
    (one_lt_zeroOneCriticalDenominator m hm)

theorem zeroOneCriticalMassAtZero_pos (m : ℕ) (hm : 3 ≤ m) :
    0 < zeroOneCriticalMassAtZero m := by
  rw [zeroOneCriticalMassAtZero]
  linarith [zeroOneCriticalMassAtOne_lt_one m hm]

theorem zeroOneCriticalMasses_sum (m : ℕ) :
    zeroOneCriticalMassAtZero m + zeroOneCriticalMassAtOne m = 1 := by
  simp [zeroOneCriticalMassAtZero]

/-- For every `m ≥ 3`, the explicit critical law with support `{0, 1}`. -/
def zeroOneCriticalLaw (m : ℕ) (hm : 3 ≤ m) : ProbabilityMass :=
  twoPointMass 1 (zeroOneCriticalMassAtZero m) (zeroOneCriticalMassAtOne m)
    (zeroOneCriticalMassAtZero_pos m hm).le (zeroOneCriticalMassAtOne_pos m hm).le
    (zeroOneCriticalMasses_sum m)

@[simp]
theorem zeroOneCriticalLaw_zero (m : ℕ) (hm : 3 ≤ m) :
    zeroOneCriticalLaw m hm 0 = zeroOneCriticalMassAtZero m := by
  simp [zeroOneCriticalLaw]

@[simp]
theorem zeroOneCriticalLaw_one (m : ℕ) (hm : 3 ≤ m) :
    zeroOneCriticalLaw m hm 1 = zeroOneCriticalMassAtOne m := by
  simp [zeroOneCriticalLaw]

/-- The family has no mass outside `{0, 1}`. -/
theorem zeroOneCriticalLaw_of_ne_zero_of_ne_one (m : ℕ) (hm : 3 ≤ m) (k : ℕ)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) : zeroOneCriticalLaw m hm k = 0 := by
  simp [zeroOneCriticalLaw, hk0, hk1]

/-- Every member of the explicit `{0, 1}` family is critical at its defining arity. -/
theorem zeroOneCriticalLaw_critical (m : ℕ) (hm : 3 ≤ m) :
    Critical m (zeroOneCriticalLaw m hm) := by
  refine ⟨?_, ?_, ?_⟩
  · exact twoPointMass_tiltSummable m 0 1 _ _ _ _ _
  · exact twoPointMass_tiltSummable m 1 1 _ _ _ _ _
  · simp only [zeroOneCriticalLaw]
    rw [tiltedMoment_twoPointMass, tiltedMoment_twoPointMass]
    simp only [zero_pow, Nat.zero_ne_add_one, pow_zero, one_mul, pow_one,
      Nat.cast_one]
    rw [zeroOneCriticalMassAtZero, zeroOneCriticalMassAtOne]
    have hne : (m : ℝ) - 1 ≠ 0 :=
      sq_pos_iff.mp (zeroOneCriticalDenominator_pos m hm)
    field_simp
    ring

/-- Every member of the family is genuinely non-Dirac. -/
theorem zeroOneCriticalLaw_not_isDirac (m : ℕ) (hm : 3 ≤ m) :
    ¬ IsDirac (zeroOneCriticalLaw m hm) := by
  rintro ⟨j, hj⟩
  have hone := congrArg (fun p : ProbabilityMass ↦ p 1) hj
  change zeroOneCriticalLaw m hm 1 = diracMass j 1 at hone
  rw [zeroOneCriticalLaw_one, diracMass_apply] at hone
  by_cases hj1 : 1 = j
  · simp [hj1] at hone
    linarith [zeroOneCriticalMassAtOne_lt_one m hm]
  · simp [hj1] at hone
    linarith [zeroOneCriticalMassAtOne_pos m hm]

/-- The `{0, 1}` family supplies profile-theorem initial data for every `m ≥ 3`. -/
def zeroOneProfileInitialData (m : ℕ) (hm : 3 ≤ m) : ProfileInitialData m where
  arity := by omega
  law := zeroOneCriticalLaw m hm
  critical := zeroOneCriticalLaw_critical m hm
  notBinaryFixedPoint := by
    rintro ⟨hm2, _⟩
    omega
  third := by
    exact twoPointMass_tiltSummable m 3 1 _ _ _ _ _

end

end DerridaRetaux
