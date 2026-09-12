import DerridaRetaux.Basic.Sequence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Probability masses and tilted moments

This file bundles nonnegative real sequences of total mass one.  It also fixes the
summability predicates and tilted moments used throughout the Derrida--Retaux
formalization.  The definitions are transparent: conclusions about criticality or
nondegeneracy are proved as theorems rather than stored as structure fields.
-/

/-- A probability law on `ℕ`, represented by its real-valued mass function. -/
structure ProbabilityMass where
  mass : Seq
  nonneg : ∀ k : ℕ, 0 ≤ mass k
  hasSum_one : HasSum mass 1

instance : CoeFun ProbabilityMass (fun _ ↦ ℕ → ℝ) :=
  ⟨ProbabilityMass.mass⟩

@[ext]
theorem ProbabilityMass.ext {p q : ProbabilityMass}
    (h : ∀ k : ℕ, p k = q k) : p = q := by
  cases p with
  | mk pmass pnonneg phasSum =>
      cases q with
      | mk qmass qnonneg qhasSum =>
          have hmass : pmass = qmass := funext h
          subst qmass
          rfl

/-- The coerced mass function has sum one. -/
theorem ProbabilityMass.hasSum_coe (p : ProbabilityMass) :
    HasSum (fun k : ℕ ↦ p k) 1 :=
  p.hasSum_one

/-- Every bundled probability mass is summable. -/
theorem ProbabilityMass.summable (p : ProbabilityMass) :
    Summable (fun k : ℕ ↦ p k) :=
  p.hasSum_coe.summable

/-- The `tsum` of a bundled probability mass is one. -/
@[simp]
theorem ProbabilityMass.tsum_eq_one (p : ProbabilityMass) :
    ∑' k : ℕ, p k = 1 :=
  p.hasSum_coe.tsum_eq

/-- Each atom of a probability mass lies below one. -/
theorem ProbabilityMass.apply_le_one (p : ProbabilityMass) (j : ℕ) : p j ≤ 1 := by
  have hle := p.summable.sum_le_tsum {j} (fun k _ ↦ p.nonneg k)
  simpa using hle

/-- The Dirac probability mass at `j`. -/
def diracMass (j : ℕ) : ProbabilityMass where
  mass := fun k : ℕ ↦ if k = j then 1 else 0
  nonneg := by
    intro k
    split_ifs <;> norm_num
  hasSum_one := by
    simpa using hasSum_ite_eq j (1 : ℝ)

@[simp]
theorem diracMass_apply (j k : ℕ) :
    diracMass j k = if k = j then 1 else 0 :=
  rfl

@[simp]
theorem diracMass_same (j : ℕ) : diracMass j j = 1 := by
  simp

@[simp]
theorem diracMass_of_ne (j k : ℕ) (h : k ≠ j) : diracMass j k = 0 := by
  simp [h]

/-- A probability mass is deterministic exactly when it is a Dirac mass. -/
def IsDirac (p : ProbabilityMass) : Prop :=
  ∃ k : ℕ, p = diracMass k

@[simp]
theorem isDirac_diracMass (j : ℕ) : IsDirac (diracMass j) :=
  ⟨j, rfl⟩

/-- Explicit finiteness of the `r`-th integer tilted moment. -/
def TiltSummable (m r : ℕ) (p : ProbabilityMass) : Prop :=
  Summable (fun k : ℕ ↦ (k : ℝ) ^ r * (m : ℝ) ^ k * p k)

/-- The `r`-th integer tilted moment.  Its evaluation requires `TiltSummable`. -/
def tiltedMoment (m r : ℕ) (p : ProbabilityMass) : ℝ :=
  ∑' k : ℕ, (k : ℝ) ^ r * (m : ℝ) ^ k * p k

/-- The real-power convention used by the sharpness theorem.

In particular, the value at `r = 0, k = 0` is fixed to be one.
-/
def realMomentWeight (r : ℝ) (k : ℕ) : ℝ :=
  if r = 0 then 1 else Real.rpow (k : ℝ) r

/-- Explicit finiteness of a real-order tilted moment. -/
def RealTiltSummable (m : ℕ) (r : ℝ) (p : ProbabilityMass) : Prop :=
  Summable (fun k : ℕ ↦ realMomentWeight r k * (m : ℝ) ^ k * p k)

@[simp]
theorem realMomentWeight_zero (k : ℕ) : realMomentWeight 0 k = 1 := by
  simp [realMomentWeight]

theorem realMomentWeight_of_ne_zero (r : ℝ) (k : ℕ) (hr : r ≠ 0) :
    realMomentWeight r k = Real.rpow (k : ℝ) r := by
  simp [realMomentWeight, hr]

theorem realMomentWeight_nonneg (r : ℝ) (k : ℕ) : 0 ≤ realMomentWeight r k := by
  by_cases hr : r = 0
  · simp [realMomentWeight, hr]
  · rw [realMomentWeight_of_ne_zero r k hr]
    exact Real.rpow_nonneg (Nat.cast_nonneg k) r

/-- A supplied `HasSum` computes the corresponding tilted moment. -/
theorem tiltedMoment_eq_of_hasSum (m r : ℕ) (p : ProbabilityMass) (a : ℝ)
    (h : HasSum (fun k : ℕ ↦ (k : ℝ) ^ r * (m : ℝ) ^ k * p k) a) :
    tiltedMoment m r p = a :=
  h.tsum_eq

/-- Tilted weights of a Dirac mass have their evident one-term sum. -/
theorem diracMass_tilted_hasSum (m r j : ℕ) :
    HasSum (fun k : ℕ ↦ (k : ℝ) ^ r * (m : ℝ) ^ k * diracMass j k)
      ((j : ℝ) ^ r * (m : ℝ) ^ j) := by
  convert hasSum_ite_eq j ((j : ℝ) ^ r * (m : ℝ) ^ j) using 1
  funext k
  by_cases hk : k = j
  · subst k
    simp
  · simp [hk]

/-- Every integer tilted moment of a Dirac mass is summable. -/
theorem diracMass_tiltSummable (m r j : ℕ) : TiltSummable m r (diracMass j) :=
  (diracMass_tilted_hasSum m r j).summable

/-- Evaluation of a Dirac integer tilted moment. -/
@[simp]
theorem tiltedMoment_diracMass (m r j : ℕ) :
    tiltedMoment m r (diracMass j) = (j : ℝ) ^ r * (m : ℝ) ^ j :=
  (diracMass_tilted_hasSum m r j).tsum_eq

/-- Real-order tilted weights of a Dirac mass have a one-term sum. -/
theorem diracMass_realTilted_hasSum (m j : ℕ) (r : ℝ) :
    HasSum
      (fun k : ℕ ↦ realMomentWeight r k * (m : ℝ) ^ k * diracMass j k)
      (realMomentWeight r j * (m : ℝ) ^ j) := by
  convert hasSum_ite_eq j (realMomentWeight r j * (m : ℝ) ^ j) using 1
  funext k
  by_cases hk : k = j
  · subst k
    simp
  · simp [hk]

/-- Every real-order tilted moment of a Dirac mass is summable. -/
theorem diracMass_realTiltSummable (m j : ℕ) (r : ℝ) :
    RealTiltSummable m r (diracMass j) :=
  (diracMass_realTilted_hasSum m j r).summable

/-- Criticality is literal equality of the zeroth and first finite tilted series. -/
def Critical (m : ℕ) (p : ProbabilityMass) : Prop :=
  TiltSummable m 0 p ∧
    TiltSummable m 1 p ∧
      ((m : ℝ) - 1) * tiltedMoment m 1 p = tiltedMoment m 0 p

/-- Initial data for conclusions that do not require a third tilted moment. -/
structure CriticalInitialData (m : ℕ) where
  arity : 2 ≤ m
  law : ProbabilityMass
  critical : Critical m law
  notBinaryFixedPoint : ¬ (m = 2 ∧ law = diracMass 1)

/-- Initial data for the profile theorem, including its third tilted moment. -/
structure ProfileInitialData (m : ℕ) extends CriticalInitialData m where
  third : TiltSummable m 3 law

/-- The binary deterministic fixed point is critical. -/
theorem critical_two_diracMass_one : Critical 2 (diracMass 1) := by
  refine ⟨diracMass_tiltSummable 2 0 1, diracMass_tiltSummable 2 1 1, ?_⟩
  norm_num

/-- At arity zero, `δ₁` is also critical; this is the counterexample motivating the
arity hypothesis in `critical_isDirac_eq_binary`. -/
theorem critical_zero_diracMass_one : Critical 0 (diracMass 1) := by
  refine ⟨diracMass_tiltSummable 0 0 1, diracMass_tiltSummable 0 1 1, ?_⟩
  norm_num

/-- Classification of deterministic critical laws at admissible arity.

This corrects `LEAN_ARCHITECTURE.md` §1, lines 78--79: the hypothesis
`hm : 2 ≤ m` is necessary, since `m = 0` with `δ₁` is a counterexample.
-/
theorem critical_isDirac_eq_binary (m : ℕ) (p : ProbabilityMass) (hm : 2 ≤ m)
    (hcritical : Critical m p) (hdirac : IsDirac p) :
    m = 2 ∧ p = diracMass 1 := by
  rcases hdirac with ⟨j, rfl⟩
  have heq := hcritical.2.2
  rw [tiltedMoment_diracMass, tiltedMoment_diracMass] at heq
  simp only [pow_one, pow_zero, one_mul] at heq
  have hmposNat : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmposNat
  have hpow : (m : ℝ) ^ j ≠ 0 := ne_of_gt (pow_pos hmpos j)
  have hfactor : ((m : ℝ) - 1) * (j : ℝ) = 1 := by
    apply mul_right_cancel₀ hpow
    simpa [mul_assoc] using heq
  have hmone : 1 ≤ m := by omega
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hmone, Nat.cast_one]
  rw [← hcast] at hfactor
  have hnat : (m - 1) * j = 1 := by
    exact_mod_cast hfactor
  have hparts : m - 1 = 1 ∧ j = 1 := mul_eq_one.mp hnat
  constructor
  · omega
  · rw [hparts.2]

/-- A two-point probability mass, supported on `{0, j}`.  Coincident points are
allowed; their weights then add. -/
def twoPointMass (j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : ProbabilityMass where
  mass := fun k : ℕ ↦ (if k = 0 then a else 0) + if k = j then b else 0
  nonneg := by
    intro k
    split_ifs <;> linarith
  hasSum_one := by
    simpa only [hab] using
      (hasSum_ite_eq 0 a).add (hasSum_ite_eq j b)

@[simp]
theorem twoPointMass_apply (j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (k : ℕ) :
    twoPointMass j a b ha hb hab k =
      (if k = 0 then a else 0) + if k = j then b else 0 :=
  rfl

/-- A weighted two-point mass is an explicitly summable finite-support sequence. -/
theorem twoPointMass_weighted_hasSum (j : ℕ) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) (f : ℕ → ℝ) :
    HasSum (fun k : ℕ ↦ f k * twoPointMass j a b ha hb hab k)
      (f 0 * a + f j * b) := by
  convert (hasSum_ite_eq 0 (f 0 * a)).add (hasSum_ite_eq j (f j * b)) using 1
  funext k
  by_cases hk0 : k = 0
  · subst k
    by_cases h0j : 0 = j
    · simp [h0j]
      ring
    · simp [h0j]
  · by_cases hkj : k = j
    · subst k
      simp [hk0]
    · simp [hk0, hkj]

/-- Every integer tilted moment of a two-point mass is summable. -/
theorem twoPointMass_tiltSummable (m r j : ℕ) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    TiltSummable m r (twoPointMass j a b ha hb hab) :=
  (twoPointMass_weighted_hasSum j a b ha hb hab
    (fun k : ℕ ↦ (k : ℝ) ^ r * (m : ℝ) ^ k)).summable

/-- Evaluation of an integer tilted moment for a two-point mass. -/
theorem tiltedMoment_twoPointMass (m r j : ℕ) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    tiltedMoment m r (twoPointMass j a b ha hb hab) =
      (0 : ℝ) ^ r * (m : ℝ) ^ 0 * a +
        (j : ℝ) ^ r * (m : ℝ) ^ j * b :=
  by
    unfold tiltedMoment
    simpa only [Nat.cast_zero] using
      (twoPointMass_weighted_hasSum j a b ha hb hab
        (fun k : ℕ ↦ (k : ℝ) ^ r * (m : ℝ) ^ k)).tsum_eq

/-- Every real-order tilted moment of a two-point mass is summable. -/
theorem twoPointMass_realTiltSummable (m j : ℕ) (r a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    RealTiltSummable m r (twoPointMass j a b ha hb hab) :=
  (twoPointMass_weighted_hasSum j a b ha hb hab
    (fun k : ℕ ↦ realMomentWeight r k * (m : ℝ) ^ k)).summable

/-- The required binary smoke-test law: mass `4/5` at zero and `1/5` at two. -/
def binaryCriticalLaw : ProbabilityMass :=
  twoPointMass 2 (4 / 5) (1 / 5) (by norm_num) (by norm_num) (by norm_num)

@[simp]
theorem binaryCriticalLaw_zero : binaryCriticalLaw 0 = 4 / 5 := by
  norm_num [binaryCriticalLaw]

@[simp]
theorem binaryCriticalLaw_two : binaryCriticalLaw 2 = 1 / 5 := by
  norm_num [binaryCriticalLaw]

/-- The binary smoke-test law is critical. -/
theorem binaryCriticalLaw_critical : Critical 2 binaryCriticalLaw := by
  refine
    ⟨twoPointMass_tiltSummable 2 0 2 (4 / 5) (1 / 5) (by norm_num) (by norm_num)
        (by norm_num),
      twoPointMass_tiltSummable 2 1 2 (4 / 5) (1 / 5) (by norm_num) (by norm_num)
        (by norm_num), ?_⟩
  norm_num [binaryCriticalLaw, tiltedMoment_twoPointMass]

/-- The binary smoke-test law is genuinely non-Dirac. -/
theorem binaryCriticalLaw_not_isDirac : ¬ IsDirac binaryCriticalLaw := by
  rintro ⟨j, hj⟩
  have hzero := congrArg (fun p : ProbabilityMass ↦ p 0) hj
  change binaryCriticalLaw 0 = diracMass j 0 at hzero
  rw [binaryCriticalLaw_zero, diracMass_apply] at hzero
  split_ifs at hzero <;> norm_num at hzero

/-- The required ternary smoke-test law: mass `3/4` at zero and `1/4` at one. -/
def ternaryCriticalLaw : ProbabilityMass :=
  twoPointMass 1 (3 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num)

@[simp]
theorem ternaryCriticalLaw_zero : ternaryCriticalLaw 0 = 3 / 4 := by
  norm_num [ternaryCriticalLaw]

@[simp]
theorem ternaryCriticalLaw_one : ternaryCriticalLaw 1 = 1 / 4 := by
  norm_num [ternaryCriticalLaw]

/-- The ternary smoke-test law is critical. -/
theorem ternaryCriticalLaw_critical : Critical 3 ternaryCriticalLaw := by
  refine
    ⟨twoPointMass_tiltSummable 3 0 1 (3 / 4) (1 / 4) (by norm_num) (by norm_num)
        (by norm_num),
      twoPointMass_tiltSummable 3 1 1 (3 / 4) (1 / 4) (by norm_num) (by norm_num)
        (by norm_num), ?_⟩
  norm_num [ternaryCriticalLaw, tiltedMoment_twoPointMass]

/-- The ternary smoke-test law is genuinely non-Dirac. -/
theorem ternaryCriticalLaw_not_isDirac : ¬ IsDirac ternaryCriticalLaw := by
  rintro ⟨j, hj⟩
  have hzero := congrArg (fun p : ProbabilityMass ↦ p 0) hj
  change ternaryCriticalLaw 0 = diracMass j 0 at hzero
  rw [ternaryCriticalLaw_zero, diracMass_apply] at hzero
  split_ifs at hzero <;> norm_num at hzero

/-- The binary smoke-test law satisfies the profile initial-data interface. -/
def binaryProfileInitialData : ProfileInitialData 2 where
  arity := by norm_num
  law := binaryCriticalLaw
  critical := binaryCriticalLaw_critical
  notBinaryFixedPoint := by
    rintro ⟨_, hfixed⟩
    exact binaryCriticalLaw_not_isDirac ⟨1, hfixed⟩
  third := by
    exact twoPointMass_tiltSummable 2 3 2 (4 / 5) (1 / 5) (by norm_num)
      (by norm_num) (by norm_num)

/-- The ternary smoke-test law satisfies the profile initial-data interface and remains
admitted despite being supported on `{0, 1}`. -/
def ternaryProfileInitialData : ProfileInitialData 3 where
  arity := by norm_num
  law := ternaryCriticalLaw
  critical := ternaryCriticalLaw_critical
  notBinaryFixedPoint := by norm_num
  third := by
    exact twoPointMass_tiltSummable 3 3 1 (3 / 4) (1 / 4) (by norm_num)
      (by norm_num) (by norm_num)

end

end DerridaRetaux
