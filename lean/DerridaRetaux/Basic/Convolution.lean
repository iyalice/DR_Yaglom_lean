import DerridaRetaux.Basic.Sequence
import DerridaRetaux.Basic.ProbabilityMass
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Finite Cauchy convolution and the Derrida--Retaux step

The coefficient-level convolution is defined by a finite `Finset.range` sum.  We
connect it both to `Finset.antidiagonal` for reindexing and to mathlib's absolutely
summable Cauchy-product theorem.  All probability-law outputs are bundled only after
nonnegativity and total-mass preservation have been proved.
-/

/-- The finite Cauchy coefficient of two real sequences. -/
def conv (a b : Seq) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- The unbundled Dirac sequence at `j`. -/
def diracSeq (j : ℕ) : Seq :=
  fun k : ℕ ↦ if k = j then 1 else 0

/-- Iterated convolution, with the zeroth power fixed to `δ₀`. -/
def convPow : ℕ → Seq → Seq
  | 0, _ => diracSeq 0
  | r + 1, a => conv (convPow r a) a

@[simp]
theorem conv_apply (a b : Seq) (n : ℕ) :
    conv a b n = ∑ k ∈ Finset.range (n + 1), a k * b (n - k) :=
  rfl

@[simp]
theorem diracSeq_apply (j k : ℕ) : diracSeq j k = if k = j then 1 else 0 :=
  rfl

@[simp]
theorem convPow_zero (a : Seq) : convPow 0 a = diracSeq 0 :=
  rfl

@[simp]
theorem convPow_succ (r : ℕ) (a : Seq) :
    convPow (r + 1) a = conv (convPow r a) a :=
  rfl

/-- Range and antidiagonal presentations of a Cauchy coefficient agree. -/
theorem conv_eq_sum_antidiagonal (a b : Seq) (n : ℕ) :
    conv a b n =
      ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := by
  simpa [conv, Nat.succ_eq_add_one] using
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l ↦ a k * b l) n).symm

/-- Turning a sequence into a formal power series sends convolution to multiplication. -/
theorem powerSeries_mk_conv (a b : Seq) :
    PowerSeries.mk (conv a b) = PowerSeries.mk a * PowerSeries.mk b := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  exact conv_eq_sum_antidiagonal a b n

/-- Convolution is commutative. -/
theorem conv_comm (a b : Seq) : conv a b = conv b a := by
  funext n
  have hseries :
      PowerSeries.mk (conv a b) = PowerSeries.mk (conv b a) := by
    rw [powerSeries_mk_conv, powerSeries_mk_conv, mul_comm]
  have hcoeff := congrArg (fun s ↦ PowerSeries.coeff ℝ n s) hseries
  simpa using hcoeff

/-- Convolution is associative. -/
theorem conv_assoc (a b c : Seq) : conv (conv a b) c = conv a (conv b c) := by
  funext n
  have hseries :
      PowerSeries.mk (conv (conv a b) c) =
        PowerSeries.mk (conv a (conv b c)) := by
    simp only [powerSeries_mk_conv, mul_assoc]
  have hcoeff := congrArg (fun s ↦ PowerSeries.coeff ℝ n s) hseries
  simpa using hcoeff

/-- The zeroth Cauchy coefficient is the product of the zeroth coefficients. -/
@[simp]
theorem conv_zero (a b : Seq) : conv a b 0 = a 0 * b 0 := by
  simp [conv]

/-- Peeling the left input gives a useful successor-coefficient identity. -/
theorem conv_succ_left (a b : Seq) (n : ℕ) :
    conv a b (n + 1) = a 0 * b (n + 1) + conv (shiftLeft a) b n := by
  simp only [conv_eq_sum_antidiagonal, Finset.Nat.sum_antidiagonal_succ,
    shiftLeft_apply]

/-- Peeling the right input gives the symmetric successor-coefficient identity. -/
theorem conv_succ_right (a b : Seq) (n : ℕ) :
    conv a b (n + 1) = a (n + 1) * b 0 + conv a (shiftLeft b) n := by
  simp only [conv_eq_sum_antidiagonal, Finset.Nat.sum_antidiagonal_succ',
    shiftLeft_apply]

/-- Right-shifting the left input shifts its convolution by one coefficient. -/
@[simp]
theorem conv_shiftRight_left_zero (a b : Seq) : conv (shiftRight a) b 0 = 0 := by
  simp

/-- Right-shifting the left input shifts its convolution by one coefficient. -/
theorem conv_shiftRight_left_succ (a b : Seq) (n : ℕ) :
    conv (shiftRight a) b (n + 1) = conv a b n := by
  simp only [conv_eq_sum_antidiagonal, Finset.Nat.sum_antidiagonal_succ,
    shiftRight_zero, zero_mul, zero_add, shiftRight_succ]

/-- Right-shifting the right input shifts its convolution by one coefficient. -/
@[simp]
theorem conv_shiftRight_right_zero (a b : Seq) : conv a (shiftRight b) 0 = 0 := by
  simp

/-- Right-shifting the right input shifts its convolution by one coefficient. -/
theorem conv_shiftRight_right_succ (a b : Seq) (n : ℕ) :
    conv a (shiftRight b) (n + 1) = conv a b n := by
  simp only [conv_eq_sum_antidiagonal, Finset.Nat.sum_antidiagonal_succ',
    shiftRight_zero, mul_zero, zero_add, shiftRight_succ]

/-- Shifting both inputs shifts their convolution by two coefficients. -/
theorem conv_shiftRight_both (a b : Seq) (n : ℕ) :
    conv (shiftRight a) (shiftRight b) (n + 2) = conv a b n := by
  rw [show n + 2 = (n + 1) + 1 by omega, conv_shiftRight_left_succ,
    conv_shiftRight_right_succ]

/-- The Dirac sequence at zero is a left convolution identity. -/
@[simp]
theorem conv_diracSeq_zero_left (a : Seq) : conv (diracSeq 0) a = a := by
  funext n
  simp [conv, diracSeq]

/-- The Dirac sequence at zero is a right convolution identity. -/
@[simp]
theorem conv_diracSeq_zero_right (a : Seq) : conv a (diracSeq 0) = a := by
  rw [conv_comm, conv_diracSeq_zero_left]

/-- The zero sequence annihilates convolution on the left. -/
@[simp]
theorem conv_zero_left (a : Seq) : conv (fun _ : ℕ ↦ 0) a = 0 := by
  funext n
  simp [conv]

/-- The zero sequence annihilates convolution on the right. -/
@[simp]
theorem conv_zero_right (a : Seq) : conv a (fun _ : ℕ ↦ 0) = 0 := by
  funext n
  simp [conv]

/-- Convolution preserves pointwise nonnegativity. -/
theorem conv_nonneg (a b : Seq) (ha : ∀ k : ℕ, 0 ≤ a k)
    (hb : ∀ k : ℕ, 0 ≤ b k) (n : ℕ) : 0 ≤ conv a b n := by
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (ha k) (hb (n - k))

/-- Cauchy products of real `HasSum` sequences have the product sum.

Lean's `HasSum` is unconditional; for real sequences it therefore supplies the absolute
summability required by mathlib's Cauchy-product theorem.
-/
theorem conv_hasSum (a b : Seq) (A B : ℝ) (ha : HasSum a A) (hb : HasSum b B) :
    HasSum (conv a b) (A * B) := by
  have hproduct :=
    hasSum_sum_range_mul_of_summable_norm ha.summable.norm hb.summable.norm
  simpa [conv, ha.tsum_eq, hb.tsum_eq] using hproduct

/-- Convolution of two summable real sequences is summable. -/
theorem conv_summable (a b : Seq) (ha : Summable a) (hb : Summable b) :
    Summable (conv a b) :=
  (conv_hasSum a b (∑' k : ℕ, a k) (∑' k : ℕ, b k) ha.hasSum hb.hasSum).summable

/-- Evaluation of the total sum of a convolution. -/
theorem tsum_conv (a b : Seq) (ha : Summable a) (hb : Summable b) :
    ∑' n : ℕ, conv a b n = (∑' k : ℕ, a k) * ∑' k : ℕ, b k :=
  (conv_hasSum a b (∑' k : ℕ, a k) (∑' k : ℕ, b k) ha.hasSum hb.hasSum).tsum_eq

/-- The unbundled Dirac sequence has total mass one. -/
theorem diracSeq_hasSum_one (j : ℕ) : HasSum (diracSeq j) 1 := by
  simpa [diracSeq] using hasSum_ite_eq j (1 : ℝ)

/-- The unbundled Dirac sequence is summable. -/
theorem diracSeq_summable (j : ℕ) : Summable (diracSeq j) :=
  (diracSeq_hasSum_one j).summable

/-- The bundled and unbundled Dirac mass functions agree. -/
theorem diracMass_mass_eq_diracSeq (j : ℕ) : (diracMass j).mass = diracSeq j :=
  rfl

/-- Convolution powers preserve pointwise nonnegativity. -/
theorem convPow_nonneg (r : ℕ) (a : Seq) (ha : ∀ k : ℕ, 0 ≤ a k)
    (n : ℕ) : 0 ≤ convPow r a n := by
  induction r generalizing n with
  | zero =>
      by_cases hn : n = 0 <;> simp [convPow, diracSeq, hn]
  | succ r ih =>
      exact conv_nonneg (convPow r a) a ih ha n

/-- The total sum of a convolution power is the corresponding scalar power. -/
theorem convPow_hasSum (r : ℕ) (a : Seq) (A : ℝ) (ha : HasSum a A) :
    HasSum (convPow r a) (A ^ r) := by
  induction r with
  | zero =>
      simpa [convPow] using diracSeq_hasSum_one 0
  | succ r ih =>
      simpa [convPow, pow_succ] using conv_hasSum (convPow r a) a (A ^ r) A ih ha

/-- A convolution power of a summable sequence is summable, including power zero. -/
theorem convPow_summable (r : ℕ) (a : Seq) (ha : Summable a) :
    Summable (convPow r a) :=
  (convPow_hasSum r a (∑' k : ℕ, a k) ha.hasSum).summable

/-- A mass-one sequence has mass-one convolution powers. -/
theorem convPow_hasSum_one (r : ℕ) (a : Seq) (ha : HasSum a 1) :
    HasSum (convPow r a) 1 := by
  simpa using convPow_hasSum r a 1 ha

/-- The first convolution power is the original sequence. -/
@[simp]
theorem convPow_one (a : Seq) : convPow 1 a = a := by
  simp [convPow]

/-- Convolution powers add their exponents. -/
theorem convPow_add (r s : ℕ) (a : Seq) :
    convPow (r + s) a = conv (convPow r a) (convPow s a) := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.add_succ, convPow_succ, ih, convPow_succ, conv_assoc]

/-- Convolution of bundled probability masses. -/
def convProb (p q : ProbabilityMass) : ProbabilityMass where
  mass := conv p q
  nonneg := conv_nonneg p q p.nonneg q.nonneg
  hasSum_one := by
    simpa using conv_hasSum p q 1 1 p.hasSum_coe q.hasSum_coe

@[simp]
theorem convProb_apply (p q : ProbabilityMass) (n : ℕ) :
    convProb p q n = conv p q n :=
  rfl

/-- Bundled convolution is commutative. -/
theorem convProb_comm (p q : ProbabilityMass) : convProb p q = convProb q p := by
  ext n
  exact congrFun (conv_comm p q) n

/-- Bundled convolution is associative. -/
theorem convProb_assoc (p q r : ProbabilityMass) :
    convProb (convProb p q) r = convProb p (convProb q r) := by
  ext n
  exact congrFun (conv_assoc p q r) n

/-- The bundled Dirac mass at zero is a left convolution identity. -/
@[simp]
theorem convProb_diracMass_zero_left (p : ProbabilityMass) :
    convProb (diracMass 0) p = p := by
  ext n
  exact congrFun (conv_diracSeq_zero_left p) n

/-- The bundled Dirac mass at zero is a right convolution identity. -/
@[simp]
theorem convProb_diracMass_zero_right (p : ProbabilityMass) :
    convProb p (diracMass 0) = p := by
  ext n
  exact congrFun (conv_diracSeq_zero_right p) n

/-- Bundled convolution powers. -/
def convPowProb (r : ℕ) (p : ProbabilityMass) : ProbabilityMass where
  mass := convPow r p
  nonneg := convPow_nonneg r p p.nonneg
  hasSum_one := convPow_hasSum_one r p p.hasSum_coe

@[simp]
theorem convPowProb_apply (r : ℕ) (p : ProbabilityMass) (n : ℕ) :
    convPowProb r p n = convPow r p n :=
  rfl

/-- The zeroth bundled convolution power is `δ₀`. -/
@[simp]
theorem convPowProb_zero (p : ProbabilityMass) : convPowProb 0 p = diracMass 0 := by
  ext n
  rfl

/-- Bundled convolution powers satisfy the successor recursion. -/
theorem convPowProb_succ (r : ℕ) (p : ProbabilityMass) :
    convPowProb (r + 1) p = convProb (convPowProb r p) p := by
  ext n
  rfl

/-- Merge the zeroth and first coefficients and shift the remaining coefficients down.
This operation preserves any real total sum. -/
theorem hasSum_mergeFirstTwo (a : Seq) (A : ℝ) (ha : HasSum a A) :
    HasSum (fun
      | 0 => a 0 + a 1
      | k + 1 => a (k + 2)) A := by
  let merged : Seq := fun
    | 0 => a 0 + a 1
    | k + 1 => a (k + 2)
  have htail : HasSum (fun n : ℕ ↦ a (n + 2)) (A - (a 0 + a 1)) := by
    simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' (f := a) 2).2 ha
  have hmergedTail :
      HasSum (fun n : ℕ ↦ merged (n + 1)) (A - (a 0 + a 1)) := by
    simpa [merged] using htail
  have hmerged := (hasSum_nat_add_iff (f := merged) 1).1 hmergedTail
  simpa [merged] using hmerged

/-- The coefficient form of one Derrida--Retaux step. -/
def drStepSeq (m : ℕ) (p : Seq) : Seq
  | 0 => convPow m p 0 + convPow m p 1
  | k + 1 => convPow m p (k + 2)

@[simp]
theorem drStepSeq_zero (m : ℕ) (p : Seq) :
    drStepSeq m p 0 = convPow m p 0 + convPow m p 1 :=
  rfl

@[simp]
theorem drStepSeq_succ (m : ℕ) (p : Seq) (k : ℕ) :
    drStepSeq m p (k + 1) = convPow m p (k + 2) :=
  rfl

/-- The arity-zero edge case reduces to `δ₀`, independently of the input. -/
theorem drStepSeq_arity_zero (p : Seq) : drStepSeq 0 p = diracSeq 0 := by
  funext n
  cases n with
  | zero => simp [drStepSeq, convPow, diracSeq]
  | succ k => simp [drStepSeq, convPow, diracSeq]

/-- The Derrida--Retaux step preserves pointwise nonnegativity. -/
theorem drStepSeq_nonneg (m : ℕ) (p : Seq) (hp : ∀ k : ℕ, 0 ≤ p k)
    (n : ℕ) : 0 ≤ drStepSeq m p n := by
  cases n with
  | zero =>
      exact add_nonneg (convPow_nonneg m p hp 0) (convPow_nonneg m p hp 1)
  | succ k =>
      exact convPow_nonneg m p hp (k + 2)

/-- The Derrida--Retaux step sends a sequence of total sum `A` to one of sum `A ^ m`. -/
theorem drStepSeq_hasSum (m : ℕ) (p : Seq) (A : ℝ) (hp : HasSum p A) :
    HasSum (drStepSeq m p) (A ^ m) := by
  simpa [drStepSeq] using
    hasSum_mergeFirstTwo (convPow m p) (A ^ m) (convPow_hasSum m p A hp)

/-- In particular, the Derrida--Retaux step preserves total mass one. -/
theorem drStepSeq_hasSum_one (m : ℕ) (p : ProbabilityMass) :
    HasSum (drStepSeq m p) 1 := by
  simpa using drStepSeq_hasSum m p 1 p.hasSum_coe

/-- The bundled Derrida--Retaux evolution step. -/
def drStepProb (m : ℕ) (p : ProbabilityMass) : ProbabilityMass where
  mass := drStepSeq m p
  nonneg := drStepSeq_nonneg m p p.nonneg
  hasSum_one := drStepSeq_hasSum_one m p

@[simp]
theorem drStepProb_apply (m : ℕ) (p : ProbabilityMass) (k : ℕ) :
    drStepProb m p k = drStepSeq m p k :=
  rfl

/-- The bundled arity-zero step is the Dirac law at zero. -/
theorem drStepProb_arity_zero (p : ProbabilityMass) : drStepProb 0 p = diracMass 0 := by
  ext n
  change drStepSeq 0 p n = diracMass 0 n
  rw [drStepSeq_arity_zero]
  rfl

/-- The coefficient-level orbit under `drStepProb`.

The paper-facing recursion module reserves the shorter name `orbit` for its PMF-bridged
law recursion.
-/
def coefficientOrbit (m : ℕ) (p : ProbabilityMass) (n : ℕ) : ProbabilityMass :=
  (drStepProb m)^[n] p

@[simp]
theorem coefficientOrbit_zero (m : ℕ) (p : ProbabilityMass) :
    coefficientOrbit m p 0 = p :=
  rfl

@[simp]
theorem coefficientOrbit_succ (m : ℕ) (p : ProbabilityMass) (n : ℕ) :
    coefficientOrbit m p (n + 1) = drStepProb m (coefficientOrbit m p n) := by
  simpa [coefficientOrbit] using Function.iterate_succ_apply' (drStepProb m) n p

end DerridaRetaux
