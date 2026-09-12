import DerridaRetaux.Model.Tilted

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

/-!
# Elementary properties of tilted partitions and critical products

The lower bound on a tilted partition needs its explicit `TiltSummable` hypothesis:
for a nonsummable real series, Lean's `tsum` is zero.  Product positivity is therefore
proved from tilted summability along precisely the finite orbit prefix used by the
product; no unproved propagation property of the orbit is assumed.
-/

noncomputable section

/-- Zeroth tilted summability is exactly summability of the partition-function series. -/
theorem tiltedPartition_summable (m : ℕ) (p : ProbabilityMass)
    (h : TiltSummable m 0 p) :
    Summable (fun k : ℕ ↦ (m : ℝ) ^ k * p k) := by
  simpa [TiltSummable] using h

/-- The defining partition-function series sums to `tiltedPartition`. -/
theorem tiltedPartition_hasSum (m : ℕ) (p : ProbabilityMass)
    (h : TiltSummable m 0 p) :
    HasSum (fun k : ℕ ↦ (m : ℝ) ^ k * p k) (tiltedPartition m p) := by
  rw [tiltedPartition_eq_tsum]
  exact (tiltedPartition_summable m p h).hasSum

/-- A tilted partition is nonnegative, independently of summability. -/
theorem tiltedPartition_nonneg (m : ℕ) (p : ProbabilityMass) :
    0 ≤ tiltedPartition m p := by
  rw [tiltedPartition_eq_tsum]
  exact tsum_nonneg fun k ↦ mul_nonneg (pow_nonneg (Nat.cast_nonneg m) k) (p.nonneg k)

/-- At arity one the tilted partition is the total probability mass. -/
@[simp]
theorem tiltedPartition_one (p : ProbabilityMass) : tiltedPartition 1 p = 1 := by
  rw [tiltedPartition_eq_tsum]
  simp

/-- A finite tilted partition dominates ordinary total mass when `1 ≤ m`. -/
theorem tiltedPartition_one_le (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (h : TiltSummable m 0 p) :
    1 ≤ tiltedPartition m p := by
  rw [tiltedPartition_eq_tsum, ← p.tsum_eq_one]
  apply p.summable.tsum_le_tsum
  · intro k
    have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    simpa using
      (mul_le_mul_of_nonneg_right (one_le_pow₀ hmReal) (p.nonneg k))
  · exact tiltedPartition_summable m p h

/-- In particular, a finite tilted partition is strictly positive when `1 ≤ m`. -/
theorem tiltedPartition_pos (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (h : TiltSummable m 0 p) :
    0 < tiltedPartition m p :=
  lt_of_lt_of_le zero_lt_one (tiltedPartition_one_le m p hm h)

/-- Criticality supplies the summability needed for the partition lower bound. -/
theorem tiltedPartition_one_le_of_critical (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (h : Critical m p) :
    1 ≤ tiltedPartition m p :=
  tiltedPartition_one_le m p hm h.1

/-- A critical law has positive tilted partition at every arity `m ≥ 1`. -/
theorem tiltedPartition_pos_of_critical (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (h : Critical m p) :
    0 < tiltedPartition m p :=
  tiltedPartition_pos m p hm h.1

/-- Every half-open critical product is nonnegative. -/
theorem criticalProduct_nonneg (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    0 ≤ criticalProduct m p₀ n := by
  rw [criticalProduct]
  exact Finset.prod_nonneg fun j _ ↦
    pow_nonneg (tiltedPartition_nonneg m (orbit m p₀ j)) (m - 1)

/-- Every inclusive critical product is nonnegative. -/
theorem criticalProductInclusive_nonneg (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    0 ≤ criticalProductInclusive m p₀ n := by
  rw [criticalProductInclusive_eq]
  exact criticalProduct_nonneg m p₀ (n + 1)

/-- A half-open product is positive if each partition in its finite prefix is positive. -/
theorem criticalProduct_pos_of_partition_pos (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ)
    (h : ∀ j : ℕ, j < n → 0 < tiltedPartition m (orbit m p₀ j)) :
    0 < criticalProduct m p₀ n := by
  rw [criticalProduct]
  apply Finset.prod_pos
  intro j hj
  exact pow_pos (h j (Finset.mem_range.mp hj)) (m - 1)

/-- Tilted summability on the used prefix makes the half-open product positive. -/
theorem criticalProduct_pos_of_tiltSummable (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ)
    (hm : 1 ≤ m)
    (h : ∀ j : ℕ, j < n → TiltSummable m 0 (orbit m p₀ j)) :
    0 < criticalProduct m p₀ n := by
  apply criticalProduct_pos_of_partition_pos
  intro j hj
  exact tiltedPartition_pos m (orbit m p₀ j) hm (h j hj)

/-- Criticality on the used prefix is a convenient sufficient condition for positivity. -/
theorem criticalProduct_pos_of_critical (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ)
    (hm : 1 ≤ m)
    (h : ∀ j : ℕ, j < n → Critical m (orbit m p₀ j)) :
    0 < criticalProduct m p₀ n := by
  apply criticalProduct_pos_of_tiltSummable m p₀ n hm
  intro j hj
  exact (h j hj).1

/-- An inclusive product is positive if every partition through its endpoint is positive. -/
theorem criticalProductInclusive_pos_of_partition_pos
    (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ)
    (h : ∀ j : ℕ, j ≤ n → 0 < tiltedPartition m (orbit m p₀ j)) :
    0 < criticalProductInclusive m p₀ n := by
  rw [criticalProductInclusive_eq]
  apply criticalProduct_pos_of_partition_pos
  intro j hj
  exact h j (by omega)

/-- Tilted summability through the endpoint makes the inclusive product positive. -/
theorem criticalProductInclusive_pos_of_tiltSummable
    (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) (hm : 1 ≤ m)
    (h : ∀ j : ℕ, j ≤ n → TiltSummable m 0 (orbit m p₀ j)) :
    0 < criticalProductInclusive m p₀ n := by
  apply criticalProductInclusive_pos_of_partition_pos
  intro j hj
  exact tiltedPartition_pos m (orbit m p₀ j) hm (h j hj)

/-- Criticality through the endpoint is a convenient sufficient condition for positivity. -/
theorem criticalProductInclusive_pos_of_critical
    (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) (hm : 1 ≤ m)
    (h : ∀ j : ℕ, j ≤ n → Critical m (orbit m p₀ j)) :
    0 < criticalProductInclusive m p₀ n := by
  apply criticalProductInclusive_pos_of_tiltSummable m p₀ n hm
  intro j hj
  exact (h j hj).1

/-- Reverse orientation of the half-open/inclusive endpoint conversion. -/
theorem criticalProduct_succ_eq_inclusive (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    criticalProduct m p₀ (n + 1) = criticalProductInclusive m p₀ n :=
  (criticalProductInclusive_eq m p₀ n).symm

/-- The inclusive product is the preceding half-open product times its endpoint factor. -/
theorem criticalProductInclusive_eq_mul_endpoint
    (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    criticalProductInclusive m p₀ n =
      criticalProduct m p₀ n * tiltedPartition m (orbit m p₀ n) ^ (m - 1) := by
  rw [criticalProductInclusive_eq, criticalProduct_succ]

/-- Successive inclusive products differ by the new endpoint factor. -/
theorem criticalProductInclusive_succ (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    criticalProductInclusive m p₀ (n + 1) =
      criticalProductInclusive m p₀ n *
        tiltedPartition m (orbit m p₀ (n + 1)) ^ (m - 1) := by
  rw [criticalProductInclusive_eq_mul_endpoint, criticalProductInclusive_eq]

end

end DerridaRetaux
