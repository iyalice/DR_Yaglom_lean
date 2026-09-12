import DerridaRetaux.Prelim.AtomTail
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Abel summation for the first tilted atom tail

This file instantiates the generic square-weight summation-by-parts identity
with the exact tail from `lem:atomtail`, completing unnumbered obligation `U26`.
-/

/-- The tail is the current first tilted atom plus the next tail. -/
theorem firstTiltedAtomTail_eq_atom_add_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (n : ℕ) :
    firstTiltedAtomTail m p₀ n =
      firstTiltedAtom m p₀ n + firstTiltedAtomTail m p₀ (n + 1) := by
  have hs := firstTiltedAtom_summable
    m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess
  rw [firstTiltedAtomTail, firstTiltedAtomTail]
  calc
    (∑' j : ℕ, firstTiltedAtom m p₀ (n + j)) =
        firstTiltedAtom m p₀ n +
          ∑' j : ℕ, firstTiltedAtom m p₀ (n + (j + 1)) :=
      tsum_nat_add_eq_self_add_succ (firstTiltedAtom m p₀) hs n
    _ = firstTiltedAtom m p₀ n +
          ∑' j : ℕ, firstTiltedAtom m p₀ (n + 1 + j) := by
      congr 1
      apply tsum_congr
      intro j
      exact congrArg (firstTiltedAtom m p₀) (by omega)

/-- The first tilted atom is the forward difference of its exact tail. -/
theorem firstTiltedAtom_eq_discreteDerivative_tail
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (n : ℕ) :
    firstTiltedAtom m p₀ n =
      discreteDerivative (firstTiltedAtomTail m p₀) n := by
  rw [discreteDerivative_apply]
  have htail := firstTiltedAtomTail_eq_atom_add_succ
    m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess n
  linarith

/-- Literal source Abel identity with endpoint `s`. -/
theorem firstTiltedAtom_squareWeight_sum_eq
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (s : ℕ) (hs : 0 < s) :
    ∑ v ∈ Finset.range s,
        ((v + 1 : ℕ) : ℝ) ^ 2 * firstTiltedAtom m p₀ v =
      firstTiltedAtomTail m p₀ 0 +
        ∑ v ∈ Finset.Ico 1 s,
          ((2 * v + 1 : ℕ) : ℝ) * firstTiltedAtomTail m p₀ v -
        (s : ℝ) ^ 2 * firstTiltedAtomTail m p₀ s := by
  exact squareWeightSummationByParts_source
    (firstTiltedAtom m p₀) (firstTiltedAtomTail m p₀) s hs
      (firstTiltedAtom_eq_discreteDerivative_tail
        m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess)

/-- Source-shaped `O(s+1)` bound for the square-weighted first atoms. -/
theorem firstTiltedAtom_squareWeight_sum_linear_bound
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1))
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ,
      ∑ v ∈ Finset.range s,
          ((v + 1 : ℕ) : ℝ) ^ 2 * firstTiltedAtom m p₀ v ≤
        C * ((s + 1 : ℕ) : ℝ) := by
  rcases firstTiltedAtomTail_bound_all
      m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess with
    ⟨A, hA, htail⟩
  refine ⟨2 * A, mul_pos (by norm_num) hA, ?_⟩
  intro s
  cases s with
  | zero => simpa using hA.le
  | succ n =>
      have hbound := squareWeightSum_le
        (firstTiltedAtom m p₀) (firstTiltedAtomTail m p₀) n A
        (firstTiltedAtom_eq_discreteDerivative_tail
          m p₀ hm hcrit hthird hnonconstant hnotBinaryFixedPoint hExcess)
        hA.le (fun k ↦ (htail k).1) (fun k ↦ (htail k).2)
      calc
        ∑ v ∈ Finset.range (n + 1),
            ((v + 1 : ℕ) : ℝ) ^ 2 * firstTiltedAtom m p₀ v ≤
          A + 2 * A * n := hbound
        _ ≤ (2 * A) * (((n + 1) + 1 : ℕ) : ℝ) := by
          push_cast
          nlinarith

end

end DerridaRetaux
