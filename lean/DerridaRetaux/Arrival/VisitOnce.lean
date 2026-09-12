import DerridaRetaux.Prelim.FarTail
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Visit-once control for the initial arrival source

The initial-source contribution in the arrival Duhamel formula is sampled at
the indices `N - 1, ..., N + s - 2`.  This file records that these indices are
distinct and bounds the finite block by the single nonnegative coefficient tail
beginning at `N - 1`.  It is the visit-once part of source obligation `U25`.
-/

/-- Once `N` is positive, the arrival index `N + j - 1` is just a fixed shift
of `j`.  In particular, the initial source cannot visit one coefficient twice. -/
theorem arrivalInitialIndex_strictMono (N : ℕ) (hN : 1 ≤ N) :
    StrictMono (fun j : ℕ ↦ N + j - 1) := by
  intro i j hij
  change N + i - 1 < N + j - 1
  omega

theorem arrivalInitialIndex_injective (N : ℕ) (hN : 1 ≤ N) :
    Function.Injective (fun j : ℕ ↦ N + j - 1) :=
  (arrivalInitialIndex_strictMono N hN).injective

/-- Exact finite interchange for the triangular source-difference sum
`sum_{j<s} sum_{v<j}`.  Keeping this step finite prevents an unjustified
infinite-sum interchange in the far-arrival argument. -/
theorem sum_range_sum_range_triangle
    (f : ℕ → ℕ → ℝ) (s : ℕ) :
    (∑ j ∈ Finset.range s, ∑ v ∈ Finset.range j, f v j) =
      ∑ v ∈ Finset.range s, ∑ j ∈ Finset.Ico (v + 1) s, f v j := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      have hvs : v + 1 ≤ s := by
        exact Finset.mem_range.mp hv
      rw [Finset.sum_Ico_succ_top hvs]

/-- The finite initial-source block in `eq:arrivalDuhamel` is controlled by one
ordinary coefficient tail.  No absolute-value estimate or sum interchange is
hidden here: the coefficients are explicitly assumed nonnegative and summable. -/
theorem arrivalInitialBlock_le_coefficientTail
    (a : Seq) (ha : ∀ k : ℕ, 0 ≤ a k) (hsum : Summable a)
    (N s : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range s, a (N + j - 1)) ≤ coefficientTail a (N - 1) := by
  have hindex : ∀ j : ℕ, N + j - 1 = j + (N - 1) := by
    intro j
    omega
  have htail : Summable (fun j : ℕ ↦ a (j + (N - 1))) :=
    (summable_nat_add_iff (N - 1)).2 hsum
  simp_rw [hindex]
  rw [coefficientTail]
  exact htail.sum_le_tsum (Finset.range s) (fun j _ ↦ ha (j + (N - 1)))

/-- A cubically summable nonnegative source automatically satisfies the
visit-once tail bound used in the manuscript. -/
theorem arrivalInitialBlock_le_coefficientTail_of_cubic
    (a : Seq) (ha : ∀ k : ℕ, 0 ≤ a k)
    (hthree : Summable (fun k : ℕ ↦ (k : ℝ) ^ 3 * a k))
    (N s : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range s, a (N + j - 1)) ≤ coefficientTail a (N - 1) := by
  exact arrivalInitialBlock_le_coefficientTail a ha
    (summable_of_summable_nat_cube a ha hthree) N s hN

end

end DerridaRetaux
