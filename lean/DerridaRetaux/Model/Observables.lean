import DerridaRetaux.Model.TiltedProperties

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-!
# Basic orbit observables

These are the scalar quantities in source equation `eq:notation`.  Survival is kept
as the literal positive-atom sum and then identified with `1 - p(0)`.
-/

/-- The tilted excess `G(p) - 1`. -/
def excess (m : ℕ) (p : ProbabilityMass) : ℝ :=
  tiltedPartition m p - 1

/-- The total mass on strictly positive integers. -/
def survival (p : ProbabilityMass) : ℝ :=
  ∑' k : ℕ, p (k + 1)

theorem survival_hasSum (p : ProbabilityMass) :
    HasSum (fun k : ℕ ↦ p (k + 1)) (survival p) := by
  exact ((summable_nat_add_iff 1).2 p.summable).hasSum

theorem survival_eq_one_sub_zero (p : ProbabilityMass) :
    survival p = 1 - p 0 := by
  have h := p.summable.tsum_eq_zero_add
  rw [p.tsum_eq_one] at h
  change 1 = p 0 + survival p at h
  linarith

theorem survival_nonneg (p : ProbabilityMass) : 0 ≤ survival p := by
  rw [survival]
  exact tsum_nonneg fun k ↦ p.nonneg (k + 1)

theorem survival_le_one (p : ProbabilityMass) : survival p ≤ 1 := by
  rw [survival_eq_one_sub_zero]
  linarith [p.nonneg 0]

theorem excess_add_one (m : ℕ) (p : ProbabilityMass) :
    excess m p + 1 = tiltedPartition m p := by
  simp [excess]

theorem excess_nonneg (m : ℕ) (p : ProbabilityMass) (hm : 1 ≤ m)
    (h : TiltSummable m 0 p) :
    0 ≤ excess m p := by
  rw [excess]
  linarith [tiltedPartition_one_le m p hm h]

@[simp]
theorem excess_one (p : ProbabilityMass) : excess 1 p = 0 := by
  simp [excess]

end

end DerridaRetaux
