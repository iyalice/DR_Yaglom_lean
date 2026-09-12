import DerridaRetaux.Model.Recursion

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-!
# Tilted partition functions and critical products

This file freezes the source-facing quantities shared by the CDHLS and Chen--Shi
interfaces.  The product `criticalProduct m p₀ n` is half-open: its indices are
exactly `0, ..., n - 1`.
-/

/-- The tilted partition function `G(p) = sum_k m^k p(k)`. -/
def tiltedPartition (m : ℕ) (p : ProbabilityMass) : ℝ :=
  tiltedMoment m 0 p

theorem tiltedPartition_eq_tsum (m : ℕ) (p : ProbabilityMass) :
    tiltedPartition m p = ∑' k : ℕ, (m : ℝ) ^ k * p k := by
  simp [tiltedPartition, tiltedMoment]

/-- The half-open critical product `prod_{0 <= j < n} G_j^(m-1)`. -/
def criticalProduct (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, tiltedPartition m (orbit m p₀ j) ^ (m - 1)

/-- The inclusive critical product through generation `n`. -/
def criticalProductInclusive (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (n + 1), tiltedPartition m (orbit m p₀ j) ^ (m - 1)

@[simp]
theorem criticalProduct_zero (m : ℕ) (p₀ : ProbabilityMass) :
    criticalProduct m p₀ 0 = 1 := by
  simp [criticalProduct]

theorem criticalProduct_succ (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    criticalProduct m p₀ (n + 1) =
      criticalProduct m p₀ n * tiltedPartition m (orbit m p₀ n) ^ (m - 1) := by
  simp [criticalProduct, Finset.prod_range_succ]

theorem criticalProductInclusive_eq (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    criticalProductInclusive m p₀ n = criticalProduct m p₀ (n + 1) := by
  rfl

end

end DerridaRetaux
