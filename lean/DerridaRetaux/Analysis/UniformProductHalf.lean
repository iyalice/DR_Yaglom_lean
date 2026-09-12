import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

/-- Uniform convergence of a coefficient to `1/2` and a source to `f`
passes to their product on moving finite index windows. -/
theorem eventuallyUniform_mul_tendsto_half_mul
    (lo hi : ℕ → ℕ) (coeff source target : ℕ → ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcoeff : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (lo n) (hi n),
        |coeff n s - (1 : ℝ) / 2| < ε)
    (hsource : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (lo n) (hi n),
        |source n s - target n s| < ε)
    (htargetBound : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (lo n) (hi n), |target n s| ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (lo n) (hi n),
        |coeff n s * source n s - (1 / 2 : ℝ) * target n s| < ε := by
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  have hc := hcoeff (ε / (4 * (C + 1))) (by positivity)
  have hs := hsource (ε / 2) (half_pos hε)
  have hsOne := hsource 1 zero_lt_one
  filter_upwards [hc, hs, hsOne, htargetBound] with n hcn hsn hs1n hbn
  intro s hsMem
  have hcPoint := hcn s hsMem
  have hsPoint := hsn s hsMem
  have hsOnePoint := hs1n s hsMem
  have hbPoint := hbn s hsMem
  have hsourceBound : |source n s| < C + 1 := by
    calc
      |source n s| = |(source n s - target n s) + target n s| := by ring_nf
      _ ≤ |source n s - target n s| + |target n s| := abs_add _ _
      _ < 1 + C := add_lt_add_of_lt_of_le hsOnePoint hbPoint
      _ = C + 1 := add_comm _ _
  rw [show coeff n s * source n s - (1 / 2 : ℝ) * target n s =
    (coeff n s - (1 / 2 : ℝ)) * source n s +
      (1 / 2 : ℝ) * (source n s - target n s) by ring]
  calc
    |(coeff n s - (1 / 2 : ℝ)) * source n s +
        (1 / 2 : ℝ) * (source n s - target n s)| ≤
      |coeff n s - (1 / 2 : ℝ)| * |source n s| +
        (1 / 2 : ℝ) * |source n s - target n s| := by
      calc
        |_ + _| ≤ |(coeff n s - (1 / 2 : ℝ)) * source n s| +
            |(1 / 2 : ℝ) * (source n s - target n s)| := abs_add _ _
        _ = _ := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ < (ε / (4 * (C + 1))) * (C + 1) +
        (1 / 2 : ℝ) * (ε / 2) := by
      apply add_lt_add
      · calc
          |coeff n s - (1 / 2 : ℝ)| * |source n s| ≤
              (ε / (4 * (C + 1))) * |source n s| :=
            mul_le_mul_of_nonneg_right hcPoint.le (abs_nonneg _)
          _ < (ε / (4 * (C + 1))) * (C + 1) :=
            mul_lt_mul_of_pos_left hsourceBound (by positivity)
      · exact mul_lt_mul_of_pos_left hsPoint (by norm_num)
    _ = ε / 2 := by field_simp [hCp.ne']; ring
    _ < ε := half_lt_self hε

end DerridaRetaux
