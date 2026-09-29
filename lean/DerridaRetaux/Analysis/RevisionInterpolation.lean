import DerridaRetaux.Analysis.GridInterpolation

set_option autoImplicit false

namespace DerridaRetaux

/-- A convex combination preserves a common absolute bound. -/
theorem abs_convex_pair_le (a b w C : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1)
    (ha : |a| ≤ C) (hb : |b| ≤ C) :
    |(1 - w) * a + w * b| ≤ C := by
  calc
    _ ≤ |(1 - w) * a| + |w * b| := abs_add_le _ _
    _ = (1 - w) * |a| + w * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hw₁), abs_of_nonneg hw₀]
    _ ≤ (1 - w) * C + w * C := add_le_add
      (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hw₁))
      (mul_le_mul_of_nonneg_left hb hw₀)
    _ = C := by ring

/-- Space-coordinate estimate inside a closed interpolation cell, including its edges. -/
theorem bilinearInterp_space_cell_bound
    (a : ℕ → ℕ → ℝ) (n j : ℕ) (t x y C : ℝ)
    (ht : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1))
    (hx : x ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1))
    (hy : y ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1))
    (h₀ : |a n (j + 1) - a n j| ≤ C)
    (h₁ : |a (n + 1) (j + 1) - a (n + 1) j| ≤ C) :
    |bilinearInterp a t x - bilinearInterp a t y| ≤ C * |x - y| := by
  rw [bilinearInterp_eq_on_cell a n j t x ht hx,
    bilinearInterp_eq_on_cell a n j t y ht hy]
  have heq :
      (1 - (t - n)) * ((1 - (x - j)) * a n j + (x - j) * a n (j + 1)) +
        (t - n) * ((1 - (x - j)) * a (n + 1) j + (x - j) * a (n + 1) (j + 1)) -
      ((1 - (t - n)) * ((1 - (y - j)) * a n j + (y - j) * a n (j + 1)) +
        (t - n) * ((1 - (y - j)) * a (n + 1) j + (y - j) * a (n + 1) (j + 1))) =
      (x - y) * ((1 - (t - n)) * (a n (j + 1) - a n j) +
        (t - n) * (a (n + 1) (j + 1) - a (n + 1) j)) := by ring
  rw [heq, abs_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left
    (abs_convex_pair_le _ _ _ _ (by linarith [ht.1]) (by linarith [ht.2]) h₀ h₁)
    (abs_nonneg _)

/-- Bilinear interpolation commutes with exchanging the two coordinates. -/
theorem bilinearInterp_transpose (a : ℕ → ℕ → ℝ) (t x : ℝ) :
    bilinearInterp (fun j n ↦ a n j) x t = bilinearInterp a t x := by
  simp only [bilinearInterp, linInterp]
  ring

/-- Time-coordinate estimate inside a closed interpolation cell. -/
theorem bilinearInterp_time_cell_bound
    (a : ℕ → ℕ → ℝ) (n j : ℕ) (t s x C : ℝ)
    (ht : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1))
    (hs : s ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1))
    (hx : x ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1))
    (h₀ : |a (n + 1) j - a n j| ≤ C)
    (h₁ : |a (n + 1) (j + 1) - a n (j + 1)| ≤ C) :
    |bilinearInterp a t x - bilinearInterp a s x| ≤ C * |t - s| := by
  simpa only [bilinearInterp_transpose] using
    bilinearInterp_space_cell_bound (fun j n ↦ a n j) j n x t s C hx ht hs h₀ h₁

/-- Physical-grid form of the spatial cell bound, used in `eq:space diff`.
An adjacent-node bound of order `(1 + log N) / N` becomes a cell Lipschitz bound
of order `1 + log N`. -/
theorem gridBilinearInterp_space_cell_bound
    (N : ℕ) (a : ℕ → ℕ → ℝ) (n j : ℕ) (t x y C : ℝ) (hN : 0 < N)
    (ht : (N : ℝ) * t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1))
    (hx : (N : ℝ) * x ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1))
    (hy : (N : ℝ) * y ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1))
    (h₀ : |a n (j + 1) - a n j| ≤ C / (N : ℝ))
    (h₁ : |a (n + 1) (j + 1) - a (n + 1) j| ≤ C / (N : ℝ)) :
    |gridBilinearInterp N a t x - gridBilinearInterp N a t y| ≤ C * |x - y| := by
  rw [gridBilinearInterp_of_pos N a t x hN, gridBilinearInterp_of_pos N a t y hN]
  have h := bilinearInterp_space_cell_bound a n j _ _ _ (C / (N : ℝ)) ht hx hy h₀ h₁
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simpa only [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ)),
    ← mul_assoc, div_mul_cancel₀ _ hNr] using h

/-- Physical-grid form of the temporal cell bound, used in `eq:time diff`. -/
theorem gridBilinearInterp_time_cell_bound
    (N : ℕ) (a : ℕ → ℕ → ℝ) (n j : ℕ) (t s x C : ℝ) (hN : 0 < N)
    (ht : (N : ℝ) * t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1))
    (hs : (N : ℝ) * s ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1))
    (hx : (N : ℝ) * x ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1))
    (h₀ : |a (n + 1) j - a n j| ≤ C / (N : ℝ))
    (h₁ : |a (n + 1) (j + 1) - a n (j + 1)| ≤ C / (N : ℝ)) :
    |gridBilinearInterp N a t x - gridBilinearInterp N a s x| ≤ C * |t - s| := by
  rw [gridBilinearInterp_of_pos N a t x hN, gridBilinearInterp_of_pos N a s x hN]
  have h := bilinearInterp_time_cell_bound a n j _ _ _ (C / (N : ℝ)) ht hs hx h₀ h₁
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simpa only [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ)),
    ← mul_assoc, div_mul_cancel₀ _ hNr] using h

end DerridaRetaux
