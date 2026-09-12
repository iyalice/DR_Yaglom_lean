import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Grid arithmetic and interpolation

This file isolates natural-floor arithmetic and the elementary interpolation layer used by the
rescaled Derrida--Retaux profiles.  It contains no compactness or profile-identification claim.
-/

namespace DerridaRetaux

noncomputable section

/-- The left endpoint of the mesh cell of size `1 / N` containing `x`, with negative inputs
clamped to the boundary cell. -/
def gridIndex (N : ℕ) (x : ℝ) : ℕ :=
  ⌊(N : ℝ) * max x 0⌋₊

/-- The fractional coordinate of `x` in its mesh cell. -/
def gridFrac (N : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * max x 0 - gridIndex N x

@[simp]
theorem gridIndex_zero_scale (x : ℝ) : gridIndex 0 x = 0 := by
  simp [gridIndex]

@[simp]
theorem gridFrac_zero_scale (x : ℝ) : gridFrac 0 x = 0 := by
  simp [gridFrac]

@[simp]
theorem gridIndex_at_zero (N : ℕ) : gridIndex N 0 = 0 := by
  simp [gridIndex]

@[simp]
theorem gridFrac_at_zero (N : ℕ) : gridFrac N 0 = 0 := by
  simp [gridFrac]

theorem gridIndex_cast_le_max (N : ℕ) (x : ℝ) :
    (gridIndex N x : ℝ) ≤ (N : ℝ) * max x 0 := by
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (le_max_right x 0))

theorem mul_max_lt_gridIndex_add_one (N : ℕ) (x : ℝ) :
    (N : ℝ) * max x 0 < (gridIndex N x : ℝ) + 1 := by
  simpa [gridIndex] using Nat.lt_floor_add_one ((N : ℝ) * max x 0)

theorem gridIndex_cast_le (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (gridIndex N x : ℝ) ≤ (N : ℝ) * x := by
  simpa [max_eq_left hx] using gridIndex_cast_le_max N x

theorem mul_lt_gridIndex_add_one (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (N : ℝ) * x < (gridIndex N x : ℝ) + 1 := by
  simpa [max_eq_left hx] using mul_max_lt_gridIndex_add_one N x

/-- The natural floor bracket, stated once with all casts exposed. -/
theorem gridIndex_bracket (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (gridIndex N x : ℝ) ≤ (N : ℝ) * x ∧
      (N : ℝ) * x < (gridIndex N x : ℝ) + 1 :=
  ⟨gridIndex_cast_le N x hx, mul_lt_gridIndex_add_one N x hx⟩

theorem gridFrac_nonneg (N : ℕ) (x : ℝ) : 0 ≤ gridFrac N x := by
  exact sub_nonneg.mpr (gridIndex_cast_le_max N x)

theorem gridFrac_lt_one (N : ℕ) (x : ℝ) : gridFrac N x < 1 := by
  have h := mul_max_lt_gridIndex_add_one N x
  simp only [gridFrac]
  linarith

theorem gridFrac_mem_Ico (N : ℕ) (x : ℝ) : gridFrac N x ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨gridFrac_nonneg N x, gridFrac_lt_one N x⟩

theorem gridFrac_le_one (N : ℕ) (x : ℝ) : gridFrac N x ≤ 1 :=
  (gridFrac_lt_one N x).le

theorem one_sub_gridFrac_nonneg (N : ℕ) (x : ℝ) : 0 ≤ 1 - gridFrac N x :=
  sub_nonneg.mpr (gridFrac_le_one N x)

theorem gridFrac_add_index (N : ℕ) (x : ℝ) :
    gridFrac N x + gridIndex N x = (N : ℝ) * max x 0 := by
  simp [gridFrac]

theorem gridFrac_eq_of_nonneg (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    gridFrac N x = (N : ℝ) * x - gridIndex N x := by
  simp [gridFrac, max_eq_left hx]

/-- The mesh-cell bracket after division by the positive scale. -/
theorem gridCell_bracket (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    (gridIndex N x : ℝ) / (N : ℝ) ≤ x ∧
      x < ((gridIndex N x : ℕ) + 1 : ℕ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · rw [div_le_iff₀ hNR]
    simpa [mul_comm] using gridIndex_cast_le N x hx
  · rw [lt_div_iff₀ hNR]
    simpa [mul_comm, Nat.cast_add, Nat.cast_one] using mul_lt_gridIndex_add_one N x hx

theorem gridOffset_eq_frac_div (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    x - (gridIndex N x : ℝ) / (N : ℝ) = gridFrac N x / (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [gridFrac_eq_of_nonneg N x hx]
  field_simp
  ring

theorem gridOffset_nonneg (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    0 ≤ x - (gridIndex N x : ℝ) / (N : ℝ) := by
  rw [gridOffset_eq_frac_div N x hN hx]
  exact div_nonneg (gridFrac_nonneg N x) (Nat.cast_nonneg N)

theorem gridOffset_lt_inv (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    x - (gridIndex N x : ℝ) / (N : ℝ) < 1 / (N : ℝ) := by
  rw [gridOffset_eq_frac_div N x hN hx]
  exact div_lt_div_of_pos_right (gridFrac_lt_one N x) (by exact_mod_cast hN)

theorem gridPoint_add_frac_div (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    (gridIndex N x : ℝ) / (N : ℝ) + gridFrac N x / (N : ℝ) = x := by
  linarith [gridOffset_eq_frac_div N x hN hx]

theorem gridConvexCoordinates (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    (1 - gridFrac N x) * ((gridIndex N x : ℝ) / (N : ℝ)) +
        gridFrac N x * (((gridIndex N x + 1 : ℕ) : ℝ) / (N : ℝ)) = x := by
  calc
    (1 - gridFrac N x) * ((gridIndex N x : ℝ) / (N : ℝ)) +
        gridFrac N x * (((gridIndex N x + 1 : ℕ) : ℝ) / (N : ℝ)) =
        (gridIndex N x : ℝ) / (N : ℝ) + gridFrac N x / (N : ℝ) := by
          push_cast
          ring
    _ = x := gridPoint_add_frac_div N x hN hx

theorem abs_gridOffset_lt_inv (N : ℕ) (x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) :
    |x - (gridIndex N x : ℝ) / (N : ℝ)| < 1 / (N : ℝ) := by
  rw [abs_of_nonneg (gridOffset_nonneg N x hN hx)]
  exact gridOffset_lt_inv N x hN hx

/-- A physical mesh node has exactly the expected natural floor index. -/
@[simp]
theorem gridIndex_at_node (N j : ℕ) (hN : 0 < N) :
    gridIndex N ((j : ℝ) / (N : ℝ)) = j := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx : 0 ≤ (j : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg j) hNR.le
  have hscale : (N : ℝ) * ((j : ℝ) / (N : ℝ)) = j := by
    field_simp
  simp [gridIndex, max_eq_left hx, hscale]

/-- The fractional coordinate vanishes exactly at every physical mesh node. -/
@[simp]
theorem gridFrac_at_node (N j : ℕ) (hN : 0 < N) :
    gridFrac N ((j : ℝ) / (N : ℝ)) = 0 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx : 0 ≤ (j : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg j) hNR.le
  have hscale : (N : ℝ) * ((j : ℝ) / (N : ℝ)) = j := by
    field_simp
  simp [gridFrac, max_eq_left hx, hscale, gridIndex_at_node N j hN]

/-- Piecewise-linear interpolation of a real sequence, extended constantly to negative inputs. -/
def linInterp (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  (1 - gridFrac 1 y) * a (gridIndex 1 y) +
    gridFrac 1 y * a (gridIndex 1 y + 1)

theorem linInterp_eq_weighted_neighbors (a : ℕ → ℝ) (y : ℝ) :
    linInterp a y =
      (1 - gridFrac 1 y) * a (gridIndex 1 y) +
        gridFrac 1 y * a (gridIndex 1 y + 1) :=
  rfl

theorem linInterp_weights_nonneg (y : ℝ) :
    0 ≤ 1 - gridFrac 1 y ∧ 0 ≤ gridFrac 1 y :=
  ⟨one_sub_gridFrac_nonneg 1 y, gridFrac_nonneg 1 y⟩

theorem linInterp_weights_sum (y : ℝ) : (1 - gridFrac 1 y) + gridFrac 1 y = 1 := by
  ring

@[simp]
theorem linInterp_of_nonpos (a : ℕ → ℝ) (y : ℝ) (hy : y ≤ 0) : linInterp a y = a 0 := by
  simp [linInterp, gridFrac, gridIndex, max_eq_right hy]

@[simp]
theorem linInterp_at_zero (a : ℕ → ℝ) : linInterp a 0 = a 0 := by
  exact linInterp_of_nonpos a 0 le_rfl

@[simp]
theorem linInterp_at_nat (a : ℕ → ℝ) (j : ℕ) : linInterp a (j : ℝ) = a j := by
  have hindex : gridIndex 1 (j : ℝ) = j := by
    simpa using gridIndex_at_node 1 j Nat.zero_lt_one
  have hfrac : gridFrac 1 (j : ℝ) = 0 := by
    simpa using gridFrac_at_node 1 j Nat.zero_lt_one
  simp [linInterp, hindex, hfrac]

/-- On a closed unit cell, the floor formula agrees with its affine polynomial even at the
right endpoint. -/
theorem linInterp_eq_on_Icc (a : ℕ → ℝ) (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    linInterp a y =
      (1 - (y - n)) * a n + (y - n) * a (n + 1) := by
  have hy0 : 0 ≤ y := (Nat.cast_nonneg n).trans hy.1
  rcases hy.2.lt_or_eq with hyn | hyn
  · have hindex : gridIndex 1 y = n := by
      simp only [gridIndex, max_eq_left hy0, Nat.cast_one, one_mul]
      exact (Nat.floor_eq_iff hy0).2 ⟨hy.1, hyn⟩
    have hfrac : gridFrac 1 y = y - n := by
      rw [gridFrac_eq_of_nonneg 1 y hy0, hindex]
      norm_num
    simp [linInterp, hindex, hfrac]
  · have hy_node : y = (n + 1 : ℕ) := by
      exact hyn.trans (by norm_num)
    rw [hy_node, linInterp_at_nat]
    norm_num

theorem linInterp_nonneg (a : ℕ → ℝ) (ha : ∀ j : ℕ, 0 ≤ a j) (y : ℝ) :
    0 ≤ linInterp a y := by
  exact add_nonneg
    (mul_nonneg (one_sub_gridFrac_nonneg 1 y) (ha (gridIndex 1 y)))
    (mul_nonneg (gridFrac_nonneg 1 y) (ha (gridIndex 1 y + 1)))

theorem linInterp_le_max_neighbors (a : ℕ → ℝ) (y : ℝ) :
    linInterp a y ≤ max (a (gridIndex 1 y)) (a (gridIndex 1 y + 1)) := by
  let M := max (a (gridIndex 1 y)) (a (gridIndex 1 y + 1))
  calc
    linInterp a y ≤ (1 - gridFrac 1 y) * M + gridFrac 1 y * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (one_sub_gridFrac_nonneg 1 y))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (gridFrac_nonneg 1 y))
    _ = M := by ring

theorem min_neighbors_le_linInterp (a : ℕ → ℝ) (y : ℝ) :
    min (a (gridIndex 1 y)) (a (gridIndex 1 y + 1)) ≤ linInterp a y := by
  let m := min (a (gridIndex 1 y)) (a (gridIndex 1 y + 1))
  calc
    m = (1 - gridFrac 1 y) * m + gridFrac 1 y * m := by ring
    _ ≤ linInterp a y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (one_sub_gridFrac_nonneg 1 y))
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (gridFrac_nonneg 1 y))

theorem abs_linInterp_le_max_abs_neighbors (a : ℕ → ℝ) (y : ℝ) :
    |linInterp a y| ≤ max |a (gridIndex 1 y)| |a (gridIndex 1 y + 1)| := by
  let M := max |a (gridIndex 1 y)| |a (gridIndex 1 y + 1)|
  calc
    |linInterp a y| ≤
        |(1 - gridFrac 1 y) * a (gridIndex 1 y)| +
          |gridFrac 1 y * a (gridIndex 1 y + 1)| := abs_add_le _ _
    _ = (1 - gridFrac 1 y) * |a (gridIndex 1 y)| +
          gridFrac 1 y * |a (gridIndex 1 y + 1)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (one_sub_gridFrac_nonneg 1 y),
        abs_of_nonneg (gridFrac_nonneg 1 y)]
    _ ≤ (1 - gridFrac 1 y) * M + gridFrac 1 y * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (one_sub_gridFrac_nonneg 1 y))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (gridFrac_nonneg 1 y))
    _ = M := by ring

theorem linInterp_sub_left_neighbor (a : ℕ → ℝ) (y : ℝ) :
    linInterp a y - a (gridIndex 1 y) =
      gridFrac 1 y * (a (gridIndex 1 y + 1) - a (gridIndex 1 y)) := by
  simp only [linInterp]
  ring

theorem abs_linInterp_sub_left_neighbor (a : ℕ → ℝ) (y : ℝ) :
    |linInterp a y - a (gridIndex 1 y)| =
      gridFrac 1 y * |a (gridIndex 1 y + 1) - a (gridIndex 1 y)| := by
  rw [linInterp_sub_left_neighbor, abs_mul, abs_of_nonneg (gridFrac_nonneg 1 y)]

theorem abs_linInterp_sub_left_neighbor_le (a : ℕ → ℝ) (y : ℝ) :
    |linInterp a y - a (gridIndex 1 y)| ≤
      |a (gridIndex 1 y + 1) - a (gridIndex 1 y)| := by
  rw [abs_linInterp_sub_left_neighbor]
  exact mul_le_of_le_one_left (abs_nonneg _) (gridFrac_le_one 1 y)

private theorem locallyFinite_natUnitCells :
    LocallyFinite (fun n : ℕ ↦ Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
  intro x
  refine ⟨Set.Iio (x + 1), Iio_mem_nhds (lt_add_one x), ?_⟩
  refine (Set.finite_le_nat ⌊max (x + 1) 0⌋₊).subset ?_
  intro n hn
  rcases hn with ⟨y, hy, hyx⟩
  have hnlt : (n : ℝ) < x + 1 := hy.1.trans_lt hyx
  apply Nat.le_floor
  exact hnlt.le.trans (le_max_left (x + 1) 0)

private theorem iUnion_natUnitCells :
    (⋃ n : ℕ, Set.Icc (n : ℝ) ((n : ℝ) + 1)) = Set.Ici (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    exact (Nat.cast_nonneg n).trans hn.1
  · intro hx
    refine Set.mem_iUnion.2 ⟨⌊x⌋₊, ?_⟩
    exact ⟨Nat.floor_le hx, (Nat.lt_floor_add_one x).le⟩

theorem continuousOn_linInterp_cell (a : ℕ → ℝ) (n : ℕ) :
    ContinuousOn (linInterp a) (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
  have hpoly : Continuous (fun y : ℝ ↦
      (1 - (y - n)) * a n + (y - n) * a (n + 1)) := by
    fun_prop
  exact hpoly.continuousOn.congr (fun y hy ↦ linInterp_eq_on_Icc a n y hy)

theorem continuousOn_linInterp_Ici (a : ℕ → ℝ) :
    ContinuousOn (linInterp a) (Set.Ici (0 : ℝ)) := by
  rw [← iUnion_natUnitCells]
  exact locallyFinite_natUnitCells.continuousOn_iUnion
    (fun _ ↦ isClosed_Icc) (continuousOn_linInterp_cell a)

@[simp]
theorem linInterp_max_zero (a : ℕ → ℝ) (y : ℝ) :
    linInterp a (max y 0) = linInterp a y := by
  simp [linInterp, gridIndex, gridFrac, max_eq_left (le_max_right y 0)]

/-- Linear interpolation is globally continuous, including every natural grid boundary and the
clamped boundary at zero. -/
theorem continuous_linInterp (a : ℕ → ℝ) : Continuous (linInterp a) := by
  have hmax : Continuous (fun y : ℝ ↦ max y 0) := continuous_id.max continuous_const
  have hcomp := (continuousOn_linInterp_Ici a).comp_continuous hmax
    (fun y ↦ le_max_right y 0)
  simpa [Function.comp_def] using hcomp

/-- Bilinear interpolation, performed first in space and then in time. -/
def bilinearInterp (a : ℕ → ℕ → ℝ) (t x : ℝ) : ℝ :=
  linInterp (fun n ↦ linInterp (a n) x) t

def bilinearWeight00 (t x : ℝ) : ℝ :=
  (1 - gridFrac 1 t) * (1 - gridFrac 1 x)

def bilinearWeight01 (t x : ℝ) : ℝ :=
  (1 - gridFrac 1 t) * gridFrac 1 x

def bilinearWeight10 (t x : ℝ) : ℝ :=
  gridFrac 1 t * (1 - gridFrac 1 x)

def bilinearWeight11 (t x : ℝ) : ℝ :=
  gridFrac 1 t * gridFrac 1 x

theorem bilinearWeights_nonneg (t x : ℝ) :
    0 ≤ bilinearWeight00 t x ∧
      0 ≤ bilinearWeight01 t x ∧
      0 ≤ bilinearWeight10 t x ∧
      0 ≤ bilinearWeight11 t x := by
  exact ⟨
    mul_nonneg (one_sub_gridFrac_nonneg 1 t) (one_sub_gridFrac_nonneg 1 x),
    mul_nonneg (one_sub_gridFrac_nonneg 1 t) (gridFrac_nonneg 1 x),
    mul_nonneg (gridFrac_nonneg 1 t) (one_sub_gridFrac_nonneg 1 x),
    mul_nonneg (gridFrac_nonneg 1 t) (gridFrac_nonneg 1 x)⟩

theorem bilinearWeights_sum (t x : ℝ) :
    bilinearWeight00 t x + bilinearWeight01 t x +
      bilinearWeight10 t x + bilinearWeight11 t x = 1 := by
  simp only [bilinearWeight00, bilinearWeight01, bilinearWeight10, bilinearWeight11]
  ring

theorem bilinearInterp_eq_four_weights (a : ℕ → ℕ → ℝ) (t x : ℝ) :
    bilinearInterp a t x =
      bilinearWeight00 t x * a (gridIndex 1 t) (gridIndex 1 x) +
      bilinearWeight01 t x * a (gridIndex 1 t) (gridIndex 1 x + 1) +
      bilinearWeight10 t x * a (gridIndex 1 t + 1) (gridIndex 1 x) +
      bilinearWeight11 t x * a (gridIndex 1 t + 1) (gridIndex 1 x + 1) := by
  simp only [bilinearInterp, linInterp, bilinearWeight00, bilinearWeight01,
    bilinearWeight10, bilinearWeight11]
  ring

theorem bilinearInterp_eq_on_cell (a : ℕ → ℕ → ℝ) (n j : ℕ) (t x : ℝ)
    (ht : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1))
    (hx : x ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1)) :
    bilinearInterp a t x =
      (1 - (t - n)) *
          ((1 - (x - j)) * a n j + (x - j) * a n (j + 1)) +
        (t - n) *
          ((1 - (x - j)) * a (n + 1) j + (x - j) * a (n + 1) (j + 1)) := by
  rw [bilinearInterp, linInterp_eq_on_Icc _ n t ht,
    linInterp_eq_on_Icc (a n) j x hx, linInterp_eq_on_Icc (a (n + 1)) j x hx]

@[simp]
theorem bilinearInterp_at_nat (a : ℕ → ℕ → ℝ) (n j : ℕ) :
    bilinearInterp a (n : ℝ) (j : ℝ) = a n j := by
  simp [bilinearInterp]

theorem bilinearInterp_of_time_nonpos (a : ℕ → ℕ → ℝ) (t x : ℝ) (ht : t ≤ 0) :
    bilinearInterp a t x = linInterp (a 0) x := by
  exact linInterp_of_nonpos (fun n ↦ linInterp (a n) x) t ht

theorem bilinearInterp_of_space_nonpos (a : ℕ → ℕ → ℝ) (t x : ℝ) (hx : x ≤ 0) :
    bilinearInterp a t x = linInterp (fun n ↦ a n 0) t := by
  simp [bilinearInterp, linInterp_of_nonpos _ x hx]

@[simp]
theorem bilinearInterp_of_nonpos (a : ℕ → ℕ → ℝ) (t x : ℝ) (ht : t ≤ 0)
    (hx : x ≤ 0) : bilinearInterp a t x = a 0 0 := by
  rw [bilinearInterp_of_time_nonpos a t x ht, linInterp_of_nonpos (a 0) x hx]

def cellMax (a : ℕ → ℕ → ℝ) (n j : ℕ) : ℝ :=
  max (max (a n j) (a n (j + 1)))
    (max (a (n + 1) j) (a (n + 1) (j + 1)))

def cellMin (a : ℕ → ℕ → ℝ) (n j : ℕ) : ℝ :=
  min (min (a n j) (a n (j + 1)))
    (min (a (n + 1) j) (a (n + 1) (j + 1)))

def cellAbsMax (a : ℕ → ℕ → ℝ) (n j : ℕ) : ℝ :=
  max (max |a n j| |a n (j + 1)|)
    (max |a (n + 1) j| |a (n + 1) (j + 1)|)

theorem bilinearInterp_le_cellMax (a : ℕ → ℕ → ℝ) (t x : ℝ) :
    bilinearInterp a t x ≤ cellMax a (gridIndex 1 t) (gridIndex 1 x) := by
  calc
    bilinearInterp a t x ≤
        max (linInterp (a (gridIndex 1 t)) x)
          (linInterp (a (gridIndex 1 t + 1)) x) := by
      exact linInterp_le_max_neighbors (fun n ↦ linInterp (a n) x) t
    _ ≤ cellMax a (gridIndex 1 t) (gridIndex 1 x) := by
      exact max_le_max
        (linInterp_le_max_neighbors (a (gridIndex 1 t)) x)
        (linInterp_le_max_neighbors (a (gridIndex 1 t + 1)) x)

theorem cellMin_le_bilinearInterp (a : ℕ → ℕ → ℝ) (t x : ℝ) :
    cellMin a (gridIndex 1 t) (gridIndex 1 x) ≤ bilinearInterp a t x := by
  calc
    cellMin a (gridIndex 1 t) (gridIndex 1 x) ≤
        min (linInterp (a (gridIndex 1 t)) x)
          (linInterp (a (gridIndex 1 t + 1)) x) := by
      exact min_le_min
        (min_neighbors_le_linInterp (a (gridIndex 1 t)) x)
        (min_neighbors_le_linInterp (a (gridIndex 1 t + 1)) x)
    _ ≤ bilinearInterp a t x := by
      exact min_neighbors_le_linInterp (fun n ↦ linInterp (a n) x) t

theorem abs_bilinearInterp_le_cellAbsMax (a : ℕ → ℕ → ℝ) (t x : ℝ) :
    |bilinearInterp a t x| ≤ cellAbsMax a (gridIndex 1 t) (gridIndex 1 x) := by
  calc
    |bilinearInterp a t x| ≤
        max |linInterp (a (gridIndex 1 t)) x|
          |linInterp (a (gridIndex 1 t + 1)) x| := by
      exact abs_linInterp_le_max_abs_neighbors (fun n ↦ linInterp (a n) x) t
    _ ≤ cellAbsMax a (gridIndex 1 t) (gridIndex 1 x) := by
      exact max_le_max
        (abs_linInterp_le_max_abs_neighbors (a (gridIndex 1 t)) x)
        (abs_linInterp_le_max_abs_neighbors (a (gridIndex 1 t + 1)) x)

theorem bilinearInterp_nonneg (a : ℕ → ℕ → ℝ) (ha : ∀ n j : ℕ, 0 ≤ a n j)
    (t x : ℝ) : 0 ≤ bilinearInterp a t x := by
  exact linInterp_nonneg (fun n ↦ linInterp (a n) x)
    (fun n ↦ linInterp_nonneg (a n) (ha n) x) t

private theorem iUnion_natTimeStrips :
    (⋃ n : ℕ, Set.Icc (n : ℝ) ((n : ℝ) + 1) ×ˢ (Set.univ : Set ℝ)) =
      Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨n, hn⟩
    exact ⟨(Nat.cast_nonneg n).trans hn.1.1, Set.mem_univ p.2⟩
  · intro hp
    have hp₁ : p.1 ∈ ⋃ n : ℕ, Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
      rw [iUnion_natUnitCells]
      exact hp.1
    rcases Set.mem_iUnion.mp hp₁ with ⟨n, hn⟩
    exact Set.mem_iUnion.2 ⟨n, ⟨hn, Set.mem_univ p.2⟩⟩

/-- A parameter-dependent linear interpolation is jointly continuous when every coefficient is
continuous in the parameter.  The proof glues the affine formulas over a locally finite family
of closed strips, so it includes all floor boundaries. -/
theorem continuous_parametric_linInterp (f : ℕ → ℝ → ℝ)
    (hf : ∀ n : ℕ, Continuous (f n)) :
    Continuous (fun p : ℝ × ℝ ↦ linInterp (fun n ↦ f n p.2) p.1) := by
  let F : ℝ × ℝ → ℝ := fun p ↦ linInterp (fun n ↦ f n p.2) p.1
  have hstrips :
      LocallyFinite (fun n : ℕ ↦
        Set.Icc (n : ℝ) ((n : ℝ) + 1) ×ˢ (Set.univ : Set ℝ)) :=
    locallyFinite_natUnitCells.prod_right (fun _ ↦ (Set.univ : Set ℝ))
  have hcell : ∀ n : ℕ,
      ContinuousOn F
        (Set.Icc (n : ℝ) ((n : ℝ) + 1) ×ˢ (Set.univ : Set ℝ)) := by
    intro n
    have hpoly : Continuous (fun p : ℝ × ℝ ↦
        (1 - (p.1 - n)) * f n p.2 + (p.1 - n) * f (n + 1) p.2) := by
      fun_prop
    exact hpoly.continuousOn.congr (fun p hp ↦ linInterp_eq_on_Icc
      (fun k ↦ f k p.2) n p.1 hp.1)
  have hnonneg : ContinuousOn F (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rw [← iUnion_natTimeStrips]
    exact hstrips.continuousOn_iUnion
      (fun _ ↦ isClosed_Icc.prod isClosed_univ) hcell
  let clampTime : ℝ × ℝ → ℝ × ℝ := fun p ↦ (max p.1 0, p.2)
  have hclamp : Continuous clampTime := by
    fun_prop
  have hmap : ∀ p : ℝ × ℝ,
      clampTime p ∈ Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := by
    intro p
    exact ⟨le_max_right p.1 0, Set.mem_univ p.2⟩
  have hcomp := hnonneg.comp_continuous hclamp hmap
  simpa [F, clampTime, Function.comp_def] using hcomp

/-- Bilinear interpolation is jointly continuous on the whole plane, hence in particular across
all grid boundaries in the nonnegative quadrant. -/
theorem continuous_bilinearInterp (a : ℕ → ℕ → ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ bilinearInterp a p.1 p.2) := by
  exact continuous_parametric_linInterp (fun n ↦ linInterp (a n))
    (fun n ↦ continuous_linInterp (a n))

theorem continuousOn_bilinearInterp_nonnegative (a : ℕ → ℕ → ℝ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ bilinearInterp a p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) :=
  (continuous_bilinearInterp a).continuousOn

theorem continuous_bilinearInterp_time (a : ℕ → ℕ → ℝ) (x : ℝ) :
    Continuous (fun t : ℝ ↦ bilinearInterp a t x) := by
  exact (continuous_bilinearInterp a).comp (continuous_id.prodMk continuous_const)

theorem continuous_bilinearInterp_space (a : ℕ → ℕ → ℝ) (t : ℝ) :
    Continuous (fun x : ℝ ↦ bilinearInterp a t x) := by
  exact (continuous_bilinearInterp a).comp (continuous_const.prodMk continuous_id)

@[simp]
theorem gridIndex_one_mul_natCast (N : ℕ) (x : ℝ) :
    gridIndex 1 ((N : ℝ) * x) = gridIndex N x := by
  by_cases hx : 0 ≤ x
  · have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg (Nat.cast_nonneg N) hx
    simp [gridIndex, max_eq_left hx, max_eq_left hNx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hNx : (N : ℝ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hx'
    simp [gridIndex, max_eq_right hx', max_eq_right hNx]

@[simp]
theorem gridFrac_one_mul_natCast (N : ℕ) (x : ℝ) :
    gridFrac 1 ((N : ℝ) * x) = gridFrac N x := by
  by_cases hx : 0 ≤ x
  · have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg (Nat.cast_nonneg N) hx
    simp [gridFrac, max_eq_left hx, max_eq_left hNx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hNx : (N : ℝ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hx'
    simp [gridFrac, max_eq_right hx', max_eq_right hNx]

/-- Bilinear interpolation on mesh size `1 / N`.  The degenerate scale is explicitly zero, as
required for the rescaled profile definition. -/
def gridBilinearInterp (N : ℕ) (a : ℕ → ℕ → ℝ) (t x : ℝ) : ℝ :=
  if N = 0 then 0 else bilinearInterp a ((N : ℝ) * t) ((N : ℝ) * x)

@[simp]
theorem gridBilinearInterp_zero (a : ℕ → ℕ → ℝ) (t x : ℝ) :
    gridBilinearInterp 0 a t x = 0 := by
  simp [gridBilinearInterp]

theorem gridBilinearInterp_of_pos (N : ℕ) (a : ℕ → ℕ → ℝ) (t x : ℝ)
    (hN : 0 < N) :
    gridBilinearInterp N a t x =
      bilinearInterp a ((N : ℝ) * t) ((N : ℝ) * x) := by
  simp [gridBilinearInterp, Nat.ne_of_gt hN]

theorem gridBilinearInterp_eq_four_weights (N : ℕ) (a : ℕ → ℕ → ℝ) (t x : ℝ)
    (hN : 0 < N) :
    gridBilinearInterp N a t x =
      ((1 - gridFrac N t) * (1 - gridFrac N x)) *
          a (gridIndex N t) (gridIndex N x) +
      ((1 - gridFrac N t) * gridFrac N x) *
          a (gridIndex N t) (gridIndex N x + 1) +
      (gridFrac N t * (1 - gridFrac N x)) *
          a (gridIndex N t + 1) (gridIndex N x) +
      (gridFrac N t * gridFrac N x) *
          a (gridIndex N t + 1) (gridIndex N x + 1) := by
  rw [gridBilinearInterp_of_pos N a t x hN,
    bilinearInterp_eq_four_weights]
  simp [bilinearWeight00, bilinearWeight01, bilinearWeight10, bilinearWeight11]

@[simp]
theorem gridBilinearInterp_at_node (N n j : ℕ) (a : ℕ → ℕ → ℝ) (hN : 0 < N) :
    gridBilinearInterp N a ((n : ℝ) / (N : ℝ)) ((j : ℝ) / (N : ℝ)) = a n j := by
  rw [gridBilinearInterp_of_pos N a _ _ hN]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hn : (N : ℝ) * ((n : ℝ) / (N : ℝ)) = n := by
    field_simp
  have hj : (N : ℝ) * ((j : ℝ) / (N : ℝ)) = j := by
    field_simp
  rw [hn, hj, bilinearInterp_at_nat]

theorem gridBilinearInterp_nonneg (N : ℕ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ n j : ℕ, 0 ≤ a n j) (t x : ℝ) : 0 ≤ gridBilinearInterp N a t x := by
  by_cases hN : N = 0
  · simp [hN, gridBilinearInterp]
  · rw [gridBilinearInterp, if_neg hN]
    exact bilinearInterp_nonneg a ha ((N : ℝ) * t) ((N : ℝ) * x)

theorem gridBilinearInterp_of_time_nonpos (N : ℕ) (a : ℕ → ℕ → ℝ) (t x : ℝ)
    (hN : 0 < N) (ht : t ≤ 0) :
    gridBilinearInterp N a t x = linInterp (a 0) ((N : ℝ) * x) := by
  rw [gridBilinearInterp_of_pos N a t x hN]
  exact bilinearInterp_of_time_nonpos a ((N : ℝ) * t) ((N : ℝ) * x)
    (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) ht)

theorem gridBilinearInterp_of_space_nonpos (N : ℕ) (a : ℕ → ℕ → ℝ) (t x : ℝ)
    (hN : 0 < N) (hx : x ≤ 0) :
    gridBilinearInterp N a t x = linInterp (fun n ↦ a n 0) ((N : ℝ) * t) := by
  rw [gridBilinearInterp_of_pos N a t x hN]
  exact bilinearInterp_of_space_nonpos a ((N : ℝ) * t) ((N : ℝ) * x)
    (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hx)

theorem gridBilinearInterp_of_nonpos (N : ℕ) (a : ℕ → ℕ → ℝ) (t x : ℝ)
    (hN : 0 < N) (ht : t ≤ 0) (hx : x ≤ 0) :
    gridBilinearInterp N a t x = a 0 0 := by
  rw [gridBilinearInterp_of_time_nonpos N a t x hN ht]
  exact linInterp_of_nonpos (a 0) ((N : ℝ) * x)
    (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) hx)

theorem gridBilinearInterp_le_cellMax (N : ℕ) (a : ℕ → ℕ → ℝ) (t x : ℝ)
    (hN : 0 < N) :
    gridBilinearInterp N a t x ≤ cellMax a (gridIndex N t) (gridIndex N x) := by
  rw [gridBilinearInterp_of_pos N a t x hN]
  simpa using bilinearInterp_le_cellMax a ((N : ℝ) * t) ((N : ℝ) * x)

theorem cellMin_le_gridBilinearInterp (N : ℕ) (a : ℕ → ℕ → ℝ) (t x : ℝ)
    (hN : 0 < N) :
    cellMin a (gridIndex N t) (gridIndex N x) ≤ gridBilinearInterp N a t x := by
  rw [gridBilinearInterp_of_pos N a t x hN]
  simpa using cellMin_le_bilinearInterp a ((N : ℝ) * t) ((N : ℝ) * x)

theorem continuous_gridBilinearInterp (N : ℕ) (a : ℕ → ℕ → ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ gridBilinearInterp N a p.1 p.2) := by
  by_cases hN : N = 0
  · subst N
    simpa [gridBilinearInterp] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ ↦ (0 : ℝ)))
  · have hscale : Continuous (fun p : ℝ × ℝ ↦
        ((N : ℝ) * p.1, (N : ℝ) * p.2)) := by
      fun_prop
    simpa [gridBilinearInterp, hN] using (continuous_bilinearInterp a).comp hscale

theorem continuousOn_gridBilinearInterp_nonnegative (N : ℕ) (a : ℕ → ℕ → ℝ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ gridBilinearInterp N a p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) :=
  (continuous_gridBilinearInterp N a).continuousOn

theorem gridBilinearInterp_time_one (N : ℕ) (a : ℕ → ℕ → ℝ) (x : ℝ)
    (hN : 0 < N) :
    gridBilinearInterp N a 1 x = linInterp (a N) ((N : ℝ) * x) := by
  rw [gridBilinearInterp_of_pos N a 1 x hN]
  norm_num [bilinearInterp]

/-- The generic `t = 1` floor-readout estimate.  A later profile module can multiply the grid
values by `N²` and bound the right-hand side by its discrete spatial modulus. -/
theorem abs_gridBilinearInterp_time_one_sub_floor_le
    (N : ℕ) (a : ℕ → ℕ → ℝ) (x : ℝ) (hN : 0 < N) :
    |gridBilinearInterp N a 1 x - a N (gridIndex N x)| ≤
      |a N (gridIndex N x + 1) - a N (gridIndex N x)| := by
  rw [gridBilinearInterp_time_one N a x hN]
  simpa using abs_linInterp_sub_left_neighbor_le (a N) ((N : ℝ) * x)

theorem abs_gridBilinearInterp_time_one_sub_floor_le_of_bound
    (N : ℕ) (a : ℕ → ℕ → ℝ) (x C : ℝ) (hN : 0 < N)
    (hC : ∀ j : ℕ, |a N (j + 1) - a N j| ≤ C) :
    |gridBilinearInterp N a 1 x - a N (gridIndex N x)| ≤ C :=
  (abs_gridBilinearInterp_time_one_sub_floor_le N a x hN).trans (hC (gridIndex N x))

end

end DerridaRetaux
