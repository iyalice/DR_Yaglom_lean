import DerridaRetaux.Main.Smoothing
import DerridaRetaux.Analysis.GridReadout
import DerridaRetaux.Analysis.GridCompactness
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

def clampedOrbitScaledGrid
    (m : ℕ) (p₀ : ProbabilityMass) (eta : ℝ) (N n j : ℕ) : ℝ :=
  orbitScaledGrid m p₀ N (max n (gridIndex N eta)) j

theorem smoothing_log_bound {q : ℝ} (hq : 0 < q) :
    q * (1 + Real.log (1 / q)) ≤ 2 * Real.sqrt q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
  have hrewrite : Real.log (1 / q) =
      2 * Real.log ((Real.sqrt q)⁻¹) := by
    rw [one_div, Real.log_inv, Real.log_inv, Real.log_sqrt hq.le]
    ring
  rw [hrewrite]
  have hinner : 1 + 2 * Real.log (Real.sqrt q)⁻¹ ≤
      1 + 2 * ((Real.sqrt q)⁻¹ - 1) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hinner hq.le
  calc
    q * (1 + 2 * Real.log (Real.sqrt q)⁻¹) ≤
        q * (1 + 2 * ((Real.sqrt q)⁻¹ - 1)) := hmul
    _ ≤ 2 * Real.sqrt q := by
      have hsquare := Real.sq_sqrt hq.le
      have hinvprod : q * (Real.sqrt q)⁻¹ = Real.sqrt q := by
        rw [← hsquare]
        field_simp [hs.ne']
      calc
        q * (1 + 2 * ((Real.sqrt q)⁻¹ - 1)) =
            2 * (q * (Real.sqrt q)⁻¹) - q := by ring
        _ = 2 * Real.sqrt q - q := by rw [hinvprod]
        _ ≤ 2 * Real.sqrt q := sub_le_self _ hq.le

theorem scaled_smoothing_rate_le_sqrt
    {N L h C eta q : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hh : 0 < h) (hC : 0 ≤ C)
    (heta : 0 < eta) (hNL : N * eta ≤ L)
    (hhL : h ≤ L) (hq : h / N ≤ q) :
    N ^ 2 * (C * h / L ^ 3 * (1 + Real.log (L / h))) ≤
      (2 * C / eta ^ 2) * Real.sqrt (q / eta) := by
  have hratio : 0 < h / L := div_pos hh hL
  have hlog := smoothing_log_bound hratio
  have hlogEq : Real.log (L / h) = Real.log (1 / (h / L)) := by
    congr 1
    field_simp [hh.ne', hL.ne']
  rw [← hlogEq] at hlog
  have hNLratio : N / L ≤ 1 / eta :=
    (div_le_div_iff₀ hL heta).2 (by simpa only [one_mul] using hNL)
  have hcoeff : 0 ≤ C * (N / L) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog hcoeff
  have hqpos : 0 < q := (div_pos hh hN).trans_le hq
  have hqratio : h / L ≤ q / eta := by
    calc
      h / L = (h / N) * (N / L) := by field_simp [hN.ne', hL.ne']
      _ ≤ q * (1 / eta) := mul_le_mul hq hNLratio (by positivity) (by positivity)
      _ = q / eta := by ring
  have hsqrt := Real.sqrt_le_sqrt hqratio
  calc
    N ^ 2 * (C * h / L ^ 3 * (1 + Real.log (L / h))) =
        (C * (N / L) ^ 2) * ((h / L) * (1 + Real.log (L / h))) := by
      field_simp [hL.ne']
      ring
    _ ≤ (C * (N / L) ^ 2) * (2 * Real.sqrt (h / L)) := hscaled
    _ ≤ (C * (1 / eta) ^ 2) * (2 * Real.sqrt (q / eta)) := by
      gcongr
    _ = (2 * C / eta ^ 2) * Real.sqrt (q / eta) := by ring

theorem clamped_row_lower
    (eta : ℝ) (N n : ℕ) (heta : 0 ≤ eta) :
    (N : ℝ) * eta < ((max n (gridIndex N eta) + 1 : ℕ) : ℝ) := by
  have hfloor := mul_lt_gridIndex_add_one N eta heta
  exact hfloor.trans_le (by exact_mod_cast Nat.succ_le_succ (le_max_right n _))

theorem clampedOrbitScaledGrid_node_bound
    (m : ℕ) (p₀ : ProbabilityMass) {C eta : ℝ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (C / profileScale n ^ 2)) :
    ∀ N n j : ℕ,
      |clampedOrbitScaledGrid m p₀ eta N n j| ≤ C / eta ^ 2 := by
  intro N n j
  by_cases hN : N = 0
  · simp [clampedOrbitScaledGrid, orbitScaledGrid, hN]
    exact div_nonneg hC (sq_nonneg eta)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  let r := max n (gridIndex N eta)
  let L : ℝ := profileScale r
  have hLpos : 0 < L := profileScale_pos r
  have hNL : (N : ℝ) * eta ≤ L := by
    exact (clamped_row_lower eta N n heta.le).le
  have hrho := supLE_of_weightedSupThree L (C / L ^ 2) hLpos
    (positiveTiltedDensity m (orbit m p₀ r)) (by simpa only [L] using hSup r) j
  have hratio : (N : ℝ) / L ≤ 1 / eta :=
    (div_le_div_iff₀ hLpos heta).2 (by simpa only [one_mul] using hNL)
  unfold clampedOrbitScaledGrid orbitScaledGrid
  dsimp only [r, L] at hrho ⊢
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    (N : ℝ) ^ 2 * |positiveTiltedDensity m (orbit m p₀
        (max n (gridIndex N eta))) j| ≤
        (N : ℝ) ^ 2 * (C / profileScale (max n (gridIndex N eta)) ^ 2) :=
      mul_le_mul_of_nonneg_left hrho (sq_nonneg _)
    _ = C * ((N : ℝ) / profileScale (max n (gridIndex N eta))) ^ 2 := by ring
    _ ≤ C * (1 / eta) ^ 2 := by gcongr
    _ = C / eta ^ 2 := by ring

end

end DerridaRetaux.FixedArity
