import DerridaRetaux.Analysis.ProfileCompactnessNodes

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

private theorem natGap_cast_div_le_abs_div
    {N a b : ℕ} (hN : 0 < N) :
    (natGap a b : ℝ) / (N : ℝ) ≤
      |(a : ℝ) / (N : ℝ) - (b : ℝ) / (N : ℝ)| := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rcases le_total a b with hab | hba
  · rw [natGap_eq_of_le hab, Nat.cast_sub hab]
    rw [abs_of_nonpos]
    · field_simp [hNreal.ne']
    · exact sub_nonpos.mpr (div_le_div_of_nonneg_right
        (by exact_mod_cast hab) hNreal.le)
  · rw [natGap_comm, natGap_eq_of_le hba, Nat.cast_sub hba]
    rw [abs_of_nonneg]
    · field_simp [hNreal.ne']
    · exact sub_nonneg.mpr (div_le_div_of_nonneg_right
        (by exact_mod_cast hba) hNreal.le)

private theorem clamped_time_gap_div_le
    (eta : ℝ) {N n s : ℕ} (hN : 0 < N) :
    (natGap (max n (gridIndex N eta)) (max s (gridIndex N eta)) : ℝ) /
        (N : ℝ) ≤
      |(n : ℝ) / (N : ℝ) - (s : ℝ) / (N : ℝ)| := by
  have hmax :
      |((max n (gridIndex N eta) : ℕ) : ℝ) -
          ((max s (gridIndex N eta) : ℕ) : ℝ)| ≤
        |(n : ℝ) - (s : ℝ)| := by
    simpa only [Nat.cast_max] using
      abs_max_sub_max_le_abs (n : ℝ) (s : ℝ) (gridIndex N eta : ℝ)
  have hgap := natGap_cast_div_le_abs_div (a := max n (gridIndex N eta))
    (b := max s (gridIndex N eta)) hN
  calc
    (natGap (max n (gridIndex N eta)) (max s (gridIndex N eta)) : ℝ) /
        (N : ℝ) ≤
      |((max n (gridIndex N eta) : ℕ) : ℝ) / (N : ℝ) -
        ((max s (gridIndex N eta) : ℕ) : ℝ) / (N : ℝ)| := hgap
    _ = |((max n (gridIndex N eta) : ℕ) : ℝ) -
          ((max s (gridIndex N eta) : ℕ) : ℝ)| / (N : ℝ) := by
      rw [show ((max n (gridIndex N eta) : ℕ) : ℝ) / (N : ℝ) -
        ((max s (gridIndex N eta) : ℕ) : ℝ) / (N : ℝ) =
        (((max n (gridIndex N eta) : ℕ) : ℝ) -
          ((max s (gridIndex N eta) : ℕ) : ℝ)) / (N : ℝ) by ring,
        abs_div, abs_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)]
    _ ≤ |(n : ℝ) - (s : ℝ)| / (N : ℝ) :=
      div_le_div_of_nonneg_right hmax (by positivity)
    _ = |(n : ℝ) / (N : ℝ) - (s : ℝ) / (N : ℝ)| := by
      rw [show (n : ℝ) / (N : ℝ) - (s : ℝ) / (N : ℝ) =
        ((n : ℝ) - (s : ℝ)) / (N : ℝ) by ring, abs_div,
        abs_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)]
theorem clampedOrbitScaledGrid_node_modulus
    (m : ℕ) (p₀ : ProbabilityMass) {C eta : ℝ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (C / profileScale n ^ 2))
    (hSpatial : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n) -
          (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
        (smoothingRate C n h))
    (hTemporal : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      SupLE
        (positiveTiltedDensity m (orbit m p₀ (n + h)) -
          positiveTiltedDensity m (orbit m p₀ n))
        (smoothingRate C n h)) :
    ∀ N n j s k : ℕ, 0 < N →
      |clampedOrbitScaledGrid m p₀ eta N n j -
        clampedOrbitScaledGrid m p₀ eta N s k| ≤
      (4 * C / eta ^ 2) * Real.sqrt
        ((|(n : ℝ) / (N : ℝ) - (s : ℝ) / (N : ℝ)| +
          |(j : ℝ) / (N : ℝ) - (k : ℝ) / (N : ℝ)|) / eta) := by
  intro N n j s k hN
  let n₀ := gridIndex N eta
  let r := max n n₀
  let u := max s n₀
  let q := |(n : ℝ) / (N : ℝ) - (s : ℝ) / (N : ℝ)| +
    |(j : ℝ) / (N : ℝ) - (k : ℝ) / (N : ℝ)|
  have hq : 0 ≤ q := add_nonneg (abs_nonneg _) (abs_nonneg _)
  by_cases hqeta : q < eta
  · have htimeq : (natGap r u : ℝ) / (N : ℝ) ≤ q := by
      apply (clamped_time_gap_div_le eta hN).trans
      exact le_add_of_nonneg_right (abs_nonneg _)
    have hspaceq : (natGap j k : ℝ) / (N : ℝ) ≤ q := by
      apply (natGap_cast_div_le_abs_div hN).trans
      exact le_add_of_nonneg_left (abs_nonneg _)
    have hrLower : (N : ℝ) * eta < profileScale r := by
      simpa only [r, n₀] using clamped_row_lower eta N n heta.le
    have huLower : (N : ℝ) * eta < profileScale u := by
      simpa only [u, n₀] using clamped_row_lower eta N s heta.le
    have htimeL : natGap r u ≤ min r u + 1 := by
      have hdivlt : (natGap r u : ℝ) / (N : ℝ) < eta := htimeq.trans_lt hqeta
      rw [div_lt_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)] at hdivlt
      have hrow : (N : ℝ) * eta < ((min r u + 1 : ℕ) : ℝ) := by
        rcases le_total r u with hru | hur
        · simpa only [min_eq_left hru, profileScale, Nat.cast_add, Nat.cast_one,
            mul_comm] using hrLower
        · simpa only [min_eq_right hur, profileScale, Nat.cast_add, Nat.cast_one,
            mul_comm] using huLower
      have hltReal : (natGap r u : ℝ) < ((min r u + 1 : ℕ) : ℝ) :=
        hdivlt.trans (by simpa [mul_comm] using hrow)
      have hltNat : natGap r u < min r u + 1 := by exact_mod_cast hltReal
      exact hltNat.le
    have hspaceL : natGap j k ≤ min r u + 1 := by
      have hdivlt : (natGap j k : ℝ) / (N : ℝ) < eta := hspaceq.trans_lt hqeta
      rw [div_lt_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)] at hdivlt
      have hrow : (N : ℝ) * eta < ((min r u + 1 : ℕ) : ℝ) := by
        rcases le_total r u with hru | hur
        · simpa only [min_eq_left hru, profileScale, Nat.cast_add, Nat.cast_one,
            mul_comm] using hrLower
        · simpa only [min_eq_right hur, profileScale, Nat.cast_add, Nat.cast_one,
            mul_comm] using huLower
      have hltReal : (natGap j k : ℝ) < ((min r u + 1 : ℕ) : ℝ) :=
        hdivlt.trans (by simpa [mul_comm] using hrow)
      have hltNat : natGap j k < min r u + 1 := by exact_mod_cast hltReal
      exact hltNat.le
    rcases le_total r u with hru | hur
    · have hspaceLr : natGap j k ≤ r + 1 := by
        simpa only [min_eq_left hru] using hspaceL
      have htimeLr : u - r ≤ r + 1 := by
        rw [← natGap_eq_of_le hru]
        simpa only [min_eq_left hru] using htimeL
      have htimeqr : ((u - r : ℕ) : ℝ) / (N : ℝ) ≤ q := by
        rw [← natGap_eq_of_le hru]
        exact htimeq
      have hsp := scaled_spatial_difference_le_sqrt m p₀ hC heta hN
        hrLower.le hspaceLr hspaceq hSpatial
      have htm := scaled_temporal_difference_le_sqrt m p₀ (j := k) hC heta hN hru
        hrLower.le htimeLr htimeqr hTemporal
      unfold clampedOrbitScaledGrid orbitScaledGrid
      dsimp only [r, u, n₀, q] at hsp htm ⊢
      rw [abs_sub_comm] at htm
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc
        (N : ℝ) ^ 2 *
            |positiveTiltedDensity m (orbit m p₀ (max n (gridIndex N eta))) j -
              positiveTiltedDensity m (orbit m p₀ (max s (gridIndex N eta))) k| ≤
            (N : ℝ) ^ 2 *
              (|positiveTiltedDensity m (orbit m p₀ (max n (gridIndex N eta))) j -
                positiveTiltedDensity m (orbit m p₀ (max n (gridIndex N eta))) k| +
               |positiveTiltedDensity m (orbit m p₀ (max n (gridIndex N eta))) k -
                positiveTiltedDensity m (orbit m p₀ (max s (gridIndex N eta))) k|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ ≤ (2 * C / eta ^ 2) * Real.sqrt (q / eta) +
            (2 * C / eta ^ 2) * Real.sqrt (q / eta) := by
          rw [mul_add]
          exact add_le_add hsp htm
        _ = (4 * C / eta ^ 2) * Real.sqrt (q / eta) := by ring
    · have hspaceLu : natGap j k ≤ u + 1 := by
        simpa only [min_eq_right hur] using hspaceL
      have hgapUR : natGap u r ≤ u + 1 := by
        rw [natGap_comm]
        simpa only [min_eq_right hur] using htimeL
      have htimeLu : r - u ≤ u + 1 := by
        rw [← natGap_eq_of_le hur]
        exact hgapUR
      have hqUR : (natGap u r : ℝ) / (N : ℝ) ≤ q := by
        simpa only [natGap_comm] using htimeq
      have htimequ : ((r - u : ℕ) : ℝ) / (N : ℝ) ≤ q := by
        rw [← natGap_eq_of_le hur]
        exact hqUR
      have hsp := scaled_spatial_difference_le_sqrt m p₀ hC heta hN
        huLower.le hspaceLu hspaceq hSpatial
      have htm := scaled_temporal_difference_le_sqrt m p₀ (j := j) hC heta hN hur
        huLower.le htimeLu htimequ hTemporal
      unfold clampedOrbitScaledGrid orbitScaledGrid
      dsimp only [r, u, n₀, q] at hsp htm ⊢
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc
        (N : ℝ) ^ 2 *
            |positiveTiltedDensity m (orbit m p₀ (max n (gridIndex N eta))) j -
              positiveTiltedDensity m (orbit m p₀ (max s (gridIndex N eta))) k| ≤
            (N : ℝ) ^ 2 *
              (|positiveTiltedDensity m (orbit m p₀ (max n (gridIndex N eta))) j -
                positiveTiltedDensity m (orbit m p₀ (max s (gridIndex N eta))) j| +
               |positiveTiltedDensity m (orbit m p₀ (max s (gridIndex N eta))) j -
                positiveTiltedDensity m (orbit m p₀ (max s (gridIndex N eta))) k|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ ≤ (2 * C / eta ^ 2) * Real.sqrt (q / eta) +
            (2 * C / eta ^ 2) * Real.sqrt (q / eta) := by
          rw [mul_add]
          exact add_le_add htm hsp
        _ = (4 * C / eta ^ 2) * Real.sqrt (q / eta) := by ring
  · have hleft := clampedOrbitScaledGrid_node_bound m p₀ hC heta hSup N n j
    have hright := clampedOrbitScaledGrid_node_bound m p₀ hC heta hSup N s k
    have hsqrt : 1 ≤ Real.sqrt (q / eta) := by
      have hratio0 : 0 ≤ q / eta := div_nonneg hq heta.le
      have hratio : 1 ≤ q / eta := (le_div_iff₀ heta).2 (by simpa only [one_mul] using le_of_not_gt hqeta)
      nlinarith [Real.sq_sqrt hratio0, Real.sqrt_nonneg (q / eta)]
    calc
      |clampedOrbitScaledGrid m p₀ eta N n j -
          clampedOrbitScaledGrid m p₀ eta N s k| ≤
          |clampedOrbitScaledGrid m p₀ eta N n j| +
            |clampedOrbitScaledGrid m p₀ eta N s k| := abs_sub _ _
      _ ≤ C / eta ^ 2 + C / eta ^ 2 := add_le_add hleft hright
      _ ≤ 2 * (C / eta ^ 2) := by ring_nf; exact le_rfl
      _ ≤ 4 * (C / eta ^ 2) := by
        have hcoef : 0 ≤ C / eta ^ 2 := div_nonneg hC (sq_nonneg eta)
        linarith
      _ ≤ 4 * (C / eta ^ 2) * Real.sqrt (q / eta) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (div_nonneg hC (sq_nonneg eta)))
      _ = (4 * C / eta ^ 2) * Real.sqrt (q / eta) := by ring

end

end DerridaRetaux.FixedArity
