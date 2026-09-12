import DerridaRetaux.Analysis.ProfileCompactness

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

def smoothingRate (C : ℝ) (n h : ℕ) : ℝ :=
  C * (h : ℝ) / profileScale n ^ 3 *
    (1 + Real.log (profileScale n / (h : ℝ)))
def natGap (a b : ℕ) : ℕ := max a b - min a b
theorem natGap_ne_zero {a b : ℕ} : natGap a b ≠ 0 ↔ a ≠ b := by
  rcases le_total a b with hab | hba
  · simp [natGap, max_eq_right hab, min_eq_left hab] <;> omega
  · simp [natGap, max_eq_left hba, min_eq_right hba] <;> omega

theorem natGap_eq_of_le {a b : ℕ} (h : a ≤ b) :
    natGap a b = b - a := by
  simp [natGap, max_eq_right h, min_eq_left h]

theorem natGap_comm (a b : ℕ) : natGap a b = natGap b a := by
  simp [natGap, max_comm, min_comm]



theorem scaled_smoothingRate_le_sqrt
    {C eta q : ℝ} {N n h : ℕ}
    (hC : 0 ≤ C) (heta : 0 < eta) (hN : 0 < N)
    (hNL : (N : ℝ) * eta ≤ profileScale n)
    (hh : 1 ≤ h) (hhL : h ≤ n + 1)
    (hq : (h : ℝ) / (N : ℝ) ≤ q) :
    (N : ℝ) ^ 2 * smoothingRate C n h ≤
      (2 * C / eta ^ 2) * Real.sqrt (q / eta) := by
  apply scaled_smoothing_rate_le_sqrt
  · exact_mod_cast hN
  · exact profileScale_pos n
  · exact_mod_cast (Nat.zero_lt_of_lt hh)
  · exact hC
  · exact heta
  · exact hNL
  · simpa only [profileScale] using
      (show ((h : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast hhL)
  · exact hq

theorem scaled_spatial_difference_le_sqrt
    (m : ℕ) (p₀ : ProbabilityMass)
    {C eta q : ℝ} {N n j k : ℕ}
    (hC : 0 ≤ C) (heta : 0 < eta) (hN : 0 < N)
    (hNL : (N : ℝ) * eta ≤ profileScale n)
    (hdistL : natGap j k ≤ n + 1)
    (hq : (natGap j k : ℝ) / (N : ℝ) ≤ q)
    (hSpatial : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n) -
          (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
        (smoothingRate C n h)) :
    (N : ℝ) ^ 2 *
        |positiveTiltedDensity m (orbit m p₀ n) j -
          positiveTiltedDensity m (orbit m p₀ n) k| ≤
      (2 * C / eta ^ 2) * Real.sqrt (q / eta) := by
  by_cases hjk : j = k
  · subst k
    simp
    positivity
  have hdistPos : 1 ≤ natGap j k := Nat.one_le_iff_ne_zero.mpr
    (natGap_ne_zero.mpr hjk)
  have hraw :
      |positiveTiltedDensity m (orbit m p₀ n) j -
        positiveTiltedDensity m (orbit m p₀ n) k| ≤
        smoothingRate C n (natGap j k) := by
    have hs := supLE_of_weightedSupThree (profileScale n)
      (smoothingRate C n (natGap j k)) (profileScale_pos n)
      (positiveTiltedDensity m (orbit m p₀ n) -
        (shiftLeft^[natGap j k])
          (positiveTiltedDensity m (orbit m p₀ n)))
      (hSpatial n (natGap j k) hdistPos hdistL)
    rcases le_total j k with hjk' | hkj
    · have hadd : j + natGap j k = k := by
        rw [natGap_eq_of_le hjk']
        omega
      simpa only [Pi.sub_apply, shiftLeft_iterate_apply, hadd] using hs j
    · have hadd : k + natGap j k = j := by
        rw [natGap_comm, natGap_eq_of_le hkj]
        omega
      simpa only [Pi.sub_apply, shiftLeft_iterate_apply, hadd, abs_sub_comm] using hs k
  exact (mul_le_mul_of_nonneg_left hraw (sq_nonneg _)).trans
    (scaled_smoothingRate_le_sqrt hC heta hN hNL hdistPos hdistL hq)

theorem scaled_temporal_difference_le_sqrt
    (m : ℕ) (p₀ : ProbabilityMass)
    {C eta q : ℝ} {N n s j : ℕ}
    (hC : 0 ≤ C) (heta : 0 < eta) (hN : 0 < N)
    (hns : n ≤ s) (hNL : (N : ℝ) * eta ≤ profileScale n)
    (hdistL : s - n ≤ n + 1)
    (hq : ((s - n : ℕ) : ℝ) / (N : ℝ) ≤ q)
    (hTemporal : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      SupLE
        (positiveTiltedDensity m (orbit m p₀ (n + h)) -
          positiveTiltedDensity m (orbit m p₀ n))
        (smoothingRate C n h)) :
    (N : ℝ) ^ 2 *
        |positiveTiltedDensity m (orbit m p₀ s) j -
          positiveTiltedDensity m (orbit m p₀ n) j| ≤
      (2 * C / eta ^ 2) * Real.sqrt (q / eta) := by
  by_cases hnsEq : n = s
  · subst s
    simp
    positivity
  have hdistPos : 1 ≤ s - n := by omega
  have hraw := hTemporal n (s - n) hdistPos hdistL j
  have hadd : n + (s - n) = s := Nat.add_sub_of_le hns
  rw [hadd] at hraw
  exact (mul_le_mul_of_nonneg_left hraw (sq_nonneg _)).trans
    (scaled_smoothingRate_le_sqrt hC heta hN hNL hdistPos hdistL hq)

end

end DerridaRetaux.FixedArity
