import DerridaRetaux.Analysis.HigherSourceVanishing
import DerridaRetaux.Analysis.TimeRiemannLimit

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-- The higher-order Duhamel segment vanishes on literal positive floor-time
windows after quadratic profile rescaling. -/
theorem scaled_densityHigherSegment_floor_tendsto_zero
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / profileScale s)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t₀ t x : ℝ) (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    Tendsto
      (fun n ↦ (scale n : ℝ) ^ 2 *
        densityHigherSegment m p₀
          (gridIndex (scale n) t₀) (gridIndex (scale n) t)
          (gridIndex (scale n) x))
      atTop (nhds 0) := by
  have heta : 0 < t₀ / 2 := half_pos ht₀
  have hT : 0 ≤ t + 1 := by linarith
  have hNPos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  have hinvSmall : ∀ᶠ N : ℕ in atTop, (N : ℝ)⁻¹ < t₀ / 2 :=
    tendsto_inverse_atTop_nhds_zero_nat (Iio_mem_nhds heta)
  have han : ∀ᶠ N : ℕ in atTop,
      gridIndex N t₀ ≤ gridIndex N t :=
    Eventually.of_forall fun N ↦ gridIndex_mono_of_nonneg ht₀.le ht N
  have ha : ∀ᶠ N : ℕ in atTop,
      t₀ / 2 * (N : ℝ) ≤ profileScale (gridIndex N t₀) := by
    filter_upwards [hNPos, hinvSmall] with N hN hinvN
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hf := gridIndex_div_floor_bounds N t₀ hN ht₀.le
    have hlower : t₀ / 2 * (N : ℝ) ≤ (gridIndex N t₀ : ℝ) := by
      rw [← le_div_iff₀ hNreal]
      linarith [hf.2]
    exact hlower.trans (by
      simp only [profileScale, Nat.cast_add, Nat.cast_one]
      linarith)
  have hspan : ∀ᶠ N : ℕ in atTop,
      (((gridIndex N t - gridIndex N t₀ : ℕ) : ℕ) : ℝ) ≤
        (t + 1) * (N : ℝ) := by
    filter_upwards [hNPos] with N hN
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hb := gridIndex_cast_le N t (ht₀.le.trans ht)
    have hsub : gridIndex N t - gridIndex N t₀ ≤ gridIndex N t :=
      Nat.sub_le _ _
    have hcast : ((gridIndex N t - gridIndex N t₀ : ℕ) : ℝ) ≤
        (gridIndex N t : ℝ) := by exact_mod_cast hsub
    calc
      ((gridIndex N t - gridIndex N t₀ : ℕ) : ℝ) ≤
          (gridIndex N t : ℝ) := hcast
      _ ≤ (N : ℝ) * t := hb
      _ ≤ (t + 1) * (N : ℝ) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (by linarith) hNreal.le
  have hbase := densityHigherSegment_orbit_scaled_tendsto_zero_on_annulus
    m p₀ hm hcrit hthird A B hA hB hL1 hSup
      (t₀ / 2) (t + 1) heta hT
      (fun N ↦ gridIndex N t₀)
      (fun N ↦ gridIndex N t)
      (fun N ↦ gridIndex N x)
      han ha hspan
  simpa only [Function.comp_apply] using hbase.comp hscale

end

end DerridaRetaux
