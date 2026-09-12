import DerridaRetaux.Analysis.ProfileCompactnessInterpolant
import DerridaRetaux.Analysis.TimeRiemannLimit

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

theorem clampedOrbitScaledGrid_eq_of_time_ge
    (m : ℕ) (p₀ : ProbabilityMass) {eta : ℝ} {N n j : ℕ}
    (hrow : gridIndex N eta ≤ n) :
    clampedOrbitScaledGrid m p₀ eta N n j = orbitScaledGrid m p₀ N n j := by
  simp [clampedOrbitScaledGrid, max_eq_left hrow]

/-- On a rectangle whose lower time edge is `eta`, clamping rows below `eta` does not alter the
bilinear interpolant. -/
theorem gridBilinearInterp_clamped_eq_of_time_ge
    (m : ℕ) (p₀ : ProbabilityMass) {eta t x : ℝ} {N : ℕ}
    (hN : 0 < N) (heta : 0 ≤ eta) (ht : eta ≤ t) :
    gridBilinearInterp N (clampedOrbitScaledGrid m p₀ eta N) t x =
      gridBilinearInterp N (orbitScaledGrid m p₀ N) t x := by
  have hindex : gridIndex N eta ≤ gridIndex N t :=
    gridIndex_mono_of_nonneg heta ht N
  have hindexSucc : gridIndex N eta ≤ gridIndex N t + 1 :=
    hindex.trans (Nat.le_succ _)
  rw [gridBilinearInterp_eq_four_weights N _ t x hN,
    gridBilinearInterp_eq_four_weights N _ t x hN]
  simp only [clampedOrbitScaledGrid_eq_of_time_ge m p₀ hindex,
    clampedOrbitScaledGrid_eq_of_time_ge m p₀ hindexSucc]

theorem orbitInterpolants_eventuallyUniformlyBoundedOn_rectangle
    (m : ℕ) (p₀ : ProbabilityMass) {C eta T R : ℝ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (C / profileScale n ^ 2)) :
    EventuallyUniformlyBoundedOn
      (fun N p ↦ gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2)
      (compactRectangle eta T R) := by
  obtain ⟨B, N₀, hB⟩ :=
    clampedOrbitInterpolants_eventuallyUniformlyBoundedOn
      m p₀ (C := C) (T := T) (R := R) hC heta hSup
  refine ⟨B, max 1 N₀, ?_⟩
  intro N hN p hp
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 N₀) hN)
  change |gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2| ≤ B
  rw [← gridBilinearInterp_clamped_eq_of_time_ge m p₀ hNpos heta.le hp.1.1]
  exact hB N (le_trans (le_max_right 1 N₀) hN) p hp

theorem orbitInterpolants_eventuallyEquicontinuousOn_rectangle
    (m : ℕ) (p₀ : ProbabilityMass) {C eta T R : ℝ}
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
    EventuallyEquicontinuousOnL1
      (fun N p ↦ gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2)
      (compactRectangle eta T R) := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, N₀, htail⟩ :=
    clampedOrbitInterpolants_eventuallyEquicontinuousOn
      m p₀ (C := C) (T := T) (R := R) hC heta hSup hSpatial hTemporal
      epsilon hepsilon
  refine ⟨delta, hdelta, max 1 N₀, ?_⟩
  intro N hN p hp q hq hpq
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 N₀) hN)
  change |gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2 - gridBilinearInterp N (orbitScaledGrid m p₀ N) q.1 q.2| < epsilon
  rw [← gridBilinearInterp_clamped_eq_of_time_ge m p₀ hNpos heta.le hp.1.1,
    ← gridBilinearInterp_clamped_eq_of_time_ge m p₀ hNpos heta.le hq.1.1]
  exact htail N (le_trans (le_max_right 1 N₀) hN) p hp q hq hpq

theorem orbitInterpolants_eventuallyUniformlyBoundedOn_exhaustion
    (m : ℕ) (p₀ : ProbabilityMass) {C : ℝ}
    (hC : 0 ≤ C)
    (hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (C / profileScale n ^ 2)) :
    ∀ k, EventuallyUniformlyBoundedOn
      (fun N p ↦ gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2)
      (gridExhaustionRectangle k) := by
  intro k
  exact orbitInterpolants_eventuallyUniformlyBoundedOn_rectangle
    m p₀ hC (by positivity) hSup

theorem orbitInterpolants_eventuallyEquicontinuousOn_exhaustion
    (m : ℕ) (p₀ : ProbabilityMass) {C : ℝ}
    (hC : 0 ≤ C)
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
    ∀ k, EventuallyEquicontinuousOnL1
      (fun N p ↦ gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2)
      (gridExhaustionRectangle k) := by
  intro k
  exact orbitInterpolants_eventuallyEquicontinuousOn_rectangle
    m p₀ hC (by positivity) hSup hSpatial hTemporal

/-- Compactness extracted internally from the source sup and smoothing estimates. -/
theorem orbitScaledGrid_compactness
    (m : ℕ) (p₀ : ProbabilityMass) {C : ℝ}
    (hC : 0 ≤ C)
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
    ∃ g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ,
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧ Tendsto phi atTop atTop ∧
          ∀ k, TendstoUniformly
            (fun n (p : gridExhaustionRectangle k) ↦
              gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
                (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
            (fun p ↦ g k p) atTop := by
  apply exists_gridBilinearInterp_diagonal_subsequence (orbitScaledGrid m p₀)
  · exact orbitInterpolants_eventuallyUniformlyBoundedOn_exhaustion m p₀ hC hSup
  · exact orbitInterpolants_eventuallyEquicontinuousOn_exhaustion
      m p₀ hC hSup hSpatial hTemporal

end

end DerridaRetaux.FixedArity
