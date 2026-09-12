import DerridaRetaux.Analysis.ProfileCompactnessOrbit

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

theorem EventuallyUniformlyBoundedOn.comp_tendsto_atTop
    {F : ℕ → (ℝ × ℝ) → ℝ} {K : Set (ℝ × ℝ)} {ns : ℕ → ℕ}
    (hF : EventuallyUniformlyBoundedOn F K)
    (hns : Tendsto ns atTop atTop) :
    EventuallyUniformlyBoundedOn (fun n ↦ F (ns n)) K := by
  obtain ⟨C, N₀, hC⟩ := hF
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hns (eventually_ge_atTop N₀))
  exact ⟨C, n₀, fun n hn ↦ hC (ns n) (hn₀ n hn)⟩

theorem EventuallyEquicontinuousOnL1.comp_tendsto_atTop
    {F : ℕ → (ℝ × ℝ) → ℝ} {K : Set (ℝ × ℝ)} {ns : ℕ → ℕ}
    (hF : EventuallyEquicontinuousOnL1 F K)
    (hns : Tendsto ns atTop atTop) :
    EventuallyEquicontinuousOnL1 (fun n ↦ F (ns n)) K := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, N₀, htail⟩ := hF epsilon hepsilon
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hns (eventually_ge_atTop N₀))
  refine ⟨delta, hdelta, n₀, ?_⟩
  intro n hn
  exact htail (ns n) (hn₀ n hn)

end

namespace FixedArity

noncomputable section

/-- Every cofinal reindexing of the orbit interpolants has a further subsequence converging
uniformly on all exhaustion rectangles. -/
theorem orbitScaledGrid_compactness_after
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
        (smoothingRate C n h))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ,
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧ Tendsto phi atTop atTop ∧
          ∀ k, TendstoUniformly
            (fun n (p : gridExhaustionRectangle k) ↦
              gridBilinearInterp (ns (phi n)) (orbitScaledGrid m p₀ (ns (phi n)))
                (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
            (fun p ↦ g k p) atTop := by
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2
  apply exists_diagonal_subsequence_of_eventuallyOn_exhaustion
    (fun n ↦ F (ns n)) (fun n ↦ (continuous_gridBilinearInterp
      (ns n) (orbitScaledGrid m p₀ (ns n))))
  · intro k
    exact (orbitInterpolants_eventuallyUniformlyBoundedOn_exhaustion
      m p₀ hC hSup k).comp_tendsto_atTop hns
  · intro k
    exact (orbitInterpolants_eventuallyEquicontinuousOn_exhaustion
      m p₀ hC hSup hSpatial hTemporal k).comp_tendsto_atTop hns

end


end DerridaRetaux.FixedArity
