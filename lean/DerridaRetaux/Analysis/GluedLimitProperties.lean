import DerridaRetaux.Analysis.TerminalReadoutLimit

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Every glued orbit limit is nonnegative on positive time and nonnegative
space, inherited from the lattice densities through the moving-node readout. -/
theorem gluedExhaustionLimit_nonneg
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    0 ≤ gluedExhaustionLimit g t x := by
  obtain ⟨R, hR⟩ := exists_nat_ge (x + 1)
  have hread := scaled_terminalDensity_tendsto
    m p₀ phi g t x R ht hx hR hphi hlim
  apply ge_of_tendsto hread
  filter_upwards [] with n
  exact mul_nonneg (sq_nonneg _) <|
    positiveTiltedDensity_nonneg m
      (orbit m p₀ (gridIndex (phi n) t)) (by omega)
      (orbit_critical m p₀ (by omega) hcrit _) _


end

end DerridaRetaux
