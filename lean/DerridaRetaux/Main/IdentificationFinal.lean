import DerridaRetaux.Main.ContinuumProfile

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Proposition `prop:identification`: every locally uniform subsequential limit is the explicit
Yaglom profile. -/
theorem identifySubsequentialLimit
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop) :
    ∀ t x : ℝ, 0 < t → 0 ≤ x →
      gluedExhaustionLimit g t x = 4 / t ^ 2 * Real.exp (-2 * x / t) := by
  exact subsequentialDensity_eq_yaglom m data phi g hphi hlim
    (κ := 1) (by norm_num)

end

end DerridaRetaux.FixedArity
