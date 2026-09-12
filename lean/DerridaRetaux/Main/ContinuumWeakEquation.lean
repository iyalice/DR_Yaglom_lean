import DerridaRetaux.Analysis.YaglomWeakEquation
import DerridaRetaux.Main.IdentificationFinal

/-!
# The concrete time-integrated weak equation

This closes source obligation U46 for every locally uniform subsequential limit.  The
boundary term is the literal trace `-phi 0 * u t 0`; no boundary condition is assumed.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- U46: every subsequential continuum density satisfies the time-integrated weak
Derrida--Retaux equation for compactly supported `C¹` tests on positive-time windows. -/
theorem subsequentialHasWeakEquationOn
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (eta T : ℝ) (heta : 0 < eta) :
    HasWeakEquationOn (fun t x ↦ gluedExhaustionLimit g t x) (Icc eta T) := by
  apply hasWeakEquationOn_congr_Icc
    (v := fun t x ↦ yaglomDensity t x)
  · intro t ht x hx
    have hid := identifySubsequentialLimit m data phi g hphi hlim
      t x (heta.trans_le ht.1) hx
    simpa only [yaglomDensity] using hid
  · exact yaglomDensity_hasWeakEquationOn eta T heta

end

end DerridaRetaux.FixedArity
