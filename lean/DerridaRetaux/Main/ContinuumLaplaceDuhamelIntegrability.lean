import DerridaRetaux.Main.ContinuumMomentDuhamelIntegrability
import DerridaRetaux.Analysis.LaplaceDuhamelIntegrability

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The Laplace-weighted continuum Duhamel kernel is integrable in space-time
on every finite forward interval. -/
theorem subsequentialLaplaceDuhamelIntegrable
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 ≤ p)
    (t h : ℝ) (ht : 0 < t) (hh : 0 ≤ h) :
    Integrable
      (laplaceDuhamelIntegrand
        (fun s ↦ positiveSelfConvolution
          (fun x ↦ gluedExhaustionLimit g s x)) p t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
  let v : ℝ → ℝ → ℝ := fun s ↦
    positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g s x)
  have hvcont : ContinuousOn (Function.uncurry v)
      (Ici t ×ˢ Ici (0 : ℝ)) := by
    simpa only [v] using
      subsequentialConvolution_continuousOn_positiveHalfStrip
        m data phi g hlim t ht
  have hvnonneg : ∀ s x : ℝ, t ≤ s → 0 ≤ x → 0 ≤ v s x := by
    intro s x hs hx
    simpa only [v] using subsequentialConvolution_nonneg
      m data phi g hphi hlim (ht.trans_le hs) hx
  have hmass0 := subsequentialMomentDuhamelIntegrable
    m data phi g hphi hlim t h ht hh 0 (by norm_num)
  have hmass : Integrable (weightedShiftedKernel v 0 t h)
      ((volume.restrict (Ici (0 : ℝ))).prod
        (volume.restrict (Ioc t (t + h)))) := by
    simpa only [weightedShiftedKernel, momentDuhamelIntegrand, v] using hmass0
  simpa only [v] using integrable_laplaceDuhamelIntegrand_of_mass
    v p t h hp hvcont hvnonneg hmass

end

end DerridaRetaux.FixedArity
