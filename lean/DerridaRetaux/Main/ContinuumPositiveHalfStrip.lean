import DerridaRetaux.Main.ContinuumConvolutionMoments
import DerridaRetaux.Analysis.ConvolutionContinuityOn
import DerridaRetaux.Analysis.PositiveHalfStripContinuity

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

theorem subsequentialDensity_continuousOn_positiveHalfStrip
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (eta : ℝ) (heta : 0 < eta) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦ gluedExhaustionLimit g p.1 p.2)
      (Ici eta ×ˢ Ici (0 : ℝ)) := by
  apply continuousOn_positiveHalfStrip_of_compactBoxes
  intro T R hetaT hR
  exact continuousOn_gluedExhaustionLimit_compactBox
    (orbitScaledGrid m data.law) phi g hlim eta T R heta hetaT hR

theorem subsequentialConvolution_continuousOn_positiveHalfStrip
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (eta : ℝ) (heta : 0 < eta) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦ positiveSelfConvolution
        (fun x ↦ gluedExhaustionLimit g p.1 x) p.2)
      (Ici eta ×ˢ Ici (0 : ℝ)) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  have huFull : ContinuousOn (Function.uncurry u)
      (Ici eta ×ˢ Ici (0 : ℝ)) := by
    simpa only [u] using
      subsequentialDensity_continuousOn_positiveHalfStrip
        m data phi g hlim eta heta
  apply continuousOn_positiveHalfStrip_of_compactBoxes
  intro T R hetaT hR
  have huBox : ContinuousOn (Function.uncurry u)
      (Icc eta T ×ˢ Icc (0 : ℝ) R) :=
    huFull.mono (fun z hz ↦ ⟨hz.1.1, hz.2.1⟩)
  simpa only [u] using continuousOn_positiveSelfConvolution_uncurry
    u eta T R hetaT hR huBox

end

end DerridaRetaux.FixedArity
