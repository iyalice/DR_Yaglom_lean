import DerridaRetaux.Main.ContinuumShiftedConvolution
import DerridaRetaux.Analysis.ShiftedMomentTriangleContinuity
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The shifted convolution moment is continuous on every compact forward
Duhamel triangle. -/
theorem subsequentialShiftedConvolutionMoment_continuousOn_triangle
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t H : ℝ) (ht : 0 < t) (hH : 0 ≤ H)
    (r : ℕ) (hr : r ≤ 3) :
    ContinuousOn
      (fun z : ℝ × ℝ ↦ shiftedHalfLineMoment
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g z.2 x)) r
          (t + z.1 - z.2)) (closedDuhamelTriangle t H) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  let v : ℝ → ℝ → ℝ := fun s ↦ positiveSelfConvolution (u s)
  have hu : ContinuousOn (Function.uncurry u)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H) := by
    simpa only [u] using
      continuousOn_gluedExhaustionLimit_compactBox
        (orbitScaledGrid m data.law) phi g hlim t (t + H) H ht
          (by linarith) hH
  have hv : ContinuousOn (Function.uncurry v)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H) := by
    exact continuousOn_positiveSelfConvolution_uncurry
      u t (t + H) H (by linarith) hH hu
  have hB : ∀ k : ℕ, k ≤ r → ContinuousOn
      (fun s : ℝ ↦ continuumMoment (v s) k) (Icc t (t + H)) := by
    intro k hk
    simpa only [v, u] using
      subsequentialConvolutionMoment_continuousOn m data phi g hphi hlim
        k (hk.trans hr) t (t + H) ht (by linarith)
  have hmom : ∀ s : ℝ, s ∈ Icc t (t + H) → ∀ k : ℕ, k ≤ r →
      IntegrableOn (fun x : ℝ ↦ x ^ k * v s x) (Ici 0) := by
    intro s hs k hk
    simpa only [v, u] using
      subsequentialConvolutionMoment_integrable m data phi g hphi hlim
        s (ht.trans_le hs.1) k (hk.trans hr)
  simpa only [v, u] using
    continuousOn_shiftedHalfLineMoment_triangle v r t H hH hv hB hmom

end

end DerridaRetaux.FixedArity
