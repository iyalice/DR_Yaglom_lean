import DerridaRetaux.Main.ContinuumLaplaceContinuity
import DerridaRetaux.Main.ContinuumShiftedConvolutionTriangle
import DerridaRetaux.Main.ContinuumMomentDuhamelIntegrability
import DerridaRetaux.Analysis.ShiftedLaplaceTriangleContinuity
import DerridaRetaux.Analysis.HalfLineLaplaceIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The shifted Laplace transform of the continuum convolution is continuous
on every compact forward Duhamel triangle. -/
theorem subsequentialShiftedConvolutionLaplace_continuousOn_triangle
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
    (t H : ℝ) (ht : 0 < t) (hH : 0 ≤ H) :
    ContinuousOn
      (fun z : ℝ × ℝ ↦ shiftedHalfLineLaplace
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g z.2 x)) p
          (t + z.1 - z.2)) (closedDuhamelTriangle t H) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  let v : ℝ → ℝ → ℝ := fun s ↦ positiveSelfConvolution (u s)
  have hu : ContinuousOn (Function.uncurry u)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H) := by
    simpa only [u] using continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m data.law) phi g hlim t (t + H) H ht
        (by linarith) hH
  have hv : ContinuousOn (Function.uncurry v)
      (Icc t (t + H) ×ˢ Icc (0 : ℝ) H) := by
    exact continuousOn_positiveSelfConvolution_uncurry
      u t (t + H) H (by linarith) hH hu
  have hU : ContinuousOn (fun s : ℝ ↦ continuumLaplace (u s) p)
      (Icc t (t + H)) := by
    simpa only [u] using subsequentialLaplace_continuousOn
      m data phi g hphi hlim p hp t (t + H) ht (by linarith)
  have huLap : ∀ s : ℝ, s ∈ Icc t (t + H) → IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u s x) (Ici 0) := by
    intro s hs
    have huFull := subsequentialDensity_continuousOn_positiveHalfStrip
      m data phi g hlim t ht
    have huSlice : ContinuousOn (u s) (Ici (0 : ℝ)) := by
      let emb : ℝ → ℝ × ℝ := fun x ↦ (s, x)
      change ContinuousOn ((Function.uncurry u) ∘ emb) (Ici (0 : ℝ))
      exact huFull.comp (by dsimp only [emb]; fun_prop)
        (fun x hx ↦ ⟨hs.1, hx⟩)
    have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u s x := by
      intro x hx
      exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
        phi g hphi hlim (ht.trans_le hs.1) hx
    have hmass : IntegrableOn (u s) (Ici 0) := by
      simpa only [u, pow_zero, one_mul] using subsequentialMoment_integrable
        m data.law data.arity data.critical data.third data.notBinaryFixedPoint
          phi g hphi hlim s (ht.trans_le hs.1) 0 (by norm_num)
    exact integrableOn_exp_neg_mul (u s) p hp huSlice hunonneg hmass
  have hB : ContinuousOn (fun s : ℝ ↦ continuumLaplace (v s) p)
      (Icc t (t + H)) := by
    apply (hU.pow 2).congr
    intro s hs
    simpa only [v] using integral_exp_mul_positiveSelfConvolution
      (u s) p (huLap s hs)
  have hvLap : ∀ s : ℝ, s ∈ Icc t (t + H) → IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * v s x) (Ici 0) := by
    intro s hs
    have hvFull := subsequentialConvolution_continuousOn_positiveHalfStrip
      m data phi g hlim t ht
    have hvSlice : ContinuousOn (v s) (Ici (0 : ℝ)) := by
      let emb : ℝ → ℝ × ℝ := fun x ↦ (s, x)
      change ContinuousOn ((Function.uncurry v) ∘ emb) (Ici (0 : ℝ))
      exact hvFull.comp (by dsimp only [emb]; fun_prop)
        (fun x hx ↦ ⟨hs.1, hx⟩)
    have hvnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ v s x := by
      intro x hx
      simpa only [v, u] using subsequentialConvolution_nonneg
        m data phi g hphi hlim (ht.trans_le hs.1) hx
    have hmass : IntegrableOn (v s) (Ici 0) := by
      simpa only [v, u, pow_zero, one_mul] using
        subsequentialConvolutionMoment_integrable
          m data phi g hphi hlim s (ht.trans_le hs.1) 0 (by norm_num)
    exact integrableOn_exp_neg_mul (v s) p hp hvSlice hvnonneg hmass
  simpa only [v, u] using continuousOn_shiftedHalfLineLaplace_triangle
    v p t H hH hv hB hvLap

end

end DerridaRetaux.FixedArity
