import DerridaRetaux.Main.ContinuumLaplaceContinuity
import DerridaRetaux.Main.ContinuumMomentDuhamelIntegrability
import DerridaRetaux.Analysis.ShiftedLaplaceContinuity
import DerridaRetaux.Analysis.HalfLineLaplaceIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The shifted convolution Laplace transform is continuous at the collapsed
Duhamel endpoint along the forward integration triangle. -/
theorem subsequentialShiftedConvolutionLaplace_continuousWithinAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 ≤ p) (t : ℝ) (ht : 0 < t) :
    ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ shiftedHalfLineLaplace
        (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g z.2 x)) p
          (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1}
      (0, t) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  let v : ℝ → ℝ → ℝ := fun s ↦ positiveSelfConvolution (u s)
  have huBox : ContinuousOn (Function.uncurry u)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [u] using continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m data.law) phi g hlim (t / 2) (t + 1) 1
        (half_pos ht) (by linarith) (by norm_num)
  have hvBox : ContinuousOn (Function.uncurry v)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) 1) := by
    exact continuousOn_positiveSelfConvolution_uncurry
      u (t / 2) (t + 1) 1 (by linarith) (by norm_num) huBox
  have hU : ContinuousOn (fun s : ℝ ↦ continuumLaplace (u s) p)
      (Icc t (t + 1)) := by
    simpa only [u] using subsequentialLaplace_continuousOn
      m data phi g hphi hlim p hp t (t + 1) ht (by linarith)
  have huLap : ∀ s : ℝ, t ≤ s → IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u s x) (Ici 0) := by
    intro s hs
    have huFull := subsequentialDensity_continuousOn_positiveHalfStrip
      m data phi g hlim t ht
    have huSlice : ContinuousOn (u s) (Ici (0 : ℝ)) := by
      let emb : ℝ → ℝ × ℝ := fun x ↦ (s, x)
      change ContinuousOn ((Function.uncurry u) ∘ emb) (Ici (0 : ℝ))
      exact huFull.comp (by dsimp only [emb]; fun_prop) (fun x hx ↦ by
        dsimp only [emb]
        change t ≤ s ∧ (0 : ℝ) ≤ x
        exact ⟨hs, hx⟩)
    have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u s x := by
      intro x hx
      exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
        phi g hphi hlim (ht.trans_le hs) hx
    have hmass : IntegrableOn (u s) (Ici 0) := by
      simpa only [u, pow_zero, one_mul] using subsequentialMoment_integrable
        m data.law data.arity data.critical data.third data.notBinaryFixedPoint
          phi g hphi hlim s (ht.trans_le hs) 0 (by norm_num)
    exact integrableOn_exp_neg_mul (u s) p hp huSlice hunonneg hmass
  have hB : ContinuousOn (fun s : ℝ ↦ continuumLaplace (v s) p)
      (Icc t (t + 1)) := by
    apply (hU.pow 2).congr
    intro s hs
    simpa only [v] using integral_exp_mul_positiveSelfConvolution
      (u s) p (huLap s hs.1)
  have hvFull : ContinuousOn (Function.uncurry v)
      (Ici t ×ˢ Ici (0 : ℝ)) := by
    simpa only [v] using subsequentialConvolution_continuousOn_positiveHalfStrip
      m data phi g hlim t ht
  have hvLap : ∀ s : ℝ, t ≤ s → IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * v s x) (Ici 0) := by
    intro s hs
    have hvSlice : ContinuousOn (v s) (Ici (0 : ℝ)) := by
      let emb : ℝ → ℝ × ℝ := fun x ↦ (s, x)
      change ContinuousOn ((Function.uncurry v) ∘ emb) (Ici (0 : ℝ))
      exact hvFull.comp (by dsimp only [emb]; fun_prop) (fun x hx ↦ by
        dsimp only [emb]
        change t ≤ s ∧ (0 : ℝ) ≤ x
        exact ⟨hs, hx⟩)
    have hvnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ v s x := by
      intro x hx
      simpa only [v, u] using subsequentialConvolution_nonneg
        m data phi g hphi hlim (ht.trans_le hs) hx
    have hmass : IntegrableOn (v s) (Ici 0) := by
      simpa only [v, u, pow_zero, one_mul] using
        subsequentialConvolutionMoment_integrable
          m data phi g hphi hlim s (ht.trans_le hs) 0 (by norm_num)
    exact integrableOn_exp_neg_mul (v s) p hp hvSlice hvnonneg hmass
  simpa only [v, u] using continuousWithinAt_shiftedHalfLineLaplace
    v p t ht hvBox hB hvLap

end

end DerridaRetaux.FixedArity
