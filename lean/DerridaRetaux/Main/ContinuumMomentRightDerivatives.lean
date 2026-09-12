import DerridaRetaux.Main.ContinuumMomentMildIdentity
import DerridaRetaux.Analysis.MomentMildDerivative
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Right derivative form of the zeroth-moment equation. -/
theorem subsequentialMoment_zero_hasDerivWithinAt_increment
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt
      (fun h : ℝ ↦ continuumMoment
        (fun x ↦ gluedExhaustionLimit g (t + h) x) 0)
      (-gluedExhaustionLimit g t 0 +
        (1 / 2 : ℝ) * continuumMoment
          (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g t x)) 0)
      (Ici 0) 0 := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  have hmild : ∀ h : ℝ, 0 ≤ h →
      continuumMoment (u (t + h)) 0 =
        shiftedHalfLineMoment (u t) 0 h +
          ∫ s in t..t + h, (1 / 2 : ℝ) * shiftedHalfLineMoment
            (positiveSelfConvolution (u s)) 0 (t + h - s) := by
    intro h hh
    simpa only [u] using subsequentialMomentMildIdentity
      m data phi g hphi hlim t h ht hh 0 (by norm_num)
  have huFull : ContinuousOn (Function.uncurry u)
      (Ici t ×ˢ Ici (0 : ℝ)) := by
    simpa only [u] using
      subsequentialDensity_continuousOn_positiveHalfStrip
        m data phi g hlim t ht
  have hucont : ContinuousOn (u t) (Ici (0 : ℝ)) := by
    let emb : ℝ → ℝ × ℝ := fun x ↦ (t, x)
    change ContinuousOn ((Function.uncurry u) ∘ emb) (Ici (0 : ℝ))
    exact huFull.comp (by dsimp only [emb]; fun_prop) (fun x hx ↦ by
      dsimp only [emb]
      change t ≤ t ∧ (0 : ℝ) ≤ x
      exact ⟨le_rfl, hx⟩)
  have h0 : IntegrableOn (u t) (Ici 0) := by
    simpa only [u, pow_zero, one_mul] using
      subsequentialMoment_integrable
        m data.law data.arity data.critical data.third data.notBinaryFixedPoint
          phi g hphi hlim t ht 0 (by norm_num)
  have htransport := hasDerivWithinAt_shiftedHalfLineMoment_zero
    (u t) hucont h0
  have hshift := subsequentialShiftedConvolution_zero_continuousWithinAt
    m data phi g hphi hlim t ht
  have hG : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ (1 / 2 : ℝ) * shiftedHalfLineMoment
        (positiveSelfConvolution (u z.2)) 0 (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1} (0, t) :=
    continuousWithinAt_const.mul hshift
  have hInt : ∀ h : ℝ, 0 ≤ h → IntervalIntegrable
      (fun s ↦ (1 / 2 : ℝ) * shiftedHalfLineMoment
        (positiveSelfConvolution (u s)) 0 (t + h - s)) volume t (t + h) := by
    intro h hh
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : t ≤ t + h)]
    simpa only [u] using
      subsequentialShiftedConvolutionMoment_integrableOn_time
        m data phi g hphi hlim t h ht hh 0 (by norm_num)
  simpa only [u] using hasDerivWithinAt_moment_of_mildIdentity
    u 0 t (-u t 0) hmild htransport hG hInt

end

end DerridaRetaux.FixedArity
