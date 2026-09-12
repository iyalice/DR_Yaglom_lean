import DerridaRetaux.Main.ContinuumLaplaceMildIdentity
import DerridaRetaux.Main.ContinuumShiftedConvolutionLaplace
import DerridaRetaux.Main.ContinuumShiftedConvolutionLaplaceTriangle
import DerridaRetaux.Analysis.LaplaceMildDerivative
import DerridaRetaux.Analysis.HalfLineLaplaceIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Right derivative form of the Laplace equation, expressed in the forward
increment variable. -/
theorem subsequentialLaplace_hasDerivWithinAt_increment
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
    HasDerivWithinAt
      (fun h : ℝ ↦ continuumLaplace
        (fun x ↦ gluedExhaustionLimit g (t + h) x) p)
      (p * continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p -
        gluedExhaustionLimit g t 0 + (1 / 2 : ℝ) *
          continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p ^ 2)
      (Ici 0) 0 := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  have hmild : ∀ h : ℝ, 0 ≤ h →
      continuumLaplace (u (t + h)) p =
        shiftedHalfLineLaplace (u t) p h +
          ∫ s in t..t + h, (1 / 2 : ℝ) *
            shiftedHalfLineLaplace (positiveSelfConvolution (u s)) p
              (t + h - s) := by
    intro h hh
    simpa only [u] using subsequentialLaplaceMildIdentity
      m data phi g hphi hlim p hp t h ht hh
  have huFull : ContinuousOn (Function.uncurry u)
      (Ici t ×ˢ Ici (0 : ℝ)) := by
    simpa only [u] using subsequentialDensity_continuousOn_positiveHalfStrip
      m data phi g hlim t ht
  have hucont : ContinuousOn (u t) (Ici (0 : ℝ)) := by
    let emb : ℝ → ℝ × ℝ := fun x ↦ (t, x)
    change ContinuousOn ((Function.uncurry u) ∘ emb) (Ici (0 : ℝ))
    exact huFull.comp (by dsimp only [emb]; fun_prop) (fun x hx ↦ by
      dsimp only [emb]
      change t ≤ t ∧ (0 : ℝ) ≤ x
      exact ⟨le_rfl, hx⟩)
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u t x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hmass : IntegrableOn (u t) (Ici 0) := by
    simpa only [u, pow_zero, one_mul] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht 0 (by norm_num)
  have hLap : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u t x) (Ici 0) :=
    integrableOn_exp_neg_mul (u t) p hp hucont hunonneg hmass
  have htransport := hasDerivWithinAt_shiftedHalfLineLaplace_zero
    (u t) p hucont hLap
  have hshift := subsequentialShiftedConvolutionLaplace_continuousWithinAt
    m data phi g hphi hlim p hp t ht
  have hG : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ (1 / 2 : ℝ) * shiftedHalfLineLaplace
        (positiveSelfConvolution (u z.2)) p (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1} (0, t) :=
    continuousWithinAt_const.mul (by simpa only [u] using hshift)
  have hInt : ∀ h : ℝ, 0 ≤ h → IntervalIntegrable
      (fun s ↦ (1 / 2 : ℝ) * shiftedHalfLineLaplace
        (positiveSelfConvolution (u s)) p (t + h - s)) volume t (t + h) := by
    intro h hh
    have htri := subsequentialShiftedConvolutionLaplace_continuousOn_triangle
      m data phi g hphi hlim p hp t h ht hh
    have htimeCont : ContinuousOn
        (fun s : ℝ ↦ shiftedHalfLineLaplace
          (positiveSelfConvolution (u s)) p (t + h - s))
        (Icc t (t + h)) := by
      let emb : ℝ → ℝ × ℝ := fun s ↦ (h, s)
      change ContinuousOn
        ((fun z : ℝ × ℝ ↦ shiftedHalfLineLaplace
          (positiveSelfConvolution (u z.2)) p (t + z.1 - z.2)) ∘ emb)
          (Icc t (t + h))
      have htri' : ContinuousOn
          (fun z : ℝ × ℝ ↦ shiftedHalfLineLaplace
            (positiveSelfConvolution (u z.2)) p (t + z.1 - z.2))
          (closedDuhamelTriangle t h) := by
        simpa only [u] using htri
      exact htri'.comp (by dsimp only [emb]; fun_prop) (fun s hs ↦ by
        dsimp only [emb]
        exact ⟨hh, le_rfl, hs.1, by simpa using hs.2⟩)
    have htimeInt : IntegrableOn
        (fun s : ℝ ↦ (1 / 2 : ℝ) * shiftedHalfLineLaplace
          (positiveSelfConvolution (u s)) p (t + h - s))
        (Ioc t (t + h)) :=
      ((continuousOn_const.mul htimeCont).integrableOn_compact
        isCompact_Icc).mono_set Ioc_subset_Icc_self
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : t ≤ t + h)]
    exact htimeInt
  have hraw := hasDerivWithinAt_laplace_of_mildIdentity
    u p t (p * continuumLaplace (u t) p - u t 0)
      hmild htransport hG hInt
  have hconv := integral_exp_mul_positiveSelfConvolution (u t) p hLap
  apply hraw.congr_deriv
  rw [show continuumLaplace (positiveSelfConvolution (u t)) p =
      continuumLaplace (u t) p ^ 2 by exact hconv]

end

end DerridaRetaux.FixedArity
