import DerridaRetaux.Main.ContinuumMomentDuhamelIntegrability
import DerridaRetaux.Main.ContinuumMild
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The pointwise continuum mild equation may be integrated against every
monomial of degree at most three. -/
theorem subsequentialMomentMildIdentity
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t h : ℝ) (ht : 0 < t) (hh : 0 ≤ h)
    (r : ℕ) (hr : r ≤ 3) :
    continuumMoment (fun x ↦ gluedExhaustionLimit g (t + h) x) r =
      shiftedHalfLineMoment (fun x ↦ gluedExhaustionLimit g t x) r h +
        ∫ s in t..t + h, (1 / 2 : ℝ) * shiftedHalfLineMoment
          (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g s x)) r
            (t + h - s) := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  have hmild : ∀ x : ℝ, 0 ≤ x →
      u (t + h) x = u t (x + h) +
        ∫ s in t..t + h, (1 / 2 : ℝ) *
          positiveSelfConvolution (u s) (x + t + h - s) := by
    intro x hx
    have hsource := subsequentialMildEquation
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t (t + h) x ht (by linarith) hx
    dsimp only [u]
    convert hsource using 1 <;> ring
  have huFull : ContinuousOn (Function.uncurry u)
      (Ici t ×ˢ Ici (0 : ℝ)) := by
    simpa only [u] using
      subsequentialDensity_continuousOn_positiveHalfStrip
        m data phi g hlim t ht
  have hucont : ContinuousOn (u t) (Ici (0 : ℝ)) := by
    let emb : ℝ → ℝ × ℝ := fun x ↦ (t, x)
    change ContinuousOn ((Function.uncurry u) ∘ emb) (Ici (0 : ℝ))
    exact huFull.comp (by dsimp only [emb]; fun_prop)
      (fun x hx ↦ by
        dsimp only [emb]
        change t ≤ t ∧ (0 : ℝ) ≤ x
        exact ⟨le_rfl, hx⟩)
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u t x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ r * u t x) (Ici 0) := by
    simpa only [u] using
      subsequentialMoment_integrable
        m data.law data.arity data.critical data.third data.notBinaryFixedPoint
          phi g hphi hlim t ht r hr
  have hbase := integrableOn_shifted_pow_mul
    (u t) r h hh hucont hunonneg hint
  have hspace := subsequentialMomentDuhamelIntegrable
    m data phi g hphi hlim t h ht hh r hr
  exact momentMildIdentity_of_pointwise u r t h hh hmild hbase hspace

end

end DerridaRetaux.FixedArity
