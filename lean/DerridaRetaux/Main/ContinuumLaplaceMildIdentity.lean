import DerridaRetaux.Main.ContinuumLaplaceDuhamelIntegrability
import DerridaRetaux.Main.ContinuumMild
import DerridaRetaux.Analysis.LaplaceMildIdentity
import DerridaRetaux.Analysis.HalfLineLaplaceIntegrability
import DerridaRetaux.Analysis.ShiftedMomentIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The continuum mild equation integrated against every nonnegative-parameter
half-line Laplace function. -/
theorem subsequentialLaplaceMildIdentity
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
    continuumLaplace (fun x ↦ gluedExhaustionLimit g (t + h) x) p =
      shiftedHalfLineLaplace (fun x ↦ gluedExhaustionLimit g t x) p h +
        ∫ s in t..t + h, (1 / 2 : ℝ) * shiftedHalfLineLaplace
          (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g s x)) p
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
    simpa only [u] using subsequentialDensity_continuousOn_positiveHalfStrip
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
  have hmass : IntegrableOn (u t) (Ici 0) := by
    simpa only [u, pow_zero, one_mul] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht 0 (by norm_num)
  have hshiftMass : IntegrableOn (fun x : ℝ ↦ u t (x + h)) (Ici 0) := by
    simpa only [pow_zero, one_mul] using integrableOn_shifted_pow_mul
      (u t) 0 h hh hucont hunonneg
        (by simpa only [pow_zero, one_mul] using hmass)
  have hshiftCont : ContinuousOn (fun x : ℝ ↦ u t (x + h))
      (Ici (0 : ℝ)) :=
    hucont.comp (continuous_id.add continuous_const).continuousOn
      (fun x hx ↦ add_nonneg hx hh)
  have hshiftNonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u t (x + h) := by
    intro x hx
    exact hunonneg (x + h) (add_nonneg hx hh)
  have hbase : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-(p * x)) * u t (x + h)) (Ici 0) :=
    integrableOn_exp_neg_mul (fun x ↦ u t (x + h)) p hp
      hshiftCont hshiftNonneg hshiftMass
  have hspace := subsequentialLaplaceDuhamelIntegrable
    m data phi g hphi hlim p hp t h ht hh
  exact laplaceMildIdentity_of_pointwise u p t h hh hmild hbase hspace

end

end DerridaRetaux.FixedArity
