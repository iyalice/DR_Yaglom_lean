import DerridaRetaux.Main.ContinuumMomentODE
import DerridaRetaux.Main.ContinuumLaplaceODE

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Source-facing Lemma `lem:momentODE`: all three moment equations and the
Laplace equation hold classically at every positive time. -/
theorem momentLaplaceODE
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop) :
    let A : ℕ → ℝ → ℝ := fun r t ↦
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) r
    let U : ℝ → ℝ → ℝ := fun t p ↦
      continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p
    let beta : ℝ → ℝ := fun t ↦ gluedExhaustionLimit g t 0
    (∀ t : ℝ, 0 < t →
      HasDerivAt (A 0) (-beta t + (1 / 2 : ℝ) * A 0 t ^ 2) t) ∧
    (∀ t : ℝ, 0 < t →
      HasDerivAt (A 2) (A 0 t * A 2 t - 1) t) ∧
    (∀ t : ℝ, 0 < t →
      HasDerivAt (A 3) (A 0 t * A 3 t) t) ∧
    (∀ p : ℝ, 0 ≤ p → ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s ↦ U s p)
        (p * U t p + (1 / 2 : ℝ) * U t p ^ 2 - beta t) t) := by
  dsimp only
  have hmom := subsequentialMomentODE m data phi g hphi hlim
  refine ⟨hmom.1, hmom.2.1, hmom.2.2, ?_⟩
  intro p hp t ht
  have h := subsequentialLaplaceODE m data phi g hphi hlim p hp t ht
  convert h using 1 <;> ring

end

end DerridaRetaux.FixedArity
