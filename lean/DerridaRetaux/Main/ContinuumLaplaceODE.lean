import DerridaRetaux.Main.ContinuumLaplaceRightDerivative
import DerridaRetaux.Analysis.RightDerivativeClosure
import DerridaRetaux.Analysis.PositiveTimeContinuity

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The continuum Laplace transform satisfies its classical Riccati equation
at every positive time and every nonnegative Laplace parameter. -/
theorem subsequentialLaplaceODE
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 ≤ p) :
    ∀ t : ℝ, 0 < t →
      HasDerivAt
        (fun s : ℝ ↦ continuumLaplace
          (fun x ↦ gluedExhaustionLimit g s x) p)
        (p * continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p -
          gluedExhaustionLimit g t 0 + (1 / 2 : ℝ) *
            continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p ^ 2) t := by
  let U : ℝ → ℝ := fun t ↦
    continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p
  let beta : ℝ → ℝ := fun t ↦ gluedExhaustionLimit g t 0
  have hU : ContinuousOn U (Ioi (0 : ℝ)) := by
    apply continuousOn_Ioi_of_continuousOn_compactIntervals
    intro eta T heta hetaT
    simpa only [U] using subsequentialLaplace_continuousOn
      m data phi g hphi hlim p hp eta T heta hetaT
  have hbeta : ContinuousOn beta (Ioi (0 : ℝ)) := by
    apply continuousOn_Ioi_of_continuousOn_compactIntervals
    intro eta T heta hetaT
    have hbox := continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m data.law) phi g hlim eta T 0 heta hetaT le_rfl
    let emb : ℝ → ℝ × ℝ := fun t ↦ (t, 0)
    change ContinuousOn
      ((fun q : ℝ × ℝ ↦ gluedExhaustionLimit g q.1 q.2) ∘ emb)
        (Icc eta T)
    exact hbox.comp (by dsimp only [emb]; fun_prop) (fun t ht ↦ by
      dsimp only [emb]
      exact ⟨ht, ⟨le_rfl, le_rfl⟩⟩)
  have hright : ∀ t : ℝ, 0 < t → HasDerivWithinAt U
      (p * U t - beta t + (1 / 2 : ℝ) * U t ^ 2) (Ici t) t := by
    intro t ht
    have hinc := subsequentialLaplace_hasDerivWithinAt_increment
      m data phi g hphi hlim p hp t ht
    simpa only [U, beta] using hasDerivWithinAt_Ici_of_increment U hinc
  have hfield : ContinuousOn
      (fun t ↦ p * U t - beta t + (1 / 2 : ℝ) * U t ^ 2)
      (Ioi (0 : ℝ)) :=
    ((continuousOn_const.mul hU).sub hbeta).add
      (continuousOn_const.mul (hU.pow 2))
  intro t ht
  exact hasDerivAt_of_continuous_rightDeriv U
    (fun s ↦ p * U s - beta s + (1 / 2 : ℝ) * U s ^ 2)
    hU hfield hright ht

end

end DerridaRetaux.FixedArity
