import DerridaRetaux.Main.ContinuumMomentODERight
import DerridaRetaux.Analysis.PositiveTimeContinuity

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Source equation `eq:momentODE`: the zeroth, second and third moments of
every glued subsequential limit satisfy the stated classical ODEs at every
positive time. -/
theorem subsequentialMomentODE
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    let A : ℕ → ℝ → ℝ := fun r t ↦
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) r
    let beta : ℝ → ℝ := fun t ↦ gluedExhaustionLimit g t 0
    (∀ t : ℝ, 0 < t →
      HasDerivAt (A 0) (-beta t + (1 / 2 : ℝ) * A 0 t ^ 2) t) ∧
    (∀ t : ℝ, 0 < t →
      HasDerivAt (A 2) (A 0 t * A 2 t - 1) t) ∧
    (∀ t : ℝ, 0 < t →
      HasDerivAt (A 3) (A 0 t * A 3 t) t) := by
  dsimp only
  let A : ℕ → ℝ → ℝ := fun r t ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) r
  let beta : ℝ → ℝ := fun t ↦ gluedExhaustionLimit g t 0
  have hA : ∀ r : ℕ, r ≤ 3 → ContinuousOn (A r) (Ioi (0 : ℝ)) := by
    intro r hr
    apply continuousOn_Ioi_of_continuousOn_compactIntervals
    intro eta T heta hetaT
    simpa only [A] using subsequentialMoment_continuousOn
      m data phi g hphi hlim r hr eta T heta hetaT
  have hbeta : ContinuousOn beta (Ioi (0 : ℝ)) := by
    apply continuousOn_Ioi_of_continuousOn_compactIntervals
    intro eta T heta hetaT
    have hbox := continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m data.law) phi g hlim eta T 0 heta hetaT le_rfl
    let emb : ℝ → ℝ × ℝ := fun t ↦ (t, 0)
    change ContinuousOn
      ((fun p : ℝ × ℝ ↦ gluedExhaustionLimit g p.1 p.2) ∘ emb)
        (Icc eta T)
    exact hbox.comp (by dsimp only [emb]; fun_prop) (fun t ht ↦ by
      dsimp only [emb]
      exact ⟨ht, ⟨le_rfl, le_rfl⟩⟩)
  have hright0 : ∀ t : ℝ, 0 < t →
      HasDerivWithinAt (A 0)
        (-beta t + (1 / 2 : ℝ) * A 0 t ^ 2) (Ici t) t := by
    intro t ht
    simpa only [A, beta] using
      subsequentialMoment_zero_hasDerivWithinAt m data phi g hphi hlim t ht
  have hright2 : ∀ t : ℝ, 0 < t →
      HasDerivWithinAt (A 2) (A 0 t * A 2 t - 1) (Ici t) t := by
    intro t ht
    simpa only [A] using
      subsequentialMoment_two_hasDerivWithinAt m data phi g hphi hlim t ht
  have hright3 : ∀ t : ℝ, 0 < t →
      HasDerivWithinAt (A 3) (A 0 t * A 3 t) (Ici t) t := by
    intro t ht
    simpa only [A] using
      subsequentialMoment_three_hasDerivWithinAt m data phi g hphi hlim t ht
  have hfield0 : ContinuousOn
      (fun t ↦ -beta t + (1 / 2 : ℝ) * A 0 t ^ 2) (Ioi (0 : ℝ)) :=
    hbeta.neg.add (continuousOn_const.mul ((hA 0 (by norm_num)).pow 2))
  have hfield2 : ContinuousOn
      (fun t ↦ A 0 t * A 2 t - 1) (Ioi (0 : ℝ)) :=
    ((hA 0 (by norm_num)).mul (hA 2 (by norm_num))).sub continuousOn_const
  have hfield3 : ContinuousOn
      (fun t ↦ A 0 t * A 3 t) (Ioi (0 : ℝ)) :=
    (hA 0 (by norm_num)).mul (hA 3 (by norm_num))
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hasDerivAt_of_continuous_rightDeriv (A 0)
      (fun s ↦ -beta s + (1 / 2 : ℝ) * A 0 s ^ 2)
      (hA 0 (by norm_num)) hfield0 hright0 ht
  · intro t ht
    exact hasDerivAt_of_continuous_rightDeriv (A 2)
      (fun s ↦ A 0 s * A 2 s - 1)
      (hA 2 (by norm_num)) hfield2 hright2 ht
  · intro t ht
    exact hasDerivAt_of_continuous_rightDeriv (A 3)
      (fun s ↦ A 0 s * A 3 s)
      (hA 3 (by norm_num)) hfield3 hright3 ht

end

end DerridaRetaux.FixedArity
