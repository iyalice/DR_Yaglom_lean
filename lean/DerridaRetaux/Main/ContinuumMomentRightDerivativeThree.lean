import DerridaRetaux.Main.ContinuumMomentRightDerivatives

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Right derivative form of the third-moment equation before simplifying
the convolution moment. -/
theorem subsequentialMoment_three_hasDerivWithinAt_increment
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
        (fun x ↦ gluedExhaustionLimit g (t + h) x) 3)
      (-3 * continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 +
        (1 / 2 : ℝ) * continuumMoment
          (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g t x)) 3)
      (Ici 0) 0 := by
  let u : ℝ → ℝ → ℝ := fun s x ↦ gluedExhaustionLimit g s x
  have hmild : ∀ h : ℝ, 0 ≤ h →
      continuumMoment (u (t + h)) 3 = shiftedHalfLineMoment (u t) 3 h +
        ∫ s in t..t + h, (1 / 2 : ℝ) * shiftedHalfLineMoment
          (positiveSelfConvolution (u s)) 3 (t + h - s) := by
    intro h hh
    simpa only [u] using subsequentialMomentMildIdentity
      m data phi g hphi hlim t h ht hh 3 (by norm_num)
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
  have hi : ∀ k : ℕ, k ≤ 3 →
      IntegrableOn (fun x : ℝ ↦ x ^ k * u t x) (Ici 0) := by
    intro k hk
    simpa only [u] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht k hk
  have htransport := hasDerivWithinAt_shiftedHalfLineMoment_three
    (u t) hucont (by simpa using hi 0 (by norm_num))
      (by simpa using hi 1 (by norm_num))
      (hi 2 (by norm_num)) (hi 3 (by norm_num))
  have hshift := subsequentialShiftedConvolution_three_continuousWithinAt
    m data phi g hphi hlim t ht
  have hG : ContinuousWithinAt
      (fun z : ℝ × ℝ ↦ (1 / 2 : ℝ) * shiftedHalfLineMoment
        (positiveSelfConvolution (u z.2)) 3 (t + z.1 - z.2))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ t ≤ z.2 ∧ z.2 ≤ t + z.1} (0, t) :=
    continuousWithinAt_const.mul hshift
  have hInt : ∀ h : ℝ, 0 ≤ h → IntervalIntegrable
      (fun s ↦ (1 / 2 : ℝ) * shiftedHalfLineMoment
        (positiveSelfConvolution (u s)) 3 (t + h - s)) volume t (t + h) := by
    intro h hh
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : t ≤ t + h)]
    simpa only [u] using subsequentialShiftedConvolutionMoment_integrableOn_time
      m data phi g hphi hlim t h ht hh 3 (by norm_num)
  simpa only [u] using hasDerivWithinAt_moment_of_mildIdentity
    u 3 t (-3 * continuumMoment (u t) 2) hmild htransport hG hInt

end

end DerridaRetaux.FixedArity
