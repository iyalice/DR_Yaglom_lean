import DerridaRetaux.Analysis.QuadraticDuhamelIntegrand
import DerridaRetaux.Analysis.UniformWindowError
import DerridaRetaux.Analysis.LocalizedTimeRiemann
import DerridaRetaux.Analysis.GluedCompactBox

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The full quadratic Duhamel time sum converges to the continuum convolution
integral at every strictly positive spatial point. -/
theorem quadraticDuhamelGridSum_tendsto_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t₀ t x : ℝ) (R : ℕ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 < x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    let u := gluedExhaustionLimit g
    let F : ℕ → ℕ → ℝ := fun n s ↦
      densityQuadraticWeight m p₀ s (gridIndex (phi n) t) *
        ((phi n : ℝ) ^ 3 *
          conv (positiveTiltedDensity m (orbit m p₀ s))
            (positiveTiltedDensity m (orbit m p₀ s))
            (gridIndex (phi n) x + (gridIndex (phi n) t - 1 - s)))
    Tendsto (fun n ↦ gridTimeArraySum F phi n t₀ t) atTop
      (nhds (∫ s in t₀..t,
        (1 / 2 : ℝ) * positiveSelfConvolution (u s) (x + t - s))) := by
  dsimp only
  let u : ℝ → ℝ → ℝ := gluedExhaustionLimit g
  let F : ℕ → ℕ → ℝ := fun n s ↦
    densityQuadraticWeight m p₀ s (gridIndex (phi n) t) *
      ((phi n : ℝ) ^ 3 *
        conv (positiveTiltedDensity m (orbit m p₀ s))
          (positiveTiltedDensity m (orbit m p₀ s))
          (gridIndex (phi n) x + (gridIndex (phi n) t - 1 - s)))
  let f : ℝ → ℝ := fun s ↦
    (1 / 2 : ℝ) * positiveSelfConvolution (u s) (x + t - s)
  have heta : 0 < t₀ / 2 := half_pos ht₀
  have hetaT : t₀ / 2 ≤ t + 1 := by linarith
  have huBox : ContinuousOn (Function.uncurry u)
      (Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ)) := by
    exact continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m p₀) phi g hlim (t₀ / 2) (t + 1) (R : ℝ)
        heta hetaT (Nat.cast_nonneg R)
  have hlocal : LocallyUniformSpacetimeLatticeDensity
      (fun _n s ↦ positiveTiltedDensity m (orbit m p₀ s)) phi u := by
    exact locallyUniformSpacetimeLatticeDensity_orbit_of_gluedExhaustion
      m p₀ phi g hlim
  have huniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Finset.Ico (gridIndex (phi n) t₀) (gridIndex (phi n) t),
        |F n s - f ((s : ℝ) / (phi n : ℝ))| < ε := by
    intro ε hε
    simpa only [F, f, u] using
      quadraticDuhamelIntegrand_floor_window_uniform_of_H1a
        m p₀ hm hcrit hthird hnonconstant hExcess phi u
        t₀ t x R ht₀ ht hx hR hphi hlocal huBox ε hε
  obtain ⟨error, herror, herrorBound⟩ :=
    exists_tendsto_zero_error_of_eventuallyUniform_window
      (fun n ↦ gridIndex (phi n) t₀) (fun n ↦ gridIndex (phi n) t)
      (fun n s ↦ F n s - f ((s : ℝ) / (phi n : ℝ))) huniform
  have hf : ContinuousOn f (Icc (t₀ / 2) t) := by
    have huSmall : ContinuousOn (Function.uncurry u)
        (Icc (t₀ / 2) t ×ˢ Icc (0 : ℝ) (R : ℝ)) :=
      huBox.mono fun p hp ↦
        ⟨⟨hp.1.1, hp.1.2.trans (by linarith)⟩, hp.2⟩
    have hconv := continuousOn_positiveSelfConvolution_uncurry
      u (t₀ / 2) t (R : ℝ) (by linarith) (Nat.cast_nonneg R) huSmall
    apply continuousOn_const.mul
    apply hconv.comp
      (continuous_id.prodMk
        (continuous_const.add continuous_const |>.sub continuous_id)).continuousOn
    intro s hs
    refine ⟨hs, ?_⟩
    constructor
    · change 0 ≤ x + t - s
      linarith [hx, hs.2]
    · have hxtR : x + t ≤ (R : ℝ) := by linarith [hR]
      change x + t - s ≤ (R : ℝ)
      linarith [hs.1]
  have hbase :=
    gridTimeLeftRiemannSum_along_scale_tendsto_of_continuousOn_neighborhood
      f phi t₀ t ht₀ ht hphi hf
  apply gridTimeArraySum_tendsto_of_uniform_approximation_of_base
    F f phi hphi t₀ t (ht₀.le.trans ht) hbase error herror
  intro n _hn s hs
  exact herrorBound n s hs

end

end DerridaRetaux
