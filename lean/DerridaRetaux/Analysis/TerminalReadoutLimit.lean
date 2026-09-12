import DerridaRetaux.Analysis.TimeRiemannLimit
import DerridaRetaux.Analysis.SpacetimeMovingReadout
import DerridaRetaux.Analysis.GluedCompactBox

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The rescaled density at the terminal floor-grid node converges to the
glued spacetime limit at the corresponding continuum point. -/
theorem scaled_terminalDensity_tendsto
    (m : ℕ) (p₀ : ProbabilityMass)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t x : ℝ) (R : ℕ)
    (ht : 0 < t) (hx : 0 ≤ x) (hR : x + 1 ≤ (R : ℝ))
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    Tendsto
      (fun n ↦ (phi n : ℝ) ^ 2 *
        positiveTiltedDensity m
          (orbit m p₀ (gridIndex (phi n) t))
          (gridIndex (phi n) x))
      atTop (nhds (gluedExhaustionLimit g t x)) := by
  let b : ℕ → ℕ := fun n ↦ gridIndex (phi n) t
  let j : ℕ → ℕ := fun n ↦ gridIndex (phi n) x
  let u : ℝ → ℝ → ℝ := gluedExhaustionLimit g
  have htime : Tendsto (fun n ↦ (b n : ℝ) / (phi n : ℝ))
      atTop (nhds t) := by
    simpa only [b] using (gridIndex_div_tendsto t ht.le).comp hphi
  have hspace : Tendsto (fun n ↦ (j n : ℝ) / (phi n : ℝ))
      atTop (nhds x) := by
    simpa only [j] using (gridIndex_div_tendsto x hx).comp hphi
  have heta : 0 < t / 2 := half_pos ht
  have hetaT : t / 2 ≤ t + 1 := by linarith
  have hu : ContinuousOn (Function.uncurry u)
      (Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ)) := by
    exact continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m p₀) phi g hlim (t / 2) (t + 1) (R : ℝ)
        heta hetaT (Nat.cast_nonneg R)
  have hlocal : LocallyUniformSpacetimeLatticeDensity
      (fun _n s ↦ positiveTiltedDensity m (orbit m p₀ s)) phi u :=
    locallyUniformSpacetimeLatticeDensity_orbit_of_gluedExhaustion
      m p₀ phi g hlim
  have htarget : (t, x) ∈
      Icc (t / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ) := by
    exact ⟨⟨by linarith, by linarith⟩, hx, by linarith [hR]⟩
  have hindices : ∀ᶠ n : ℕ in atTop,
      t / 2 * (phi n : ℝ) ≤ (b n : ℝ) ∧
      (b n : ℝ) ≤ (t + 1) * (phi n : ℝ) ∧
      j n ≤ R * phi n := by
    have hphiPos : ∀ᶠ n : ℕ in atTop, 0 < phi n := by
      have hge := hphi.eventually_ge_atTop 1
      exact hge.mono fun _ hn ↦ by omega
    have htimeLow : ∀ᶠ n : ℕ in atTop,
        t / 2 ≤ (b n : ℝ) / (phi n : ℝ) :=
      htime (Ici_mem_nhds (by linarith))
    have htimeHigh : ∀ᶠ n : ℕ in atTop,
        (b n : ℝ) / (phi n : ℝ) ≤ t + 1 :=
      htime (Iic_mem_nhds (by linarith))
    have hspaceHigh : ∀ᶠ n : ℕ in atTop,
        (j n : ℝ) / (phi n : ℝ) < (R : ℝ) :=
      hspace (Iio_mem_nhds (by linarith [hR]))
    filter_upwards [hphiPos, htimeLow, htimeHigh, hspaceHigh] with
      n hn htl hth hjh
    have hNreal : (0 : ℝ) < (phi n : ℝ) := by exact_mod_cast hn
    refine ⟨(le_div_iff₀ hNreal).mp htl,
      (div_le_iff₀ hNreal).mp hth, ?_⟩
    have : (j n : ℝ) < ((R * phi n : ℕ) : ℝ) := by
      push_cast
      exact (div_lt_iff₀ hNreal).mp hjh
    exact_mod_cast this.le
  simpa only [b, j, u] using
    spacetimeLatticeDensity_tendsto_moving
      (fun _n s ↦ positiveTiltedDensity m (orbit m p₀ s))
      phi b j u (t / 2) (t + 1) R t x hphi heta hetaT
      hlocal hu htarget htime hspace hindices

end

end DerridaRetaux
