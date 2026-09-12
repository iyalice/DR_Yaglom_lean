import DerridaRetaux.Analysis.GluedTimeSlice
import DerridaRetaux.Analysis.GridReadout
import DerridaRetaux.Analysis.QuadraticConvolutionLimit

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Every positive-time slice of the glued limit is continuous on the whole
nonnegative spatial half-line. -/
theorem continuousOn_gluedExhaustionLimit_timeSlice_Ici
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩)
    (t : ℝ) (ht : 0 < t) :
    ContinuousOn (fun x ↦ gluedExhaustionLimit g t x) (Ici (0 : ℝ)) := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_mem_gridExhaustionRectangle ht hx
  let K : ℕ := k + 1
  have htk : (t, x) ∈ gridExhaustionRectangle K :=
    gridExhaustionRectangle_mono (Nat.le_succ k) hk
  have hxUpper : x < ((K + 1 : ℕ) : ℝ) := by
    exact hk.2.2.trans_lt (by dsimp only [K]; norm_num)
  have hlocal := continuousOn_gluedExhaustionLimit_rectangle g hcompat K
    (t, x) htk
  have hslice : ContinuousWithinAt
      (fun y : ℝ ↦ gluedExhaustionLimit g t y)
      (Icc (0 : ℝ) ((K + 1 : ℕ) : ℝ)) x := by
    simpa only [Function.comp_apply] using hlocal.comp
      (continuousAt_const.prodMk continuousAt_id).continuousWithinAt
      (fun y hy ↦ ⟨htk.1, hy⟩)
  apply hslice.mono_of_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
  refine ⟨Iio (((K + 1 : ℕ) : ℝ)), Iio_mem_nhds hxUpper, ?_⟩
  rintro y ⟨hyUpper, hyZero⟩
  exact ⟨hyZero, hyUpper.le⟩

/-- The fixed-time lattice-density bridge specialized to the literal DR orbit
array. -/
theorem locallyUniformLatticeDensity_orbit_of_gluedExhaustion_at_time
    (m : ℕ) (p₀ : ProbabilityMass) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t : ℝ) (ht : 0 < t)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    LocallyUniformLatticeDensity
      (fun n ↦ positiveTiltedDensity m
        (orbit m p₀ (gridIndex (phi n) t)))
      phi (fun x ↦ gluedExhaustionLimit g t x) := by
  apply locallyUniformLatticeDensity_of_gluedExhaustion_at_time
    (rho := fun n ↦ positiveTiltedDensity m
      (orbit m p₀ (gridIndex (phi n) t)))
    (a := orbitScaledGrid m p₀) (phi := phi) (g := g) (t := t) ht hphi
  · intro n j
    rfl
  · exact hlim

/-- Consequently the rescaled quadratic orbit convolution converges at every
fixed positive time and nonnegative spatial point. -/
theorem orbit_rho_scaled_conv_tendsto_of_gluedExhaustion_at_time
    (m : ℕ) (p₀ : ProbabilityMass) (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t x : ℝ) (ht : 0 < t) (hx : 0 ≤ x)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    Tendsto
      (fun n : ℕ ↦ (phi n : ℝ) ^ 3 *
        conv (rho m (orbit m p₀ (gridIndex (phi n) t)))
          (rho m (orbit m p₀ (gridIndex (phi n) t)))
          (gridIndex (phi n) x))
      atTop
      (nhds (positiveSelfConvolution
        (fun y ↦ gluedExhaustionLimit g t y) x)) := by
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (orbitScaledGrid m p₀ N) p.1 p.2
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible F phi g hlim hkl p
  exact orbit_rho_scaled_conv_gridIndex_tendsto m p₀
    (fun n ↦ gridIndex (phi n) t) phi
    (fun y ↦ gluedExhaustionLimit g t y) x hphi
    (continuousOn_gluedExhaustionLimit_timeSlice_Ici g hcompat t ht)
    (locallyUniformLatticeDensity_orbit_of_gluedExhaustion_at_time
      m p₀ phi g t ht hphi hlim) hx

end

end DerridaRetaux
