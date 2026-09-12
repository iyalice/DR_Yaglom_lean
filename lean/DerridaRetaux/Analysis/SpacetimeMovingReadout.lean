import DerridaRetaux.Analysis.SpacetimeLatticeDensity

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- A moving lattice node in a compact spacetime box converges to the value of
the continuous spacetime density at the limiting point. -/
theorem spacetimeLatticeDensity_tendsto_moving
    (rho : ℕ → ℕ → Seq) (scale timeIndex spaceIndex : ℕ → ℕ)
    (u : ℝ → ℝ → ℝ) (eta T : ℝ) (R : ℕ) (t x : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (heta : 0 < eta) (hetaT : eta ≤ T)
    (hlocal : LocallyUniformSpacetimeLatticeDensity rho scale u)
    (hu : ContinuousOn (Function.uncurry u)
      (Icc eta T ×ˢ Icc (0 : ℝ) (R : ℝ)))
    (htarget : (t, x) ∈ Icc eta T ×ˢ Icc (0 : ℝ) (R : ℝ))
    (htime : Tendsto
      (fun n ↦ (timeIndex n : ℝ) / (scale n : ℝ)) atTop (nhds t))
    (hspace : Tendsto
      (fun n ↦ (spaceIndex n : ℝ) / (scale n : ℝ)) atTop (nhds x))
    (hindices : ∀ᶠ n : ℕ in atTop,
      eta * (scale n : ℝ) ≤ (timeIndex n : ℝ) ∧
      (timeIndex n : ℝ) ≤ T * (scale n : ℝ) ∧
      spaceIndex n ≤ R * scale n) :
    Tendsto
      (fun n ↦ (scale n : ℝ) ^ 2 * rho n (timeIndex n) (spaceIndex n))
      atTop (nhds (u t x)) := by
  obtain ⟨error, herror, hlocalBox⟩ := hlocal eta T R heta hetaT
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge := hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  have hp : Tendsto
      (fun n ↦ ((timeIndex n : ℝ) / (scale n : ℝ),
        (spaceIndex n : ℝ) / (scale n : ℝ)))
      atTop (nhds (t, x)) := htime.prodMk_nhds hspace
  have hpMem : ∀ᶠ n : ℕ in atTop,
      ((timeIndex n : ℝ) / (scale n : ℝ),
        (spaceIndex n : ℝ) / (scale n : ℝ)) ∈
      Icc eta T ×ˢ Icc (0 : ℝ) (R : ℝ) := by
    filter_upwards [hindices, hscalePos] with n hn hnpos
    have hNreal : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hnpos
    exact ⟨⟨(le_div_iff₀ hNreal).2 (by simpa only [mul_comm] using hn.1),
      (div_le_iff₀ hNreal).2 (by simpa only [mul_comm] using hn.2.1)⟩,
      div_nonneg (Nat.cast_nonneg _) hNreal.le,
      (div_le_iff₀ hNreal).2 (by exact_mod_cast hn.2.2)⟩
  have hpWithin : Tendsto
      (fun n ↦ ((timeIndex n : ℝ) / (scale n : ℝ),
        (spaceIndex n : ℝ) / (scale n : ℝ)))
      atTop (nhdsWithin (t, x)
        (Icc eta T ×ˢ Icc (0 : ℝ) (R : ℝ))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp, hpMem⟩
  have huTend : Tendsto
      (fun n ↦ u ((timeIndex n : ℝ) / (scale n : ℝ))
        ((spaceIndex n : ℝ) / (scale n : ℝ)))
      atTop (nhds (u t x)) := by
    simpa only [Function.uncurry_apply_pair] using
      (hu (t, x) htarget).tendsto.comp hpWithin
  have hdist : Tendsto
      (fun n ↦ dist
        ((scale n : ℝ) ^ 2 * rho n (timeIndex n) (spaceIndex n))
        (u ((timeIndex n : ℝ) / (scale n : ℝ))
          ((spaceIndex n : ℝ) / (scale n : ℝ))))
      atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ herror
    filter_upwards [hindices, hscalePos] with n hn hnpos
    rw [Real.dist_eq]
    exact hlocalBox n hnpos (timeIndex n) hn.1 hn.2.1
      (spaceIndex n) hn.2.2
  apply huTend.congr_dist
  simpa only [dist_comm] using hdist

end

end DerridaRetaux
