import DerridaRetaux.Analysis.ContinuumMomentIntegrability

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Local lattice convergence only probes the nonnegative half-line.  Extend
the limiting density by zero on the left before applying the whole-line
compact-test argument. -/
theorem integrableOn_pow_mul_of_locallyUniform_and_momentBound_Ici
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (r : ℕ) (hr : r ≤ 3) (C : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hrho : ∀ n j : ℕ, 0 ≤ rho n j)
    (hmoment : ∀ n : ℕ,
      Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho n j))
    (hbound : ∀ᶠ n : ℕ in atTop,
      scaledDiscreteMoment (rho n) r (scale n) ≤ C) :
    IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ)) := by
  let u₀ : ℝ → ℝ := fun x ↦ if x < 0 then 0 else u x
  have hu₀cont : ContinuousOn u₀ (Ici (0 : ℝ)) := by
    apply hucont.congr
    intro x hx
    have hx0 : 0 ≤ x := hx
    simp only [u₀, if_neg (not_lt.mpr hx0)]
  have hu₀neg : ∀ x : ℝ, x < 0 → u₀ x = 0 := by
    intro x hx
    simp only [u₀, if_pos hx]
  have hu₀nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u₀ x := by
    intro x hx
    simpa only [u₀, if_neg (not_lt.mpr hx)] using hunonneg x hx
  have hlocal₀ : LocallyUniformLatticeDensity rho scale u₀ := by
    intro R
    obtain ⟨error, herror, hlocalR⟩ := hlocal R
    refine ⟨error, herror, ?_⟩
    intro n hn j hj
    have hx : 0 ≤ (j : ℝ) / (scale n : ℝ) :=
      div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg (scale n))
    simpa only [u₀, if_neg (not_lt.mpr hx)] using hlocalR n hn j hj
  have hint := integrableOn_pow_mul_of_locallyUniform_and_momentBound
    rho scale u₀ r hr C hscale hu₀cont hu₀neg hu₀nonneg
      hlocal₀ hrho hmoment hbound
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  have hx0 : 0 ≤ x := hx
  simp only [u₀, if_neg (not_lt.mpr hx0)]

end

end DerridaRetaux
