import DerridaRetaux.Main.ContinuumMoments
import DerridaRetaux.Main.SpineCore
import DerridaRetaux.Analysis.MomentConvergence

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Source equation `eq:momentpass` for an arbitrary positive-time slice of
an arbitrary glued subsequential limit. -/
theorem subsequentialMoment_tendsto
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) (r : ℕ) (hr : r ≤ 3) :
    Tendsto
      (fun n : ℕ ↦ scaledDiscreteMoment
        (positiveTiltedDensity m
          (orbit m data.law (gridIndex (phi n) t))) r (phi n))
      atTop
      (nhds (continuumMoment
        (fun x ↦ gluedExhaustionLimit g t x) r)) := by
  have hnonconstant : ¬ IsDirac data.law := by
    intro hdirac
    exact data.notBinaryFixedPoint
      (critical_isDirac_eq_binary m data.law data.arity data.critical hdirac)
  have hProduct := HumanInputs.cdhls_product_upper
    m data.law data.arity data.critical hnonconstant
  have hsharp := (cubicWeightedChain m data).2.2.2.2
  let rhoN : ℕ → Seq := fun n ↦ positiveTiltedDensity m
    (orbit m data.law (gridIndex (phi n) t))
  let u : ℝ → ℝ := fun x ↦ gluedExhaustionLimit g t x
  let u₀ : ℝ → ℝ := fun x ↦ if x < 0 then 0 else u x
  let F : ℕ → (ℝ × ℝ) → ℝ := fun N p ↦
    gridBilinearInterp N (orbitScaledGrid m data.law N) p.1 p.2
  have hcompat : ∀ {k l : ℕ}, ∀ hkl : k ≤ l,
      ∀ p : gridExhaustionRectangle k,
        g k p = g l ⟨(p : ℝ × ℝ),
          gridExhaustionRectangle_mono hkl p.property⟩ := by
    intro k l hkl p
    exact exhaustionLimits_compatible F phi g hlim hkl p
  have hucont : ContinuousOn u (Ici (0 : ℝ)) :=
    continuousOn_gluedExhaustionLimit_timeSlice_Ici g hcompat t ht
  have hu₀cont : ContinuousOn u₀ (Ici (0 : ℝ)) := by
    apply hucont.congr
    intro x hx
    have hx0 : 0 ≤ x := hx
    simp only [u₀, if_neg (not_lt.mpr hx0)]
  have hu₀neg : ∀ x : ℝ, x < 0 → u₀ x = 0 := by
    intro x hx
    simp only [u₀, if_pos hx]
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hu₀nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u₀ x := by
    intro x hx
    simpa only [u₀, if_neg (not_lt.mpr hx)] using hunonneg x hx
  have hlocal : LocallyUniformLatticeDensity rhoN phi u := by
    exact locallyUniformLatticeDensity_orbit_of_gluedExhaustion_at_time
      m data.law phi g t ht hphi hlim
  have hlocal₀ : LocallyUniformLatticeDensity rhoN phi u₀ := by
    intro R
    obtain ⟨error, herror, hlocalR⟩ := hlocal R
    refine ⟨error, herror, ?_⟩
    intro n hn j hj
    have hx : 0 ≤ (j : ℝ) / (phi n : ℝ) :=
      div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg (phi n))
    simpa only [u₀, if_neg (not_lt.mpr hx)] using hlocalR n hn j hj
  have hrho : ∀ n j : ℕ, 0 ≤ rhoN n j := by
    intro n j
    exact positiveTiltedDensity_nonneg m
      (orbit m data.law (gridIndex (phi n) t)) (le_trans (by norm_num) data.arity)
      (orbit_critical m data.law (le_trans (by norm_num) data.arity) data.critical _) j
  have hmoment : ∀ n : ℕ,
      Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rhoN n j) := by
    intro n
    let s := gridIndex (phi n) t
    have hscrit := orbit_critical m data.law (le_trans (by norm_num) data.arity) data.critical s
    have hsthird := orbit_tiltSummable_three
      m data.law (le_trans (by norm_num) data.arity) data.critical data.third s
    have hzero := (positiveTiltedDensity_hasSum
      m (orbit m data.law s) (le_trans (by norm_num) data.arity) hscrit).summable
    have hthree := positiveTiltedDensity_third_summable
      m (orbit m data.law s) (le_trans (by norm_num) data.arity) hscrit hsthird
    simpa only [rhoN, s] using
      moment_summable_of_zero_and_third
        (positiveTiltedDensity m (orbit m data.law s)) r hr
          (positiveTiltedDensity_nonneg m (orbit m data.law s)
            (le_trans (by norm_num) data.arity) hscrit) hzero hthree
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ)) :=
    subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht r hr
  have hint₀ : IntegrableOn (fun x : ℝ ↦ x ^ r * u₀ x) (Ici (0 : ℝ)) := by
    refine hint.congr_fun_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    have hx0 : 0 ≤ x := hx
    simp only [u₀, if_neg (not_lt.mpr hx0)]
  have htail : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ n : ℕ in atTop,
        scaledDiscreteMomentTail (rhoN n) r (phi n) A ≤ epsilon := by
    intro epsilon hepsilon
    have hUI := profileDensityMomentTail_uniform_integrability_of_spineTail
      m data hnonconstant hProduct hsharp r hr (t + 1) (by linarith)
        epsilon hepsilon
    filter_upwards [hUI] with A hUIA
    have hUIAlong := hphi hUIA
    filter_upwards [hUIAlong] with n hn
    apply hn (gridIndex (phi n) t)
    calc
      (gridIndex (phi n) t : ℝ) ≤ (phi n : ℝ) * t :=
        gridIndex_cast_le (phi n) t ht.le
      _ ≤ (phi n : ℝ) * t + (phi n : ℝ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg (phi n))
      _ = (t + 1) * (phi n : ℝ) := by ring
  have hconv := scaledDiscreteMoment_tendsto_of_locallyUniform_and_uniformTails
    rhoN phi u₀ r hphi hu₀cont hu₀neg hu₀nonneg hlocal₀
      hrho hmoment hint₀ htail
  have hmomentEq : continuumMoment u₀ r = continuumMoment u r := by
    unfold continuumMoment
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    have hx0 : 0 ≤ x := hx
    simp only [u₀, if_neg (not_lt.mpr hx0)]
  simpa only [rhoN, u, hmomentEq] using hconv

end

end DerridaRetaux.FixedArity
