import DerridaRetaux.Analysis.MomentConvergenceFromLocal

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace DerridaRetaux

noncomputable section

/-- Local lattice convergence and uniform moment tails identify the full
continuum moment.  Smooth compact cutoffs avoid any discontinuous-test gap. -/
theorem scaledDiscreteMoment_tendsto_of_locallyUniform_and_uniformTails
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (r : ℕ)
    (hscale : Tendsto scale atTop atTop)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (huneg : ∀ x : ℝ, x < 0 → u x = 0)
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hrho : ∀ n j : ℕ, 0 ≤ rho n j)
    (hmoment : ∀ n : ℕ,
      Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho n j))
    (hint : IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ)))
    (htail : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ A : ℝ in atTop, ∀ᶠ n : ℕ in atTop,
        scaledDiscreteMomentTail (rho n) r (scale n) A ≤ epsilon) :
    Tendsto
      (fun n : ℕ ↦ scaledDiscreteMoment (rho n) r (scale n))
      atTop (nhds (continuumMoment u r)) := by
  have hcut := integral_positiveMomentCutoff_tendsto_continuumMoment
    u r hucont hunonneg hint
  have hsoft : ∀ R : ℕ, Tendsto
      (fun n : ℕ ↦ softScaledDiscreteMoment (rho n) r (scale n) R)
      atTop
      (nhds (∫ x in Ici (0 : ℝ),
        u x * positiveMomentCutoff r R x)) := by
    intro R
    have hcompact := compact_lattice_sums_tendsto_of_locallyUniform
      rho scale u hscale hucont huneg hlocal
        (positiveMomentCutoffBCF r R)
        (positiveMomentCutoff_hasCompactSupport r R)
    have hintegral :
        (∫ x, u x * positiveMomentCutoff r R x) =
          ∫ x in Ici (0 : ℝ), u x * positiveMomentCutoff r R x := by
      rw [← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 ≤ x
      · have hxmem : x ∈ Ici (0 : ℝ) := hx
        rw [indicator_of_mem hxmem]
      · have hxneg : x < 0 := lt_of_not_ge hx
        have hxnot : x ∉ Ici (0 : ℝ) := hx
        rw [indicator_of_not_mem hxnot, huneg x hxneg, zero_mul]
    rw [← hintegral]
    simpa only [softScaledDiscreteMoment,
      positiveMomentCutoffBCF_apply] using hcompact
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  let delta : ℝ := epsilon / 3
  have hdelta : 0 < delta := div_pos hepsilon (by norm_num)
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.mp hcut delta hdelta
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1 (htail delta hdelta)
  obtain ⟨R₁, hR₁⟩ := exists_nat_ge (max A₀ (R₀ : ℝ))
  have hR₀le : R₀ ≤ R₁ := by
    exact_mod_cast (le_trans (le_max_right A₀ (R₀ : ℝ)) hR₁)
  have hA₀le : A₀ ≤ (R₁ : ℝ) :=
    (le_max_left A₀ (R₀ : ℝ)).trans hR₁
  have hcutNear := hR₀ R₁ hR₀le
  have htailR := hA₀ (R₁ : ℝ) hA₀le
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (hsoft R₁) delta hdelta
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge := hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  rw [eventually_atTop] at htailR hscalePos
  obtain ⟨N₁, hN₁⟩ := htailR
  obtain ⟨N₂, hN₂⟩ := hscalePos
  refine ⟨max N₀ (max N₁ N₂), ?_⟩
  intro n hnAll
  have hn : N₀ ≤ n := (le_max_left N₀ (max N₁ N₂)).trans hnAll
  have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans
    ((le_max_right N₀ (max N₁ N₂)).trans hnAll)
  have hn₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans
    ((le_max_right N₀ (max N₁ N₂)).trans hnAll)
  have htailn := hN₁ n hn₁
  have hnpos := hN₂ n hn₂
  have hsoftNear := hN₀ n hn
  have hsandwich := softScaledDiscreteMoment_sandwich
    (rho n) r (scale n) R₁ hnpos (hrho n) (hmoment n)
  have htailNonneg := scaledDiscreteMomentTail_nonneg
    (rho n) r (scale n) (R₁ : ℝ) (hrho n)
  rw [Real.dist_eq] at hcutNear hsoftNear ⊢
  have hdiffNonneg : 0 ≤
      scaledDiscreteMoment (rho n) r (scale n) -
        softScaledDiscreteMoment (rho n) r (scale n) R₁ :=
    sub_nonneg.mpr hsandwich.1
  have hdiffLe :
      scaledDiscreteMoment (rho n) r (scale n) -
          softScaledDiscreteMoment (rho n) r (scale n) R₁ ≤
        scaledDiscreteMomentTail (rho n) r (scale n) (R₁ : ℝ) := by
    linarith [hsandwich.2]
  calc
    |scaledDiscreteMoment (rho n) r (scale n) - continuumMoment u r| ≤
        |scaledDiscreteMoment (rho n) r (scale n) -
            softScaledDiscreteMoment (rho n) r (scale n) R₁| +
          |softScaledDiscreteMoment (rho n) r (scale n) R₁ -
            (∫ x in Ici (0 : ℝ),
              u x * positiveMomentCutoff r R₁ x)| +
          |(∫ x in Ici (0 : ℝ),
              u x * positiveMomentCutoff r R₁ x) - continuumMoment u r| := by
        calc
          _ ≤ |scaledDiscreteMoment (rho n) r (scale n) -
                  softScaledDiscreteMoment (rho n) r (scale n) R₁| +
              |softScaledDiscreteMoment (rho n) r (scale n) R₁ -
                continuumMoment u r| := abs_sub_le _ _ _
          _ ≤ _ := by
            simpa only [add_assoc] using add_le_add_left
              (abs_sub_le
                (softScaledDiscreteMoment (rho n) r (scale n) R₁)
                (∫ x in Ici (0 : ℝ), u x * positiveMomentCutoff r R₁ x)
                (continuumMoment u r))
              |scaledDiscreteMoment (rho n) r (scale n) -
                softScaledDiscreteMoment (rho n) r (scale n) R₁|
    _ < epsilon := by
      rw [abs_of_nonneg hdiffNonneg]
      have hdiffBound := hdiffLe.trans htailn
      dsimp only [delta] at hdiffBound hsoftNear hcutNear
      linarith

end

end DerridaRetaux
