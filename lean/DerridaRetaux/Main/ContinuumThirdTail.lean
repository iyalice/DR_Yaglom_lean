import DerridaRetaux.Main.ContinuumMomentBounds
import DerridaRetaux.Analysis.LatticeWeakFromLocal
import DerridaRetaux.Analysis.LimitTail

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators BoundedContinuousFunction ENNReal

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Source equation `eq:limitthirdtail` for every glued subsequential limit. -/
theorem subsequentialThirdMomentTail
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    ∃ C : ℝ, 0 < C ∧ ∀ t delta : ℝ, 0 < t → 0 < delta →
      (∫ x in Ioi delta, x ^ 3 * gluedExhaustionLimit g t x) ≤
        C * t ^ 3 / delta := by
  have hnonconstant : ¬ IsDirac data.law := by
    intro hdirac
    exact data.notBinaryFixedPoint
      (critical_isDirac_eq_binary m data.law data.arity data.critical hdirac)
  have hProduct := HumanInputs.cdhls_product_upper
    m data.law data.arity data.critical hnonconstant
  have hsharp := (cubicWeightedChain m data).2.2.2.2
  obtain ⟨K, hK, htailRaw⟩ := profileThirdTail_quadratic_of_spineTail
    m data hnonconstant hProduct hsharp
  have hmFactor : 0 < (m : ℝ) - 1 :=
    critical_tiltFactor_pos m data.law
      (le_trans (by norm_num) data.arity) data.critical
  let C : ℝ := 2 * ((m : ℝ) - 1) * K
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t delta ht hdelta
  let s : ℕ → ℕ := fun n ↦ gridIndex (phi n) t
  let L : ℕ → ℝ := fun n ↦ profileScale (s n)
  let rhoN : ℕ → Seq := fun n ↦
    positiveTiltedDensity m (orbit m data.law (s n))
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
  have hu₀nonneg : ∀ x : ℝ, 0 ≤ u₀ x := by
    intro x
    by_cases hx : x < 0
    · simp only [u₀, if_pos hx, le_refl]
    · simpa only [u₀, if_neg hx] using hunonneg x (le_of_not_gt hx)
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
    exact positiveTiltedDensity_nonneg m (orbit m data.law (s n))
      (le_trans (by norm_num) data.arity)
      (orbit_critical m data.law (le_trans (by norm_num) data.arity)
        data.critical (s n)) j
  have hzero : ∀ n : ℕ, Summable (rhoN n) := by
    intro n
    exact (positiveTiltedDensity_hasSum m (orbit m data.law (s n))
      (le_trans (by norm_num) data.arity)
      (orbit_critical m data.law (le_trans (by norm_num) data.arity)
        data.critical (s n))).summable
  have hthird : ∀ n : ℕ,
      Summable (fun j : ℕ ↦ (j : ℝ) ^ 3 * rhoN n j) := by
    intro n
    exact positiveTiltedDensity_third_summable m
      (orbit m data.law (s n)) (le_trans (by norm_num) data.arity)
      (orbit_critical m data.law (le_trans (by norm_num) data.arity)
        data.critical (s n))
      (orbit_tiltSummable_three m data.law
        (le_trans (by norm_num) data.arity) data.critical data.third (s n))
  have hint0 : IntegrableOn u (Ici (0 : ℝ)) := by
    simpa only [pow_zero, one_mul] using
      subsequentialMoment_integrable
        m data.law data.arity data.critical data.third
          data.notBinaryFixedPoint phi g hphi hlim t ht 0 (by norm_num)
  have hintU₀ : Integrable u₀ volume := by
    have hi := hint0.integrable_indicator measurableSet_Ici
    apply hi.congr
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · have hxmem : x ∈ Ici (0 : ℝ) := hx
      rw [indicator_of_mem hxmem]
      simp only [u₀, if_neg (not_lt.mpr hx)]
    · have hxneg : x < 0 := lt_of_not_ge hx
      have hxnot : x ∉ Ici (0 : ℝ) := hx
      rw [indicator_of_not_mem hxnot]
      simp only [u₀, if_pos hxneg]
  have hmomentEq0 : continuumMoment u₀ 0 = continuumMoment u 0 := by
    unfold continuumMoment
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    have hx0 : 0 ≤ x := hx
    simp only [u₀, if_neg (not_lt.mpr hx0)]
  have hmassConv : Tendsto
      (fun n ↦ scaledDiscreteMoment (rhoN n) 0 (phi n))
      atTop (nhds (continuumMoment u₀ 0)) := by
    rw [hmomentEq0]
    simpa only [rhoN, s, u] using
      subsequentialMoment_tendsto m data phi g hphi hlim t ht 0 (by norm_num)
  have hweak := scaledLatticeMeasuresAlong_tendsto_of_locallyUniform_and_mass
    rhoN phi u₀ hphi hu₀cont hu₀neg hu₀nonneg hintU₀
      hlocal₀ hrho hzero hmassConv
  have hint3 : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u x) (Ici (0 : ℝ)) :=
    subsequentialMoment_integrable
      m data.law data.arity data.critical data.third
        data.notBinaryFixedPoint phi g hphi hlim t ht 3 (by norm_num)
  have hmuTail : Integrable (cubicTailIntegrand delta)
      (finiteDensityMeasure u₀ hu₀nonneg hintU₀ : Measure ℝ) := by
    change Integrable (cubicTailIntegrand delta)
      (volume.withDensity (fun x ↦ ENNReal.ofReal (u₀ x)))
    rw [integrable_withDensity_iff_integrable_smul₀'
      hintU₀.1.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (hu₀nonneg _)]
    have hdom : Integrable (fun x : ℝ ↦ x ^ 3 * u₀ x) volume := by
      have hi : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u₀ x) (Ici 0) := by
        refine hint3.congr_fun_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
        have hx0 : 0 ≤ x := hx
        simp only [u₀, if_neg (not_lt.mpr hx0)]
      have hind := hi.integrable_indicator measurableSet_Ici
      apply hind.congr
      filter_upwards with x
      by_cases hx : 0 ≤ x
      · have hxmem : x ∈ Ici (0 : ℝ) := hx
        rw [indicator_of_mem hxmem]
      · have hxneg : x < 0 := lt_of_not_ge hx
        have hxnot : x ∉ Ici (0 : ℝ) := hx
        rw [indicator_of_not_mem hxnot]
        simp only [u₀, if_pos hxneg, mul_zero]
    apply hdom.mono'
    · simpa only [smul_eq_mul] using
        hintU₀.1.mul
          (cubicTailIntegrand_lowerSemicontinuous delta).measurable.aestronglyMeasurable
    · filter_upwards with x
      change |u₀ x * cubicTailIntegrand delta x| ≤ x ^ 3 * u₀ x
      have hprod0 := mul_nonneg (hu₀nonneg x)
        (cubicTailIntegrand_nonneg delta x)
      rw [abs_of_nonneg hprod0]
      by_cases hx : 0 ≤ x
      · rw [mul_comm]
        have htailLe : cubicTailIntegrand delta x ≤ x ^ 3 := by
          unfold cubicTailIntegrand
          by_cases hdx : delta < x
          · rw [if_pos hdx, max_eq_left hx]
          · rw [if_neg hdx]
            exact pow_nonneg hx 3
        exact mul_le_mul_of_nonneg_right htailLe (hu₀nonneg x)
      · have hxneg : x < 0 := lt_of_not_ge hx
        simp only [u₀, if_pos hxneg, zero_mul, mul_zero, le_refl]
  have hratio : Tendsto (fun n ↦ L n / (phi n : ℝ))
      atTop (nhds t) := by
    have hgrid := (gridIndex_div_tendsto t ht.le).comp hphi
    have hinv := tendsto_inverse_atTop_nhds_zero_nat.comp hphi
    have hadd := hgrid.add hinv
    convert hadd using 1 <;>
      simp [L, s, profileScale, Function.comp_def, add_div, one_div]
  have hsratio : Tendsto (fun n ↦ (s n : ℝ) / (phi n : ℝ))
      atTop (nhds t) := by
    simpa only [s] using (gridIndex_div_tendsto t ht.le).comp hphi
  have hinitial : Tendsto
      (fun n ↦ spineMarginalTail m data 0
        (delta * (phi n : ℝ) / 2)) atTop (nhds 0) :=
    (spineMarginalTail_initial_linear_tendsto_zero m data delta hdelta).comp hphi
  let E : ℕ → ℝ := fun n ↦
    ((m : ℝ) - 1) * K * (L n / (phi n : ℝ)) ^ 2 *
      (spineMarginalTail m data 0 (delta * (phi n : ℝ) / 2) +
        (s n : ℝ) / (delta * (phi n : ℝ)))
  have hlast : Tendsto (fun n ↦ (s n : ℝ) / (delta * (phi n : ℝ)))
      atTop (nhds (t / delta)) := by
    have hdiv := hsratio.div_const delta
    apply hdiv.congr'
    have hphiPos : ∀ᶠ n : ℕ in atTop, 0 < phi n := by
      have hge := hphi.eventually_ge_atTop 1
      exact hge.mono fun _ hn ↦ by omega
    filter_upwards [hphiPos] with n hn
    simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
  have hE : Tendsto E atTop
      (nhds (((m : ℝ) - 1) * K * t ^ 3 / delta)) := by
    have hsum : Tendsto
        (fun n ↦ spineMarginalTail m data 0
            (delta * (phi n : ℝ) / 2) +
          (s n : ℝ) / (delta * (phi n : ℝ)))
        atTop (nhds (0 + t / delta)) := hinitial.add hlast
    have hconst : Tendsto (fun _ : ℕ ↦ ((m : ℝ) - 1) * K) atTop
        (nhds (((m : ℝ) - 1) * K)) := tendsto_const_nhds
    have hcoeff : Tendsto
        (fun n : ℕ ↦ ((m : ℝ) - 1) * K *
          (L n / (phi n : ℝ)) ^ 2)
        atTop (nhds (((m : ℝ) - 1) * K * t ^ 2)) :=
      hconst.mul (hratio.pow 2)
    have hprod := hcoeff.mul hsum
    convert hprod using 1
    field_simp [hdelta.ne']
    ring
  have hdiscTail : ∀ᶠ n : ℕ in atTop,
      scaledDiscreteMomentTail (rhoN n) 3 (phi n) delta ≤ E n := by
    have hphiPos : ∀ᶠ n : ℕ in atTop, 1 ≤ phi n :=
      hphi.eventually_ge_atTop 1
    have hcutoff : ∀ᶠ n : ℕ in atTop,
        2 ≤ delta * (phi n : ℝ) := by
      have hgrow :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hdelta).comp hphi
      exact hgrow.eventually (eventually_ge_atTop 2)
    filter_upwards [hphiPos, hcutoff] with n hn hdn
    have hnorm := htailRaw (s n) (delta * (phi n : ℝ)) hdn
    have hnormScaled :
        normalizedTiltThirdTail m (orbit m data.law (s n))
            (delta * (phi n : ℝ)) / (phi n : ℝ) ^ 2 ≤
          (K * ((s n + 1 : ℕ) : ℝ) ^ 2 *
            (spineMarginalTail m data 0
                (delta * (phi n : ℝ) / 2) +
              (s n : ℝ) / (delta * (phi n : ℝ)))) /
            (phi n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hnorm (sq_nonneg _)
    calc
      scaledDiscreteMomentTail (rhoN n) 3 (phi n) delta ≤
          ((m : ℝ) - 1) *
            (normalizedTiltThirdTail m (orbit m data.law (s n))
              (delta * (phi n : ℝ)) / (phi n : ℝ) ^ 2) := by
        simpa only [rhoN, s] using
          scaledPositiveTiltedDensityThirdTail_le m
            (orbit m data.law (s n))
            (le_trans (by norm_num) data.arity)
            (orbit_critical m data.law
              (le_trans (by norm_num) data.arity) data.critical (s n))
            (orbit_tiltSummable_three m data.law
              (le_trans (by norm_num) data.arity)
              data.critical data.third (s n)) (phi n) delta hn
      _ ≤ ((m : ℝ) - 1) *
          ((K * ((s n + 1 : ℕ) : ℝ) ^ 2 *
            (spineMarginalTail m data 0
                (delta * (phi n : ℝ) / 2) +
              (s n : ℝ) / (delta * (phi n : ℝ)))) /
            (phi n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hnormScaled hmFactor.le
      _ = E n := by
        dsimp only [E, L, profileScale]
        have hN : (phi n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
        field_simp [hN]
        ring
  let B : ℝ := C * t ^ 3 / delta
  have hdouble : B = 2 * (((m : ℝ) - 1) * K * t ^ 3 / delta) := by
    dsimp only [B, C]
    ring
  have hbasePos : 0 < ((m : ℝ) - 1) * K * t ^ 3 / delta := by positivity
  have hEBound : ∀ᶠ n : ℕ in atTop, E n ≤ B := by
    have hlt : ((m : ℝ) - 1) * K * t ^ 3 / delta < B := by
      rw [hdouble]
      linarith
    exact ((tendsto_order.1 hE).2 B hlt).mono fun _ h ↦ h.le
  have hbound : ∀ᶠ n : ℕ in atTop,
      scaledDiscreteMomentTail (rhoN n) 3 (phi n) delta ≤ B := by
    filter_upwards [hdiscTail, hEBound] with n hdn hEn
    exact hdn.trans hEn
  have hport := limit_cubicTail_le_of_scaledLatticeMeasuresAlong_tendsto_eventually
    rhoN phi (finiteDensityMeasure u₀ hu₀nonneg hintU₀)
      hrho hzero hthird hweak delta B hmuTail hbound
  have hintegralEq :
      (∫ x, cubicTailIntegrand delta x
        ∂(finiteDensityMeasure u₀ hu₀nonneg hintU₀ : Measure ℝ)) =
      ∫ x in Ioi delta, x ^ 3 * u x := by
    change (∫ x, cubicTailIntegrand delta x
      ∂volume.withDensity (fun x ↦ ENNReal.ofReal (u₀ x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hintU₀.1.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hu₀nonneg x)]
    by_cases hx : delta < x
    · have hx0 : 0 ≤ x := hdelta.le.trans hx.le
      have hxmem : x ∈ Ioi delta := hx
      rw [indicator_of_mem hxmem]
      simp [cubicTailIntegrand, hx, max_eq_left hx0, u₀,
        not_lt.mpr hx0, mul_comm]
    · have hxnot : x ∉ Ioi delta := hx
      rw [indicator_of_not_mem hxnot]
      simp [cubicTailIntegrand, hx]
  rw [← hintegralEq]
  simpa only [B] using hport

end

end DerridaRetaux.FixedArity
