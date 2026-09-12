import DerridaRetaux.Main.ContinuumMomentPassage
import DerridaRetaux.Analysis.MildCoefficientLimits
import DerridaRetaux.Analysis.OrbitMomentEnvelope
import DerridaRetaux.Prelim.AtomTail

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The four bounds and normalization in source equation `eq:Amoment`, for
every positive-time slice of an arbitrary glued subsequential limit. -/
theorem subsequentialMoment_bounds
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 ≤ C / t ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 1 = 1 ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 ≤ C * t ∧
      continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 ≤ C * t ^ 2 := by
  have hnonconstant : ¬ IsDirac data.law := by
    intro hdirac
    exact data.notBinaryFixedPoint
      (critical_isDirac_eq_binary m data.law data.arity data.critical hdirac)
  let hExcess := HumanInputs.cdhls_excess_upper
    m data.law data.arity data.critical data.third hnonconstant
  let hProduct := HumanInputs.cdhls_product_upper
    m data.law data.arity data.critical hnonconstant
  obtain ⟨A, hA, hL1, hfirstShifted⟩ :=
    positiveTiltedDensity_weightedMass_orbit
      m data.law data.arity data.critical data.third hnonconstant
        hExcess hProduct
  refine ⟨A, hA, ?_⟩
  intro t ht
  let s : ℕ → ℕ := fun n ↦ gridIndex (phi n) t
  let L : ℕ → ℝ := fun n ↦ profileScale (s n)
  let rhoN : ℕ → Seq := fun n ↦
    positiveTiltedDensity m (orbit m data.law (s n))
  let moment : ℕ → ℝ := fun r ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) r
  have hratio : Tendsto (fun n ↦ L n / (phi n : ℝ))
      atTop (nhds t) := by
    have hgrid := (gridIndex_div_tendsto t ht.le).comp hphi
    have hinv := tendsto_inverse_atTop_nhds_zero_nat.comp hphi
    have hadd := hgrid.add hinv
    convert hadd using 1 <;>
      simp [L, s, profileScale, Function.comp_def, add_div, one_div]
  have hphiPos : ∀ᶠ n : ℕ in atTop, 0 < phi n := by
    have hge := hphi.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  have hupper : ∀ r : ℕ, r ≤ 3 → ∀ᶠ n : ℕ in atTop,
      scaledDiscreteMoment (rhoN n) r (phi n) ≤
        ((phi n : ℝ) / (phi n : ℝ) ^ r) *
          (L n ^ r * (A / L n)) := by
    intro r hr
    filter_upwards [hphiPos] with n hn
    exact orbit_scaledDiscreteMoment_le_envelope
      m data.law data.arity data.critical data.third A hL1
        (phi n) (s n) r hn hr
  have hconv : ∀ r : ℕ, r ≤ 3 →
      Tendsto (fun n ↦ scaledDiscreteMoment (rhoN n) r (phi n))
        atTop (nhds (moment r)) := by
    intro r hr
    simpa only [rhoN, s, moment] using
      subsequentialMoment_tendsto m data phi g hphi hlim t ht r hr
  have henv0 : Tendsto
      (fun n ↦ ((phi n : ℝ) / (phi n : ℝ) ^ 0) *
        (L n ^ 0 * (A / L n)))
      atTop (nhds (A / t)) := by
    have hinv := hratio.inv₀ ht.ne'
    have hmul : Tendsto
        (fun n : ℕ ↦ A * (L n / (phi n : ℝ))⁻¹)
        atTop (nhds (A * t⁻¹)) := tendsto_const_nhds.mul hinv
    have hmul' : Tendsto
        (fun n : ℕ ↦ A * (L n / (phi n : ℝ))⁻¹)
        atTop (nhds (A / t)) := by
      simpa only [div_eq_mul_inv] using hmul
    apply hmul'.congr'
    filter_upwards [hphiPos] with n hn
    have hN : (phi n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hLn : L n ≠ 0 := by
      dsimp only [L, s, profileScale]
      positivity
    simp only [pow_zero, div_one, one_mul]
    field_simp [hN, hLn]
    ring
  have henv2 : Tendsto
      (fun n ↦ ((phi n : ℝ) / (phi n : ℝ) ^ 2) *
        (L n ^ 2 * (A / L n)))
      atTop (nhds (A * t)) := by
    have hmul : Tendsto (fun n : ℕ ↦ A * (L n / (phi n : ℝ)))
        atTop (nhds (A * t)) := tendsto_const_nhds.mul hratio
    apply hmul.congr'
    filter_upwards [hphiPos] with n hn
    have hN : (phi n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hLn : L n ≠ 0 := by
      dsimp only [L, s, profileScale]
      positivity
    field_simp [hN, hLn]
    ring
  have henv3 : Tendsto
      (fun n ↦ ((phi n : ℝ) / (phi n : ℝ) ^ 3) *
        (L n ^ 3 * (A / L n)))
      atTop (nhds (A * t ^ 2)) := by
    have hmul : Tendsto
        (fun n : ℕ ↦ A * (L n / (phi n : ℝ)) ^ 2)
        atTop (nhds (A * t ^ 2)) :=
      tendsto_const_nhds.mul (hratio.pow 2)
    apply hmul.congr'
    filter_upwards [hphiPos] with n hn
    have hN : (phi n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hLn : L n ≠ 0 := by
      dsimp only [L, s, profileScale]
      positivity
    field_simp [hN, hLn]
    ring
  have hA0 : moment 0 ≤ A / t :=
    le_of_tendsto_of_tendsto (hconv 0 (by norm_num)) henv0
      (hupper 0 (by norm_num))
  have hA2 : moment 2 ≤ A * t :=
    le_of_tendsto_of_tendsto (hconv 2 (by norm_num)) henv2
      (hupper 2 (by norm_num))
  have hA3 : moment 3 ≤ A * t ^ 2 :=
    le_of_tendsto_of_tendsto (hconv 3 (by norm_num)) henv3
      (hupper 3 (by norm_num))
  have hsTop : Tendsto s atTop atTop := by
    simpa only [s, gridIndex, max_eq_left ht.le, mul_comm] using
      (natFloor_mul_cofinal_tendsto_atTop phi hphi t ht)
  obtain ⟨B, hB, htheta⟩ := orbitPositiveTiltMass_bound_all
    m data.law data.arity data.critical data.third hnonconstant hExcess
  have hthetaZero : Tendsto
      (fun n : ℕ ↦ orbitPositiveTiltMass m data.law (s n))
      atTop (nhds 0) := by
    have hsOneTop : Tendsto (fun n ↦ s n + 1) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      have hs := hsTop.eventually_ge_atTop b
      exact hs.mono fun n hn ↦ by omega
    have hupperZero := (tendsto_const_div_atTop_nhds_zero_nat B).comp hsOneTop
    apply squeeze_zero'
      (Eventually.of_forall fun n ↦ (htheta (s n)).1)
      (Eventually.of_forall fun n ↦ (htheta (s n)).2)
      hupperZero
  have hdiscOne : Tendsto
      (fun n ↦ scaledDiscreteMoment (rhoN n) 1 (phi n))
      atTop (nhds 1) := by
    have hcomparison : Tendsto
        (fun n : ℕ ↦ 1 - ((m : ℝ) - 1) *
          orbitPositiveTiltMass m data.law (s n))
        atTop (nhds 1) := by
      convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hthetaZero) using 1 <;> ring
    apply hcomparison.congr'
    filter_upwards [hphiPos] with n hn
    have hN : (phi n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hscrit := orbit_critical m data.law
      (le_trans (by norm_num) data.arity) data.critical (s n)
    have hzeroRaw := (positiveTiltedDensity_hasSum
      m (orbit m data.law (s n))
        (le_trans (by norm_num) data.arity) hscrit).summable
    have hzero : Summable (rhoN n) := by
      simpa only [rhoN, s] using hzeroRaw
    have hsthird := orbit_tiltSummable_three m data.law
      (le_trans (by norm_num) data.arity) data.critical data.third (s n)
    have hthreeRaw := positiveTiltedDensity_third_summable
      m (orbit m data.law (s n))
        (le_trans (by norm_num) data.arity) hscrit hsthird
    have hthree : Summable (fun j : ℕ ↦ (j : ℝ) ^ 3 * rhoN n j) := by
      simpa only [rhoN, s] using hthreeRaw
    have hone := moment_summable_of_zero_and_third
      (rhoN n) 1 (by norm_num)
      (fun j ↦ by
        dsimp only [rhoN, s]
        exact positiveTiltedDensity_nonneg m (orbit m data.law (gridIndex (phi n) t))
          (le_trans (by norm_num) data.arity) hscrit j)
      hzero hthree
    have hlinear : Summable (fun j : ℕ ↦ (j : ℝ) * rhoN n j) := by
      simpa only [pow_one] using hone
    have hsplit :
        (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * rhoN n j) =
          (∑' j : ℕ, (j : ℝ) * rhoN n j) + ∑' j : ℕ, rhoN n j := by
      rw [← hlinear.tsum_add hzero]
      apply tsum_congr
      intro j
      push_cast
      ring
    have hshiftEq :
        (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * rhoN n j) = 1 := by
      simpa only [rhoN, s] using hfirstShifted (s n)
    have hmassEq : (∑' j : ℕ, rhoN n j) =
        ((m : ℝ) - 1) * orbitPositiveTiltMass m data.law (s n) := by
      simpa only [rhoN, s] using
        (positiveTiltedDensity_hasSum m (orbit m data.law (s n))
          (le_trans (by norm_num) data.arity) hscrit).tsum_eq
    rw [scaledDiscreteMoment, pow_one, div_self hN, one_mul]
    simp only [pow_one]
    linarith [hsplit, hshiftEq, hmassEq]
  have hA1 : moment 1 = 1 :=
    tendsto_nhds_unique (hconv 1 (by norm_num)) hdiscOne
  simpa only [moment] using And.intro hA0 (And.intro hA1 (And.intro hA2 hA3))

end

end DerridaRetaux.FixedArity
