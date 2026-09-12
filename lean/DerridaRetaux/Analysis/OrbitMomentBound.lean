import DerridaRetaux.Analysis.WeightedMomentBound
import DerridaRetaux.Analysis.TimeRiemannLimit

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- The weighted `l1` estimate supplies an eventual bound for every rescaled
orbit moment of order at most three at a fixed positive macroscopic time. -/
theorem orbit_scaledDiscreteMoment_eventually_bounded_of_weightedL1
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A : ℝ) (hA : 0 ≤ A)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / profileScale s)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (r : ℕ) (hr : r ≤ 3) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      scaledDiscreteMoment
        (positiveTiltedDensity m
          (orbit m p₀ (gridIndex (scale n) t))) r (scale n) ≤ C := by
  let L : ℕ → ℝ := fun n ↦ profileScale (gridIndex (scale n) t)
  let E : ℕ → ℝ := fun n ↦
    ((scale n : ℝ) / (scale n : ℝ) ^ r) *
      (L n ^ r * (A / L n))
  have hratio : Tendsto (fun n ↦ L n / (scale n : ℝ))
      atTop (nhds t) := by
    have hgrid := (gridIndex_div_tendsto t ht.le).comp hscale
    have hinv := tendsto_inverse_atTop_nhds_zero_nat.comp hscale
    have hadd := hgrid.add hinv
    convert hadd using 1 <;> simp [L, profileScale, Function.comp_def, add_div, one_div]
  have hE : ∃ z : ℝ, Tendsto E atTop (nhds z) := by
    have hrCases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrCases with rfl | rfl | rfl | rfl
    · refine ⟨A / t, ?_⟩
      have hinv := hratio.inv₀ ht.ne'
      have hmul : Tendsto
          (fun n : ℕ ↦ A * (L n / (scale n : ℝ))⁻¹)
          atTop (nhds (A * t⁻¹)) := tendsto_const_nhds.mul hinv
      have hmul' : Tendsto
          (fun n : ℕ ↦ A * (L n / (scale n : ℝ))⁻¹)
          atTop (nhds (A / t)) := by
        simpa [div_eq_mul_inv] using hmul
      apply hmul'.congr'
      have hscalePos := hscale.eventually_ge_atTop 1
      filter_upwards [hscalePos] with n hn
      have hN : (scale n : ℝ) ≠ 0 := by exact_mod_cast (by omega : scale n ≠ 0)
      have hLn : L n ≠ 0 := by
        dsimp only [L, profileScale]
        positivity
      simp [E]
      field_simp [hN, hLn]
      ring
    · refine ⟨A, ?_⟩
      apply tendsto_const_nhds.congr'
      have hscalePos := hscale.eventually_ge_atTop 1
      filter_upwards [hscalePos] with n hn
      have hN : (scale n : ℝ) ≠ 0 := by exact_mod_cast (by omega : scale n ≠ 0)
      have hLn : L n ≠ 0 := by
        dsimp only [L, profileScale]
        positivity
      simp [E]
      field_simp [hN, hLn]
    · refine ⟨A * t, ?_⟩
      have hmul : Tendsto
          (fun n : ℕ ↦ A * (L n / (scale n : ℝ)))
          atTop (nhds (A * t)) := tendsto_const_nhds.mul hratio
      apply hmul.congr'
      have hscalePos := hscale.eventually_ge_atTop 1
      filter_upwards [hscalePos] with n hn
      have hN : (scale n : ℝ) ≠ 0 := by exact_mod_cast (by omega : scale n ≠ 0)
      have hLn : L n ≠ 0 := by
        dsimp only [L, profileScale]
        positivity
      simp [E]
      field_simp [hN, hLn]
      ring
    · refine ⟨A * t ^ 2, ?_⟩
      have hmul : Tendsto
          (fun n : ℕ ↦ A * (L n / (scale n : ℝ)) ^ 2)
          atTop (nhds (A * t ^ 2)) :=
        tendsto_const_nhds.mul (hratio.pow 2)
      apply hmul.congr'
      have hscalePos := hscale.eventually_ge_atTop 1
      filter_upwards [hscalePos] with n hn
      have hN : (scale n : ℝ) ≠ 0 := by exact_mod_cast (by omega : scale n ≠ 0)
      have hLn : L n ≠ 0 := by
        dsimp only [L, profileScale]
        positivity
      simp [E]
      field_simp [hN, hLn]
      ring
  obtain ⟨z, hz⟩ := hE
  obtain ⟨C, hEC⟩ := hz.isBoundedUnder_le
  refine ⟨C, ?_⟩
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge := hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  filter_upwards [hscalePos, hEC] with n hn hEn
  let s := gridIndex (scale n) t
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  have hsthird := orbit_tiltSummable_three m p₀ (by omega) hcrit hthird s
  have hrho : ∀ j : ℕ,
      0 ≤ positiveTiltedDensity m (orbit m p₀ s) j :=
    positiveTiltedDensity_nonneg m (orbit m p₀ s) (by omega) hscrit
  have hmoment : Summable (fun j : ℕ ↦
      (j : ℝ) ^ r * positiveTiltedDensity m (orbit m p₀ s) j) := by
    have hzero := (positiveTiltedDensity_hasSum
      m (orbit m p₀ s) (by omega) hscrit).summable
    have hthree := positiveTiltedDensity_third_summable
      m (orbit m p₀ s) (by omega) hscrit hsthird
    exact moment_summable_of_zero_and_third _ r hr hrho hzero hthree
  have hweighted := weightedAbs_positiveTiltedDensity_orbit_summable
    m p₀ hm hcrit hthird s
  have hraw := scaledDiscreteMoment_le_weightedL1
    (positiveTiltedDensity m (orbit m p₀ s)) r (scale n) (L n)
      hr hn (by dsimp only [L, profileScale]; positivity)
      hrho hmoment (by simpa only [L, s] using hweighted)
  have hweightedBound :
      weightedL1Three (L n) (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / L n := by
    simpa only [L, s] using hL1 s
  have hfactor : 0 ≤
      (scale n : ℝ) / (scale n : ℝ) ^ r * L n ^ r := by
    exact mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) r))
      (pow_nonneg (by dsimp only [L, profileScale]; positivity) r)
  have htoE :
      ((scale n : ℝ) / (scale n : ℝ) ^ r) *
          (L n ^ r * weightedL1Three (L n)
            (positiveTiltedDensity m (orbit m p₀ s))) ≤ E n := by
    simp [E]
    calc
      ((scale n : ℝ) / (scale n : ℝ) ^ r) *
          (L n ^ r * weightedL1Three (L n)
            (positiveTiltedDensity m (orbit m p₀ s))) =
        (((scale n : ℝ) / (scale n : ℝ) ^ r) * L n ^ r) *
          weightedL1Three (L n)
            (positiveTiltedDensity m (orbit m p₀ s)) := by ring
      _ ≤ (((scale n : ℝ) / (scale n : ℝ) ^ r) * L n ^ r) *
          (A / L n) := mul_le_mul_of_nonneg_left hweightedBound hfactor
      _ = E n := by simp [E]; ring
  exact hraw.trans (htoE.trans hEn)

end

end DerridaRetaux
