import DerridaRetaux.Analysis.ProfileCompactnessClamped

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- The square-root modulus furnished by the source smoothing estimates away from time zero. -/
def profileSqrtModulus (C eta q : ℝ) : ℝ :=
  (4 * C / eta ^ 2) * Real.sqrt (q / eta)

/-- The common adjacent-mesh error used for space and time interpolation. -/
def profileMeshStep (C eta : ℝ) (N : ℕ) : ℝ :=
  profileSqrtModulus C eta ((N : ℝ)⁻¹)

theorem profileSqrtModulus_monotone
    {C eta : ℝ} (hC : 0 ≤ C) (heta : 0 < eta) :
    Monotone (profileSqrtModulus C eta) := by
  intro a b hab
  unfold profileSqrtModulus
  have hcoef : 0 ≤ 4 * C / eta ^ 2 := by positivity
  gcongr

private theorem adjacent_space_distance
    {N n j : ℕ} (hN : 0 < N) :
    |(n : ℝ) / (N : ℝ) - (n : ℝ) / (N : ℝ)| +
        |((j + 1 : ℕ) : ℝ) / (N : ℝ) - (j : ℝ) / (N : ℝ)| =
      (N : ℝ)⁻¹ := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sub_self, abs_zero, zero_add]
  have heq : ((j + 1 : ℕ) : ℝ) / (N : ℝ) - (j : ℝ) / (N : ℝ) =
      (N : ℝ)⁻¹ := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [hNreal.ne']
  rw [heq, abs_of_pos (inv_pos.mpr hNreal)]

private theorem adjacent_time_distance
    {N n j : ℕ} (hN : 0 < N) :
    |((n + 1 : ℕ) : ℝ) / (N : ℝ) - (n : ℝ) / (N : ℝ)| +
        |(j : ℝ) / (N : ℝ) - (j : ℝ) / (N : ℝ)| =
      (N : ℝ)⁻¹ := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sub_self, abs_zero, add_zero]
  have heq : ((n + 1 : ℕ) : ℝ) / (N : ℝ) - (n : ℝ) / (N : ℝ) =
      (N : ℝ)⁻¹ := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [hNreal.ne']
  rw [heq, abs_of_pos (inv_pos.mpr hNreal)]

theorem clampedOrbitScaledGrid_adjacent_space
    (m : ℕ) (p₀ : ProbabilityMass) {C eta : ℝ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (C / profileScale n ^ 2))
    (hSpatial : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n) -
          (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
        (smoothingRate C n h))
    (hTemporal : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      SupLE
        (positiveTiltedDensity m (orbit m p₀ (n + h)) -
          positiveTiltedDensity m (orbit m p₀ n))
        (smoothingRate C n h)) :
    ∀ N n j : ℕ, 0 < N →
      |clampedOrbitScaledGrid m p₀ eta N n (j + 1) -
        clampedOrbitScaledGrid m p₀ eta N n j| ≤ profileMeshStep C eta N := by
  intro N n j hN
  have h := clampedOrbitScaledGrid_node_modulus m p₀ hC heta hSup hSpatial hTemporal
    N n (j + 1) n j hN
  simpa only [profileMeshStep, profileSqrtModulus, adjacent_space_distance hN] using h

theorem clampedOrbitScaledGrid_adjacent_time
    (m : ℕ) (p₀ : ProbabilityMass) {C eta : ℝ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (C / profileScale n ^ 2))
    (hSpatial : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n) -
          (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
        (smoothingRate C n h))
    (hTemporal : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      SupLE
        (positiveTiltedDensity m (orbit m p₀ (n + h)) -
          positiveTiltedDensity m (orbit m p₀ n))
        (smoothingRate C n h)) :
    ∀ N n j : ℕ, 0 < N →
      |clampedOrbitScaledGrid m p₀ eta N (n + 1) j -
        clampedOrbitScaledGrid m p₀ eta N n j| ≤ profileMeshStep C eta N := by
  intro N n j hN
  have h := clampedOrbitScaledGrid_node_modulus m p₀ hC heta hSup hSpatial hTemporal
    N (n + 1) j n j hN
  simpa only [profileMeshStep, profileSqrtModulus, adjacent_time_distance hN] using h

theorem profileMeshStep_tendsto_zero
    {C eta : ℝ} (heta : 0 < eta) :
    Tendsto (profileMeshStep C eta) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inverse_atTop_nhds_zero_nat
  have hdiv : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ / eta) atTop (𝓝 0) := by
    convert hinv.div_const eta using 1 <;> simp
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt ((N : ℝ)⁻¹ / eta)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hdiv
  unfold profileMeshStep profileSqrtModulus
  convert tendsto_const_nhds.mul hsqrt using 1 <;> ring

theorem profileSqrtModulus_small
    {C eta : ℝ} (hC : 0 ≤ C) (heta : 0 < eta) :
    ∀ epsilon > 0, ∃ delta > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 < N ∧
        2 * (profileMeshStep C eta N + profileMeshStep C eta N) +
          profileSqrtModulus C eta (delta + 4 / (N : ℝ)) < epsilon := by
  intro epsilon hepsilon
  have homega0 : Tendsto (profileSqrtModulus C eta) (𝓝 0) (𝓝 0) := by
    have hdiv : Tendsto (fun q : ℝ ↦ q / eta) (𝓝 0) (𝓝 0) := by
      have hid : Tendsto (fun q : ℝ ↦ q) (𝓝 0) (𝓝 0) := tendsto_id
      simpa only [zero_div] using hid.div_const eta
    have hsqrt : Tendsto (fun q : ℝ ↦ Real.sqrt (q / eta)) (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0).comp hdiv
    unfold profileSqrtModulus
    convert tendsto_const_nhds.mul hsqrt using 1 <;> ring
  have hnear : ∀ᶠ q : ℝ in 𝓝 0, profileSqrtModulus C eta q < epsilon / 2 :=
    homega0 (Iio_mem_nhds (by linarith))
  obtain ⟨d, hd, hdsub⟩ := Metric.mem_nhds_iff.mp hnear
  let delta : ℝ := d / 2
  have hdelta : 0 < delta := div_pos hd (by norm_num)
  have homegaDelta : profileSqrtModulus C eta delta < epsilon / 2 := by
    apply hdsub
    have hdelta_lt : delta < d := by
      dsimp only [delta]
      linarith
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hdelta] using hdelta_lt
  have hinv : Tendsto (fun N : ℕ ↦ 4 / (N : ℝ)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat using 1 <;> ring
  have harg : Tendsto (fun N : ℕ ↦ delta + 4 / (N : ℝ)) atTop (𝓝 delta) := by
    simpa using tendsto_const_nhds.add hinv
  have homegaDeltaN :
      Tendsto (fun N : ℕ ↦ profileSqrtModulus C eta (delta + 4 / (N : ℝ)))
        atTop (𝓝 (profileSqrtModulus C eta delta)) := by
    exact ((continuous_const.mul
      (Real.continuous_sqrt.comp (continuous_id.div_const eta))).tendsto delta).comp harg
  have hsteps : Tendsto
      (fun N : ℕ ↦ 2 * (profileMeshStep C eta N + profileMeshStep C eta N))
      atTop (𝓝 0) := by
    have hs := profileMeshStep_tendsto_zero (C := C) heta
    convert tendsto_const_nhds.mul (hs.add hs) using 1 <;> ring
  have htotal : Tendsto
      (fun N : ℕ ↦ 2 * (profileMeshStep C eta N + profileMeshStep C eta N) +
        profileSqrtModulus C eta (delta + 4 / (N : ℝ)))
      atTop (𝓝 (profileSqrtModulus C eta delta)) := by
    simpa using hsteps.add homegaDeltaN
  have hevent : ∀ᶠ N : ℕ in atTop,
      2 * (profileMeshStep C eta N + profileMeshStep C eta N) +
        profileSqrtModulus C eta (delta + 4 / (N : ℝ)) < epsilon :=
    htotal (Iio_mem_nhds (homegaDelta.trans (by linarith)))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hevent
  refine ⟨delta, hdelta, max 1 N₁, ?_⟩
  intro N hN
  refine ⟨lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left 1 N₁) hN), ?_⟩
  exact hN₁ N (le_trans (le_max_right 1 N₁) hN)

theorem clampedOrbitInterpolants_eventuallyUniformlyBoundedOn
    (m : ℕ) (p₀ : ProbabilityMass) {C eta T R : ℝ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (C / profileScale n ^ 2)) :
    EventuallyUniformlyBoundedOn
      (fun N p ↦ gridBilinearInterp N (clampedOrbitScaledGrid m p₀ eta N) p.1 p.2)
      (compactRectangle eta T R) := by
  refine ⟨C / eta ^ 2, 1, ?_⟩
  intro N hN p hp
  exact gridBilinearInterp_family_uniformlyBoundedOn_rectangle
    (clampedOrbitScaledGrid m p₀ eta) eta T R (C / eta ^ 2)
    (fun N n j _ ↦ clampedOrbitScaledGrid_node_bound m p₀ hC heta hSup N n j)
    N (lt_of_lt_of_le Nat.zero_lt_one hN) p hp

theorem clampedOrbitInterpolants_eventuallyEquicontinuousOn
    (m : ℕ) (p₀ : ProbabilityMass) {C eta T R : ℝ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hSup : ∀ n : ℕ, WeightedSupThreeLE (profileScale n)
      (positiveTiltedDensity m (orbit m p₀ n))
      (C / profileScale n ^ 2))
    (hSpatial : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      WeightedSupThreeLE (profileScale n)
        (positiveTiltedDensity m (orbit m p₀ n) -
          (shiftLeft^[h]) (positiveTiltedDensity m (orbit m p₀ n)))
        (smoothingRate C n h))
    (hTemporal : ∀ n h : ℕ, 1 ≤ h → h ≤ n + 1 →
      SupLE
        (positiveTiltedDensity m (orbit m p₀ (n + h)) -
          positiveTiltedDensity m (orbit m p₀ n))
        (smoothingRate C n h)) :
    EventuallyEquicontinuousOnL1
      (fun N p ↦ gridBilinearInterp N (clampedOrbitScaledGrid m p₀ eta N) p.1 p.2)
      (compactRectangle eta T R) := by
  apply gridBilinearInterp_family_eventuallyEquicontinuousOn_rectangle
    (clampedOrbitScaledGrid m p₀ eta) (profileSqrtModulus C eta)
    (profileMeshStep C eta) (profileMeshStep C eta) eta T R heta.le
    (profileSqrtModulus_monotone hC heta)
  · exact clampedOrbitScaledGrid_adjacent_space m p₀ hC heta hSup hSpatial hTemporal
  · exact clampedOrbitScaledGrid_adjacent_time m p₀ hC heta hSup hSpatial hTemporal
  · exact clampedOrbitScaledGrid_node_modulus m p₀ hC heta hSup hSpatial hTemporal
  · exact profileSqrtModulus_small hC heta

end

end DerridaRetaux.FixedArity
