import DerridaRetaux.Analysis.SmoothingOrbitBounds
import DerridaRetaux.Prelim.AtomTail
import Mathlib.Tactic

set_option autoImplicit false

open Filter Topology

namespace DerridaRetaux

noncomputable section

/-!
# Limits and variation of the smoothing coefficients

This file formalizes the coefficient estimates preceding source equation
`eq:coefficientbounds`.  The published excess estimate `H1a` and the pointwise
estimate `eq:sup` are explicit theorem parameters.  No profile conclusion is used.
-/

/-- The quadratic density coefficient as a scalar function of the zero atom. -/
def quadraticDensityAt (m : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose m 2 : ℝ) * x ^ (m - 2) /
    ((1 + ((m : ℝ) - 1) * x ^ m) * ((m : ℝ) - 1))

/-- A uniform Lipschitz constant for `quadraticDensityAt m` on `[0, 1]`. -/
def quadraticDensityLipschitzConstant (m : ℕ) : ℝ :=
  ((Nat.choose m 2 : ℝ) / ((m : ℝ) - 1)) *
    (((m - 2 : ℕ) : ℝ) + ((m : ℝ) - 1) * (m : ℝ))

/-- The constant in the quadratic transport-defect estimate. -/
def transportDefectBoundConstant (m : ℕ) (Ctheta : ℝ) : ℝ :=
  ((m - 1 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) + 1) / 2 * Ctheta ^ 2

/-- The combined zero-atom variation constant furnished by `H1a` and `eq:sup`. -/
def zeroTiltVariationConstant (m : ℕ) (Ctheta B : ℝ) : ℝ :=
  transportDefectBoundConstant m Ctheta + B

/-- The orbit coefficient `d_s` is the scalar function above evaluated at `x_s`. -/
theorem densityCoeff_two_eq_quadraticDensityAt
    (m : ℕ) (p : ProbabilityMass) :
    densityCoeff m 2 p = quadraticDensityAt m (zeroTilt m p) := by
  simp [densityCoeff, quadraticDensityAt, tiltDenom]

/-- At the limiting zero atom `x = 1`, the quadratic coefficient is `1 / 2`. -/
theorem quadraticDensityAt_one (m : ℕ) (hm : 2 ≤ m) :
    quadraticDensityAt m 1 = (1 : ℝ) / 2 := by
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have hmReal : (1 : ℝ) < m := by
      exact_mod_cast (show 1 < m by omega)
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [quadraticDensityAt, one_pow, one_pow, Nat.cast_choose_two]
  field_simp [hm0, hm1]
  ring

/-- The scalar coefficient function is continuous at its limiting argument. -/
theorem quadraticDensityAt_continuousAt_one (m : ℕ) (hm : 2 ≤ m) :
    ContinuousAt (quadraticDensityAt m) 1 := by
  unfold quadraticDensityAt
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · have hm1 : (m : ℝ) - 1 ≠ 0 := by
      have hmReal : (1 : ℝ) < m := by
        exact_mod_cast (show 1 < m by omega)
      linarith
    have hm0 : m ≠ 0 := by omega
    norm_num [hm1, hm0]

/-- `H1a` forces the zero atom of the normalized tilt to converge to one. -/
theorem orbit_zeroTilt_tendsto_one_of_excess
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    Tendsto (fun n : ℕ ↦ zeroTilt m (orbit m p₀ n)) atTop (𝓝 1) := by
  have htheta := orbitPositiveTiltMass_tendsto_zero
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hsub := hone.sub htheta
  simpa [orbitPositiveTiltMass, positiveTiltMass] using hsub

/-- Consequently the quadratic coefficient tends to its source value `1 / 2`. -/
theorem orbit_densityD_tendsto_half_of_excess
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (hcrit : Critical m p₀)
    (hthird : TiltSummable m 3 p₀) (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant) :
    Tendsto (densityD m p₀) atTop (𝓝 ((1 : ℝ) / 2)) := by
  have hx := orbit_zeroTilt_tendsto_one_of_excess
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hd := (quadraticDensityAt_continuousAt_one m hm).tendsto.comp hx
  rw [quadraticDensityAt_one m hm] at hd
  apply hd.congr'
  filter_upwards [] with n
  exact (densityCoeff_two_eq_quadraticDensityAt m (orbit m p₀ n)).symm

private theorem abs_pow_sub_pow_le_nat_mul_abs_sub_of_unit
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (n : ℕ) :
    |x ^ n - y ^ n| ≤ (n : ℝ) * |x - y| := by
  have hmax0 : 0 ≤ max |x| |y| :=
    (abs_nonneg x).trans (le_max_left |x| |y|)
  have hmax1 : max |x| |y| ≤ 1 := by
    apply max_le
    · simpa [abs_of_nonneg hx0] using hx1
    · simpa [abs_of_nonneg hy0] using hy1
  calc
    |x ^ n - y ^ n| ≤
        |x - y| * (n : ℝ) * max |x| |y| ^ (n - 1) :=
      abs_pow_sub_pow_le x y n
    _ ≤ |x - y| * (n : ℝ) * 1 := by
      exact mul_le_mul_of_nonneg_left (pow_le_one₀ hmax0 hmax1)
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg n))
    _ = (n : ℝ) * |x - y| := by ring

private theorem abs_inv_tiltDenomAt_sub_le
    (m : ℕ) (hm : 2 ≤ m) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(1 + ((m : ℝ) - 1) * x ^ m)⁻¹ -
        (1 + ((m : ℝ) - 1) * y ^ m)⁻¹| ≤
      ((m : ℝ) - 1) * (m : ℝ) * |x - y| := by
  let F : ℝ := (m : ℝ) - 1
  let Dx : ℝ := 1 + F * x ^ m
  let Dy : ℝ := 1 + F * y ^ m
  have hF : 0 ≤ F := by
    dsimp [F]
    exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ m by omega))
  have hDx : 1 ≤ Dx := by
    dsimp [Dx]
    exact le_add_of_nonneg_right (mul_nonneg hF (pow_nonneg hx0 m))
  have hDy : 1 ≤ Dy := by
    dsimp [Dy]
    exact le_add_of_nonneg_right (mul_nonneg hF (pow_nonneg hy0 m))
  have hDxPos : 0 < Dx := lt_of_lt_of_le zero_lt_one hDx
  have hDyPos : 0 < Dy := lt_of_lt_of_le zero_lt_one hDy
  have hden : 1 ≤ |Dx * Dy| := by
    rw [abs_of_pos (mul_pos hDxPos hDyPos)]
    nlinarith
  have hdenPos : 0 < |Dx * Dy| := lt_of_lt_of_le zero_lt_one hden
  have hp : |y ^ m - x ^ m| ≤ (m : ℝ) * |x - y| := by
    simpa [abs_sub_comm] using
      abs_pow_sub_pow_le_nat_mul_abs_sub_of_unit hx0 hx1 hy0 hy1 m
  have hnum : |Dy - Dx| ≤ F * (m : ℝ) * |x - y| := by
    dsimp [Dx, Dy]
    rw [show 1 + F * y ^ m - (1 + F * x ^ m) =
        F * (y ^ m - x ^ m) by ring]
    rw [abs_mul, abs_of_nonneg hF]
    calc
      F * |y ^ m - x ^ m| ≤ F * ((m : ℝ) * |x - y|) :=
        mul_le_mul_of_nonneg_left hp hF
      _ = F * (m : ℝ) * |x - y| := by ring
  change |Dx⁻¹ - Dy⁻¹| ≤ _
  calc
    |Dx⁻¹ - Dy⁻¹| = |Dy - Dx| / |Dx * Dy| := by
      rw [inv_sub_inv hDxPos.ne' hDyPos.ne', abs_div]
    _ ≤ |Dy - Dx| := by
      apply (div_le_iff₀ hdenPos).2
      nlinarith [abs_nonneg (Dy - Dx)]
    _ ≤ F * (m : ℝ) * |x - y| := hnum
    _ = ((m : ℝ) - 1) * (m : ℝ) * |x - y| := by rfl

/-- `quadraticDensityAt m` is uniformly Lipschitz on the full unit interval. -/
theorem quadraticDensityAt_lipschitz_on_unit
    (m : ℕ) (hm : 2 ≤ m) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |quadraticDensityAt m x - quadraticDensityAt m y| ≤
      quadraticDensityLipschitzConstant m * |x - y| := by
  let A : ℝ := Nat.choose m 2
  let F : ℝ := (m : ℝ) - 1
  let Dx : ℝ := 1 + F * x ^ m
  let Dy : ℝ := 1 + F * y ^ m
  let e : ℕ := m - 2
  have hF : 0 < F := by
    dsimp [F]
    have hmReal : (1 : ℝ) < m := by
      exact_mod_cast (show 1 < m by omega)
    linarith
  have hA : 0 ≤ A := by positivity
  have hcoef : 0 ≤ A / F := div_nonneg hA hF.le
  have hDx : 1 ≤ Dx := by
    dsimp [Dx]
    exact le_add_of_nonneg_right (mul_nonneg hF.le (pow_nonneg hx0 m))
  have hDy : 1 ≤ Dy := by
    dsimp [Dy]
    exact le_add_of_nonneg_right (mul_nonneg hF.le (pow_nonneg hy0 m))
  have hDxPos : 0 < Dx := lt_of_lt_of_le zero_lt_one hDx
  have hDyPos : 0 < Dy := lt_of_lt_of_le zero_lt_one hDy
  have hDxInv : |Dx⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hDxPos)]
    exact inv_le_one_of_one_le₀ hDx
  have hyPow : |y ^ e| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hy0 e)]
    exact pow_le_one₀ hy0 hy1
  have hpow : |x ^ e - y ^ e| ≤ (e : ℝ) * |x - y| :=
    abs_pow_sub_pow_le_nat_mul_abs_sub_of_unit hx0 hx1 hy0 hy1 e
  have hinv : |Dx⁻¹ - Dy⁻¹| ≤ F * (m : ℝ) * |x - y| := by
    simpa only [F, Dx, Dy] using
      abs_inv_tiltDenomAt_sub_le m hm hx0 hx1 hy0 hy1
  have hterm1 :
      |x ^ e - y ^ e| * |Dx⁻¹| ≤ ((e : ℝ) * |x - y|) * 1 := by
    calc
      |x ^ e - y ^ e| * |Dx⁻¹| ≤
          ((e : ℝ) * |x - y|) * |Dx⁻¹| :=
        mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ ≤ ((e : ℝ) * |x - y|) * 1 :=
        mul_le_mul_of_nonneg_left hDxInv
          (mul_nonneg (Nat.cast_nonneg e) (abs_nonneg _))
  have hterm2 :
      |y ^ e| * |Dx⁻¹ - Dy⁻¹| ≤
        1 * (F * (m : ℝ) * |x - y|) := by
    calc
      |y ^ e| * |Dx⁻¹ - Dy⁻¹| ≤ 1 * |Dx⁻¹ - Dy⁻¹| :=
        mul_le_mul_of_nonneg_right hyPow (abs_nonneg _)
      _ ≤ 1 * (F * (m : ℝ) * |x - y|) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hinner :
      |x ^ e * Dx⁻¹ - y ^ e * Dy⁻¹| ≤
        ((e : ℝ) + F * (m : ℝ)) * |x - y| := by
    calc
      |x ^ e * Dx⁻¹ - y ^ e * Dy⁻¹| =
          |(x ^ e - y ^ e) * Dx⁻¹ +
            y ^ e * (Dx⁻¹ - Dy⁻¹)| := by
        congr 1
        ring
      _ ≤ |(x ^ e - y ^ e) * Dx⁻¹| +
          |y ^ e * (Dx⁻¹ - Dy⁻¹)| :=
        abs_add_le _ _
      _ = |x ^ e - y ^ e| * |Dx⁻¹| +
          |y ^ e| * |Dx⁻¹ - Dy⁻¹| := by
        rw [abs_mul, abs_mul]
      _ ≤ ((e : ℝ) * |x - y|) * 1 +
          1 * (F * (m : ℝ) * |x - y|) :=
        add_le_add hterm1 hterm2
      _ = ((e : ℝ) + F * (m : ℝ)) * |x - y| := by ring
  have hrewrite : ∀ z D : ℝ,
      A * z ^ e / (D * F) = (A / F) * (z ^ e * D⁻¹) := by
    intro z D
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [quadraticDensityAt]
  change |A * x ^ e / (Dx * F) - A * y ^ e / (Dy * F)| ≤ _
  rw [hrewrite x Dx, hrewrite y Dy]
  have habs :
      |A / F * (x ^ e * Dx⁻¹) - A / F * (y ^ e * Dy⁻¹)| =
        A / F * |x ^ e * Dx⁻¹ - y ^ e * Dy⁻¹| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hcoef]
  rw [habs]
  calc
    A / F * |x ^ e * Dx⁻¹ - y ^ e * Dy⁻¹| ≤
        A / F * (((e : ℝ) + F * (m : ℝ)) * |x - y|) :=
      mul_le_mul_of_nonneg_left hinner hcoef
    _ = quadraticDensityLipschitzConstant m * |x - y| := by
      simp only [quadraticDensityLipschitzConstant, A, F, e]
      ring

/-- Along a critical orbit, the `d`-coefficient variation is controlled by the
corresponding zero-atom variation. -/
theorem orbit_densityD_sub_le_zeroTilt_sub
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (s t : ℕ) :
    |densityD m p₀ s - densityD m p₀ t| ≤
      quadraticDensityLipschitzConstant m *
        |zeroTilt m (orbit m p₀ s) - zeroTilt m (orbit m p₀ t)| := by
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  have htcrit := orbit_critical m p₀ (by omega) hcrit t
  have hs0 := normalizedTilt_nonneg m (orbit m p₀ s) (by omega) hscrit 0
  have ht0 := normalizedTilt_nonneg m (orbit m p₀ t) (by omega) htcrit 0
  have hs1 := zeroTilt_le_one m (orbit m p₀ s) (by omega) hscrit
  have ht1 := zeroTilt_le_one m (orbit m p₀ t) (by omega) htcrit
  rw [densityD, densityD]
  rw [densityCoeff_two_eq_quadraticDensityAt,
    densityCoeff_two_eq_quadraticDensityAt]
  exact quadraticDensityAt_lipschitz_on_unit
    m hm hs0 hs1 ht0 ht1

/-- An explicit `theta_n` bound and `eq:sup` give the one-step
`|x_(s+1)-x_s|` estimate with no asymptotic notation. -/
theorem orbit_zeroTilt_succ_variation_of_bounds
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (Ctheta : ℝ) (hCtheta : 0 ≤ Ctheta)
    (htheta : ∀ n : ℕ,
      orbitPositiveTiltMass m p₀ n ≤ Ctheta / ((n + 1 : ℕ) : ℝ))
    (B : ℝ)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2))
    (s : ℕ) :
    |zeroTilt m (orbit m p₀ (s + 1)) -
        zeroTilt m (orbit m p₀ s)| ≤
      zeroTiltVariationConstant m Ctheta B /
        ((s + 1 : ℕ) : ℝ) ^ 2 := by
  let L : ℝ := ((s + 1 : ℕ) : ℝ)
  let x : ℝ := zeroTilt m (orbit m p₀ s)
  let q : ℝ := firstTiltedAtom m p₀ s
  let c : ℝ := transportCoeff m (orbit m p₀ s)
  let K : ℝ := transportDefectBoundConstant m Ctheta
  have hB : 0 ≤ B := by
    have hs := hSup 0 0
    have habs :
        |positiveTiltedDensity m (orbit m p₀ 0) 0| ≤ B := by
      simpa [cubicWeight] using hs
    exact (abs_nonneg _).trans habs
  have hK : 0 ≤ K := by
    dsimp [K, transportDefectBoundConstant]
    positivity
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact normalizedTilt_nonneg m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s) 0
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact zeroTilt_le_one m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s)
  have hq0 : 0 ≤ q := by
    dsimp [q, firstTiltedAtom]
    exact normalizedTilt_nonneg m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s) 1
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact transportCoeff_nonneg m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s)
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact transportCoeff_le_one m (orbit m p₀ s) (by omega)
      (orbit_critical m p₀ (by omega) hcrit s)
  have hq : q ≤ B / L ^ 2 := by
    have hfactor : (1 : ℝ) ≤ (m : ℝ) - 1 := by
      have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hbeta := abs_densityBeta_orbit_le_of_pointwise m p₀ B hSup s
    calc
      q = 1 * q := by ring
      _ ≤ ((m : ℝ) - 1) * q :=
        mul_le_mul_of_nonneg_right hfactor hq0
      _ = densityBeta m p₀ s := by
        simp only [q, densityBeta, firstTiltedAtom,
          positiveTiltedDensity_apply]
      _ ≤ |densityBeta m p₀ s| := le_abs_self _
      _ ≤ B / L ^ 2 := by simpa only [L] using hbeta
  have hdefect : 1 - c ≤ K / L ^ 2 := by
    simpa only [c, K, L, transportDefectBoundConstant,
      orbitTransportDefect] using
      orbitTransportDefect_le_of_positiveTiltMass_bound
        m p₀ (by omega) hcrit Ctheta hCtheta htheta s
  have hdefect0 : 0 ≤ 1 - c := by linarith
  have hcq : c * q ≤ q := by
    simpa using mul_le_mul_of_nonneg_right hc1 hq0
  have hneg : (c - 1) * x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc1) hx0
  have hdefectx : (1 - c) * x ≤ 1 - c :=
    mul_le_of_le_one_right hdefect0 hx1
  have hcq0 : 0 ≤ c * q := mul_nonneg hc0 hq0
  have hrec := orbitZeroTilt_succ_eq_transportCoeff_mul
    m p₀ (by omega) hcrit s
  change |zeroTilt m (orbit m p₀ (s + 1)) - x| ≤ _
  rw [hrec]
  change |c * (x + q) - x| ≤ _
  apply abs_le.mpr
  constructor
  · calc
      -(zeroTiltVariationConstant m Ctheta B / L ^ 2) ≤
          -(K / L ^ 2) := by
        apply neg_le_neg
        apply div_le_div_of_nonneg_right _ (sq_nonneg L)
        simp only [zeroTiltVariationConstant]
        exact le_add_of_nonneg_right hB
      _ ≤ -(1 - c) := neg_le_neg hdefect
      _ ≤ (c - 1) * x := by nlinarith
      _ ≤ (c - 1) * x + c * q := le_add_of_nonneg_right hcq0
      _ = c * (x + q) - x := by ring
  · calc
      c * (x + q) - x = (c - 1) * x + c * q := by ring
      _ ≤ 0 + q := add_le_add hneg hcq
      _ ≤ B / L ^ 2 := by simpa using hq
      _ ≤ zeroTiltVariationConstant m Ctheta B / L ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg L)
        simp only [zeroTiltVariationConstant]
        exact le_add_of_nonneg_left hK

/-- A reciprocal-square zero-atom variation bound transfers literally to the
source-indexed coefficient variation.  The factor four accounts for changing
the denominator from `s^2` to `(s+1)^2`. -/
theorem orbit_densityD_variation_of_zeroTilt_variation
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n : ℕ,
      |zeroTilt m (orbit m p₀ (n + 1)) -
          zeroTilt m (orbit m p₀ n)| ≤
        C / ((n + 1 : ℕ) : ℝ) ^ 2) :
    ∀ s : ℕ, 1 ≤ s →
      |densityD m p₀ s - densityD m p₀ (s - 1)| ≤
        (4 * quadraticDensityLipschitzConstant m * C) /
          ((s + 1 : ℕ) : ℝ) ^ 2 := by
  intro s hs
  have hsPos : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hs)
  have hsSuccPos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
  have hxPrev :
      |zeroTilt m (orbit m p₀ s) -
          zeroTilt m (orbit m p₀ (s - 1))| ≤
        C / (s : ℝ) ^ 2 := by
    simpa [Nat.sub_add_cancel hs] using hx (s - 1)
  have hLip : 0 ≤ quadraticDensityLipschitzConstant m := by
    rw [quadraticDensityLipschitzConstant]
    have hfactor : 0 < (m : ℝ) - 1 := by
      have hmReal : (1 : ℝ) < m := by
        exact_mod_cast (show 1 < m by omega)
      linarith
    positivity
  have hLC : 0 ≤ quadraticDensityLipschitzConstant m * C :=
    mul_nonneg hLip hC
  have hscale :
      quadraticDensityLipschitzConstant m * (C / (s : ℝ) ^ 2) =
        (quadraticDensityLipschitzConstant m * C) / (s : ℝ) ^ 2 := by
    ring
  have hcompare :
      (quadraticDensityLipschitzConstant m * C) / (s : ℝ) ^ 2 ≤
        (4 * quadraticDensityLipschitzConstant m * C) /
          ((s + 1 : ℕ) : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hsPos) (sq_pos_of_pos hsSuccPos)).2
    have hsCast : ((s + 1 : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
      exact_mod_cast (show s + 1 ≤ 2 * s by omega)
    have hsq : ((s + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * (s : ℝ) ^ 2 := by
      nlinarith
    calc
      quadraticDensityLipschitzConstant m * C *
            ((s + 1 : ℕ) : ℝ) ^ 2 ≤
          quadraticDensityLipschitzConstant m * C *
            (4 * (s : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hLC
      _ = 4 * quadraticDensityLipschitzConstant m * C *
            (s : ℝ) ^ 2 := by ring
  calc
    |densityD m p₀ s - densityD m p₀ (s - 1)| ≤
        quadraticDensityLipschitzConstant m *
          |zeroTilt m (orbit m p₀ s) -
            zeroTilt m (orbit m p₀ (s - 1))| :=
      orbit_densityD_sub_le_zeroTilt_sub m p₀ hm hcrit s (s - 1)
    _ ≤ quadraticDensityLipschitzConstant m * (C / (s : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hxPrev hLip
    _ = (quadraticDensityLipschitzConstant m * C) / (s : ℝ) ^ 2 :=
      hscale
    _ ≤ (4 * quadraticDensityLipschitzConstant m * C) /
          ((s + 1 : ℕ) : ℝ) ^ 2 := hcompare

/-- Source-shaped closure of `U29`: `H1a` and the still-explicit pointwise
`eq:sup` estimate yield all three coefficient limits and all three quadratic
one-step/defect bounds with one positive constant. -/
theorem coefficientVariation_orbit_of_H1a_and_pointwise
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (B : ℝ)
    (hSup : ∀ n : ℕ,
      WeightedSupThreeLE ((n + 1 : ℕ) : ℝ)
        (positiveTiltedDensity m (orbit m p₀ n))
        (B / ((n + 1 : ℕ) : ℝ) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (orbitPositiveTiltMass m p₀) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ zeroTilt m (orbit m p₀ n)) atTop (𝓝 1) ∧
      Tendsto (densityD m p₀) atTop (𝓝 ((1 : ℝ) / 2)) ∧
      (∀ s : ℕ,
        |1 - transportCoeff m (orbit m p₀ s)| ≤
          C / ((s + 1 : ℕ) : ℝ) ^ 2) ∧
      (∀ s : ℕ,
        |zeroTilt m (orbit m p₀ (s + 1)) -
            zeroTilt m (orbit m p₀ s)| ≤
          C / ((s + 1 : ℕ) : ℝ) ^ 2) ∧
      ∀ s : ℕ, 1 ≤ s →
        |densityD m p₀ s - densityD m p₀ (s - 1)| ≤
          C / ((s + 1 : ℕ) : ℝ) ^ 2 := by
  rcases orbitPositiveTiltMass_bound_all
      m p₀ hm hcrit hthird hnonconstant hExcess with
    ⟨Ctheta, hCtheta, htheta⟩
  let Cx := zeroTiltVariationConstant m Ctheta B
  let Lip := quadraticDensityLipschitzConstant m
  let C := Cx + 4 * Lip * Cx
  have hB : 0 ≤ B := by
    have hzero := hSup 0 0
    have habs :
        |positiveTiltedDensity m (orbit m p₀ 0) 0| ≤ B := by
      simpa [cubicWeight] using hzero
    exact (abs_nonneg _).trans habs
  have hdefectPos : 0 < transportDefectBoundConstant m Ctheta := by
    have hmSub : 0 < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m - 1 by omega)
    dsimp [transportDefectBoundConstant]
    positivity
  have hCx : 0 < Cx := by
    dsimp [Cx, zeroTiltVariationConstant]
    exact add_pos_of_pos_of_nonneg hdefectPos hB
  have hLip : 0 ≤ Lip := by
    dsimp [Lip, quadraticDensityLipschitzConstant]
    have hfactor : 0 < (m : ℝ) - 1 := by
      have hmReal : (1 : ℝ) < m := by
        exact_mod_cast (show 1 < m by omega)
      linarith
    positivity
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg hCx
      (mul_nonneg (mul_nonneg (by norm_num) hLip) hCx.le)
  have hmass := orbitPositiveTiltMass_tendsto_zero
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hxLimit := orbit_zeroTilt_tendsto_one_of_excess
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hdLimit := orbit_densityD_tendsto_half_of_excess
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hcDefect : ∀ s : ℕ,
      |1 - transportCoeff m (orbit m p₀ s)| ≤
        Cx / ((s + 1 : ℕ) : ℝ) ^ 2 := by
    intro s
    have hnonneg := orbitTransportDefect_nonneg m p₀ (by omega) hcrit s
    have hraw := orbitTransportDefect_le_of_positiveTiltMass_bound
      m p₀ (by omega) hcrit Ctheta hCtheta.le (fun n ↦ (htheta n).2) s
    rw [orbitTransportDefect] at hnonneg hraw
    rw [abs_of_nonneg hnonneg]
    exact hraw.trans (by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      dsimp [Cx, zeroTiltVariationConstant]
      exact le_add_of_nonneg_right hB)
  have hxVariation : ∀ s : ℕ,
      |zeroTilt m (orbit m p₀ (s + 1)) -
          zeroTilt m (orbit m p₀ s)| ≤
        Cx / ((s + 1 : ℕ) : ℝ) ^ 2 := by
    intro s
    exact orbit_zeroTilt_succ_variation_of_bounds
      m p₀ hm hcrit Ctheta hCtheta.le (fun n ↦ (htheta n).2) B hSup s
  have hdVariation := orbit_densityD_variation_of_zeroTilt_variation
    m p₀ hm hcrit Cx hCx.le hxVariation
  refine ⟨C, hC, hmass, hxLimit, hdLimit, ?_, ?_, ?_⟩
  · intro s
    exact (hcDefect s).trans (by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      dsimp [C]
      exact le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by norm_num) hLip) hCx.le))
  · intro s
    calc
      |zeroTilt m (orbit m p₀ (s + 1)) -
          zeroTilt m (orbit m p₀ s)| ≤
          Cx / ((s + 1 : ℕ) : ℝ) ^ 2 := hxVariation s
      _ ≤ C / ((s + 1 : ℕ) : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        dsimp [C]
        exact le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (by norm_num) hLip) hCx.le)
  · intro s hs
    calc
      |densityD m p₀ s - densityD m p₀ (s - 1)| ≤
          (4 * Lip * Cx) / ((s + 1 : ℕ) : ℝ) ^ 2 := by
        simpa only [Lip] using hdVariation s hs
      _ ≤ C / ((s + 1 : ℕ) : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        dsimp [C]
        exact le_add_of_nonneg_left hCx.le

end

end DerridaRetaux
