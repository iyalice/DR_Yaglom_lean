import DerridaRetaux.Analysis.HalfLineIntegrability
import DerridaRetaux.Analysis.LatticeRiemannLimit
import DerridaRetaux.Analysis.LatticeWeakConvergence
import DerridaRetaux.Analysis.WeightedMomentBound
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace DerridaRetaux

noncomputable section

/-- A compactly supported nonnegative cutoff which agrees with `x^r` on
`[0,R]`. -/
def positiveMomentCutoff (r R : ℕ) (x : ℝ) : ℝ :=
  (max x 0) ^ r * compactMassCutoff R x

theorem continuous_positiveMomentCutoff (r R : ℕ) :
    Continuous (positiveMomentCutoff r R) := by
  exact (continuous_id.max continuous_const).pow r |>.mul
    (continuous_compactMassCutoff R)

theorem positiveMomentCutoff_hasCompactSupport (r R : ℕ) :
    HasCompactSupport (positiveMomentCutoff r R) := by
  exact (compactMassCutoff_hasCompactSupport R).mul_left

def positiveMomentCutoffBCF (r R : ℕ) : ℝ →ᵇ ℝ :=
  ofCompactSupport (positiveMomentCutoff r R)
    (continuous_positiveMomentCutoff r R)
    (positiveMomentCutoff_hasCompactSupport r R)

@[simp] theorem positiveMomentCutoffBCF_apply (r R : ℕ) (x : ℝ) :
    positiveMomentCutoffBCF r R x = positiveMomentCutoff r R x := rfl

theorem positiveMomentCutoff_nonneg (r R : ℕ) (x : ℝ) :
    0 ≤ positiveMomentCutoff r R x := by
  exact mul_nonneg (pow_nonneg (by positivity) r)
    (compactMassCutoff_nonneg R x)

theorem positiveMomentCutoff_le_power_of_nonneg
    (r R : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    positiveMomentCutoff r R x ≤ x ^ r := by
  rw [positiveMomentCutoff, max_eq_left hx]
  exact mul_le_of_le_one_right (pow_nonneg hx r)
    (compactMassCutoff_le_one R x)

theorem positiveMomentCutoff_eq_power
    (r R : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (R : ℝ)) :
    positiveMomentCutoff r R x = x ^ r := by
  rw [positiveMomentCutoff, max_eq_left hx.1,
    compactMassCutoff_eq_one_of_abs_le R x]
  · ring
  · rw [abs_of_nonneg hx.1]
    exact hx.2

/-- Local lattice convergence plus an eventual global bound on a normalized
moment proves integrability of the corresponding continuum moment. -/
theorem integrableOn_pow_mul_of_locallyUniform_and_momentBound
    (rho : ℕ → Seq) (scale : ℕ → ℕ) (u : ℝ → ℝ)
    (r : ℕ) (hr : r ≤ 3) (C : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (huneg : ∀ x : ℝ, x < 0 → u x = 0)
    (hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x)
    (hlocal : LocallyUniformLatticeDensity rho scale u)
    (hrho : ∀ n j : ℕ, 0 ≤ rho n j)
    (hmoment : ∀ n : ℕ,
      Summable (fun j : ℕ ↦ (j : ℝ) ^ r * rho n j))
    (hbound : ∀ᶠ n : ℕ in atTop,
      scaledDiscreteMoment (rho n) r (scale n) ≤ C) :
    IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ)) := by
  have hfcont : ContinuousOn (fun x : ℝ ↦ x ^ r * u x) (Ici (0 : ℝ)) :=
    continuousOn_pow r |>.mul hucont
  have hfnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ x ^ r * u x := by
    intro x hx
    exact mul_nonneg (pow_nonneg hx r) (hunonneg x hx)
  apply integrableOn_Ici_of_intervalIntegral_bounded
    (fun x : ℝ ↦ x ^ r * u x) C hfcont hfnonneg
  intro R
  let test : ℝ →ᵇ ℝ := positiveMomentCutoffBCF r R
  have htest := compact_lattice_sums_tendsto_of_locallyUniform
    rho scale u hscale hucont huneg hlocal test
      (positiveMomentCutoff_hasCompactSupport r R)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := by
    have hge := hscale.eventually_ge_atTop 1
    exact hge.mono fun _ hn ↦ by omega
  have hsumLe : ∀ᶠ n : ℕ in atTop,
      (∑' j : ℕ, ((scale n : ℝ) * rho n j) *
          test ((j : ℝ) / (scale n : ℝ))) ≤
        scaledDiscreteMoment (rho n) r (scale n) := by
    filter_upwards [hscalePos] with n hn
    have hNreal : (0 : ℝ) < (scale n : ℝ) := by exact_mod_cast hn
    have hright : Summable (fun j : ℕ ↦
        ((scale n : ℝ) / (scale n : ℝ) ^ r) *
          ((j : ℝ) ^ r * rho n j)) :=
      (hmoment n).mul_left ((scale n : ℝ) / (scale n : ℝ) ^ r)
    have hleft : Summable (fun j : ℕ ↦
        ((scale n : ℝ) * rho n j) *
          test ((j : ℝ) / (scale n : ℝ))) := by
      apply hright.of_nonneg_of_le
      · intro j
        exact mul_nonneg (mul_nonneg hNreal.le (hrho n j))
          (positiveMomentCutoff_nonneg r R _)
      · intro j
        rw [positiveMomentCutoffBCF_apply]
        have hcut := positiveMomentCutoff_le_power_of_nonneg r R
          (div_nonneg (Nat.cast_nonneg j) hNreal.le)
        calc
          (scale n : ℝ) * rho n j *
              positiveMomentCutoff r R ((j : ℝ) / (scale n : ℝ)) ≤
            (scale n : ℝ) * rho n j *
              ((j : ℝ) / (scale n : ℝ)) ^ r := by
                exact mul_le_mul_of_nonneg_left hcut
                  (mul_nonneg hNreal.le (hrho n j))
          _ = ((scale n : ℝ) / (scale n : ℝ) ^ r) *
              ((j : ℝ) ^ r * rho n j) := by
                field_simp
                ring
    rw [scaledDiscreteMoment, ← (hmoment n).tsum_mul_left]
    exact hleft.tsum_le_tsum (fun j ↦ by
      rw [positiveMomentCutoffBCF_apply]
      have hcut := positiveMomentCutoff_le_power_of_nonneg r R
        (div_nonneg (Nat.cast_nonneg j) hNreal.le)
      calc
        (scale n : ℝ) * rho n j *
            positiveMomentCutoff r R ((j : ℝ) / (scale n : ℝ)) ≤
          (scale n : ℝ) * rho n j *
            ((j : ℝ) / (scale n : ℝ)) ^ r := by
              exact mul_le_mul_of_nonneg_left hcut
                (mul_nonneg hNreal.le (hrho n j))
        _ = ((scale n : ℝ) / (scale n : ℝ) ^ r) *
            ((j : ℝ) ^ r * rho n j) := by field_simp; ring) hright
  have htestBound : ∫ x, u x * test x ∂volume ≤ C := by
    apply le_of_tendsto htest
    filter_upwards [hsumLe, hbound] with n hn hbn
    exact hn.trans hbn
  have hleftInt : IntegrableOn (fun x : ℝ ↦ x ^ r * u x)
      (Icc (0 : ℝ) (R : ℝ)) :=
    (hfcont.mono fun _ hx ↦ hx.1).integrableOn_compact isCompact_Icc
  have hrightInt : Integrable (fun x : ℝ ↦ u x * test x) volume := by
    let S : Set ℝ := Icc (0 : ℝ) ((R : ℝ) + 1)
    have hcont : ContinuousOn (fun x : ℝ ↦ u x * test x) S := by
      exact (hucont.mono fun _ hx ↦ hx.1).mul test.continuous.continuousOn
    have hint : IntegrableOn (fun x : ℝ ↦ u x * test x) S :=
      hcont.integrableOn_compact isCompact_Icc
    apply hint.integrable_of_forall_not_mem_eq_zero
    intro x hx
    by_cases hx0 : 0 ≤ x
    · have hxlarge : (R : ℝ) + 1 < x :=
        lt_of_not_ge (fun hle ↦ hx ⟨hx0, hle⟩)
      have hcut : compactMassCutoff R x = 0 :=
        compactMassCutoff_eq_zero_of_radius_le_abs R x (by
          rw [abs_of_nonneg hx0]
          exact hxlarge.le)
      simp only [test, positiveMomentCutoffBCF_apply, positiveMomentCutoff, hcut, mul_zero]
    · rw [huneg x (lt_of_not_ge hx0), zero_mul]
  have hmonoInt :
      (∫ x in Icc (0 : ℝ) (R : ℝ), x ^ r * u x) ≤
        ∫ x, u x * test x := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_mono (hleftInt.integrable_indicator measurableSet_Icc) hrightInt
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) (R : ℝ)
    · rw [indicator_of_mem hx]
      change x ^ r * u x ≤ u x * positiveMomentCutoffBCF r R x
      rw [positiveMomentCutoffBCF_apply, positiveMomentCutoff_eq_power r R hx]
      rw [mul_comm]
    · rw [indicator_of_not_mem hx]
      change 0 ≤ u x * test x
      by_cases hx0 : 0 ≤ x
      · exact mul_nonneg (hunonneg x hx0)
          (positiveMomentCutoff_nonneg r R x)
      · rw [huneg x (lt_of_not_ge hx0), zero_mul]
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg R)]
  rw [← integral_Icc_eq_integral_Ioc]
  exact hmonoInt.trans htestBound

end

end DerridaRetaux
