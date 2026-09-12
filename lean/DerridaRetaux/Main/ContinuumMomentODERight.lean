import DerridaRetaux.Main.ContinuumMomentRightDerivativeTwo
import DerridaRetaux.Main.ContinuumMomentRightDerivativeThree
import DerridaRetaux.Analysis.RightDerivativeClosure
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

private theorem subsequential_slice_continuous
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    ContinuousOn (fun x ↦ gluedExhaustionLimit g t x) (Ici (0 : ℝ)) := by
  have hu := subsequentialDensity_continuousOn_positiveHalfStrip
    m data phi g hlim t ht
  let emb : ℝ → ℝ × ℝ := fun x ↦ (t, x)
  change ContinuousOn
    ((fun p : ℝ × ℝ ↦ gluedExhaustionLimit g p.1 p.2) ∘ emb)
      (Ici (0 : ℝ))
  exact hu.comp (by dsimp only [emb]; fun_prop) (fun x hx ↦ by
    dsimp only [emb]
    change t ≤ t ∧ (0 : ℝ) ≤ x
    exact ⟨le_rfl, hx⟩)

private theorem subsequential_slice_moment_integrable
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
    IntegrableOn
      (fun x : ℝ ↦ x ^ r * gluedExhaustionLimit g t x) (Ici 0) :=
  subsequentialMoment_integrable
    m data.law data.arity data.critical data.third data.notBinaryFixedPoint
      phi g hphi hlim t ht r hr

/-- The zeroth-moment ODE as a right derivative at positive time. -/
theorem subsequentialMoment_zero_hasDerivWithinAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt
      (fun s : ℝ ↦ continuumMoment
        (fun x ↦ gluedExhaustionLimit g s x) 0)
      (-gluedExhaustionLimit g t 0 + (1 / 2 : ℝ) *
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 ^ 2)
      (Ici t) t := by
  let A0 : ℝ → ℝ := fun s ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 0
  have hraw := subsequentialMoment_zero_hasDerivWithinAt_increment
    m data phi g hphi hlim t ht
  have hright := hasDerivWithinAt_Ici_of_increment A0 hraw
  have h0 : IntegrableOn (fun x ↦ gluedExhaustionLimit g t x) (Ici 0) := by
    simpa only [pow_zero, one_mul] using subsequential_slice_moment_integrable
      m data phi g hphi hlim t ht 0 (by norm_num)
  have hconv := integral_positiveSelfConvolution
    (fun x ↦ gluedExhaustionLimit g t x) h0
  apply hright.congr_deriv
  dsimp only [A0]
  rw [show continuumMoment
      (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g t x)) 0 =
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 ^ 2 by
    simpa only [continuumMoment, pow_zero, one_mul] using hconv]

/-- The second-moment ODE as a right derivative at positive time. -/
theorem subsequentialMoment_two_hasDerivWithinAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt
      (fun s : ℝ ↦ continuumMoment
        (fun x ↦ gluedExhaustionLimit g s x) 2)
      (continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 *
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 - 1)
      (Ici t) t := by
  let A : ℕ → ℝ := fun r ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) r
  have hraw := subsequentialMoment_two_hasDerivWithinAt_increment
    m data phi g hphi hlim t ht
  have hright := hasDerivWithinAt_Ici_of_increment
    (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 2) hraw
  have hucont := subsequential_slice_continuous m data phi g hlim t ht
  have hi : ∀ k : ℕ, k ≤ 2 → IntegrableOn
      (fun x : ℝ ↦ x ^ k * gluedExhaustionLimit g t x) (Ici 0) := by
    intro k hk
    exact subsequential_slice_moment_integrable
      m data phi g hphi hlim t ht k (hk.trans (by norm_num))
  have hconv := integral_pow_two_mul_positiveSelfConvolution
    (fun x ↦ gluedExhaustionLimit g t x) hucont
      (by simpa using hi 0 (by norm_num))
      (by simpa using hi 1 (by norm_num)) (hi 2 (by norm_num))
  obtain ⟨C, hC, hb⟩ := subsequentialMoment_bounds m data phi g hphi hlim
  have hA1 : A 1 = 1 := by simpa only [A] using (hb t ht).2.1
  apply hright.congr_deriv
  dsimp only [A] at hA1 ⊢
  rw [show continuumMoment
      (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g t x)) 2 =
        2 * continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 *
            continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 +
          2 * continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 1 ^ 2 by
    simpa only [continuumMoment] using hconv,
    hA1]
  ring

/-- The third-moment ODE as a right derivative at positive time. -/
theorem subsequentialMoment_three_hasDerivWithinAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop)
    (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt
      (fun s : ℝ ↦ continuumMoment
        (fun x ↦ gluedExhaustionLimit g s x) 3)
      (continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 *
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3)
      (Ici t) t := by
  let A : ℕ → ℝ := fun r ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g t x) r
  have hraw := subsequentialMoment_three_hasDerivWithinAt_increment
    m data phi g hphi hlim t ht
  have hright := hasDerivWithinAt_Ici_of_increment
    (fun s ↦ continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 3) hraw
  have hucont := subsequential_slice_continuous m data phi g hlim t ht
  have hi : ∀ k : ℕ, k ≤ 3 → IntegrableOn
      (fun x : ℝ ↦ x ^ k * gluedExhaustionLimit g t x) (Ici 0) := by
    intro k hk
    exact subsequential_slice_moment_integrable
      m data phi g hphi hlim t ht k hk
  have hconv := integral_pow_three_mul_positiveSelfConvolution
    (fun x ↦ gluedExhaustionLimit g t x) hucont
      (by simpa using hi 0 (by norm_num))
      (by simpa using hi 1 (by norm_num))
      (hi 2 (by norm_num)) (hi 3 (by norm_num))
  obtain ⟨C, hC, hb⟩ := subsequentialMoment_bounds m data phi g hphi hlim
  have hA1 : A 1 = 1 := by simpa only [A] using (hb t ht).2.1
  apply hright.congr_deriv
  dsimp only [A] at hA1 ⊢
  rw [show continuumMoment
      (positiveSelfConvolution (fun x ↦ gluedExhaustionLimit g t x)) 3 =
        2 * continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 *
            continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3 +
          6 * continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 1 *
            continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 by
    simpa only [continuumMoment] using hconv,
    hA1]
  ring

end

end DerridaRetaux.FixedArity
