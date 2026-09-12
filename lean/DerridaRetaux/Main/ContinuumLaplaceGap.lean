import DerridaRetaux.Main.ContinuumLaplaceODE
import DerridaRetaux.Main.ContinuumMomentODE
import DerridaRetaux.Main.ContinuumRigidityMoments
import DerridaRetaux.Analysis.HalfLineDensityMeasure
import DerridaRetaux.Analysis.HalfLineLaplaceIntegrability
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux.FixedArity

noncomputable section

def subsequentialLaplaceGap
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t p : ℝ) : ℝ :=
  p - continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 +
    continuumLaplace (fun x ↦ gluedExhaustionLimit g t x) p

theorem subsequential_slice_continuous_for_gap
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun x ↦ gluedExhaustionLimit g t x) (Ici (0 : ℝ)) := by
  have hu := subsequentialDensity_continuousOn_positiveHalfStrip
    m data phi g hlim t ht
  let emb : ℝ → ℝ × ℝ := fun x ↦ (t, x)
  change ContinuousOn
    ((fun q : ℝ × ℝ ↦ gluedExhaustionLimit g q.1 q.2) ∘ emb)
      (Ici (0 : ℝ))
  exact hu.comp (by dsimp only [emb]; fun_prop) (fun x hx ↦ by
    dsimp only [emb]
    change t ≤ t ∧ (0 : ℝ) ≤ x
    exact ⟨le_rfl, hx⟩)

/-- The algebraic gap is exactly the integral of the nonnegative second-order
Laplace remainder. -/
theorem subsequentialLaplaceGap_eq_integrated
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {t p : ℝ} (ht : 0 < t) (hp : 0 ≤ p) :
    subsequentialLaplaceGap g t p =
      integratedLaplaceSecondGap
        (halfLineDensityMeasure (fun x ↦ gluedExhaustionLimit g t x)) p := by
  let u : ℝ → ℝ := fun x ↦ gluedExhaustionLimit g t x
  have hucont := subsequential_slice_continuous_for_gap m data phi g hlim ht
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hi : ∀ r : ℕ, r ≤ 3 →
      IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici 0) := by
    intro r hr
    simpa only [u] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht r hr
  have hzero : IntegrableOn u (Ici 0) := by
    simpa only [pow_zero, one_mul] using hi 0 (by norm_num)
  have hfirst : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici 0) := by
    simpa only [pow_one] using hi 1 (by norm_num)
  have hLap := integrableOn_exp_neg_mul (u) p hp hucont hunonneg hzero
  obtain ⟨C, hC, hb⟩ := subsequentialMoment_bounds m data phi g hphi hlim
  have hA1 : continuumMoment u 1 = 1 := by
    simpa only [u] using (hb t ht).2.1
  symm
  have hgap := integratedLaplaceSecondGap_eq_momentLaplaceGap
    u p hucont hunonneg hLap hzero hfirst hA1
  simpa only [subsequentialLaplaceGap, momentLaplaceGap, u] using hgap

/-- Positivity and the quadratic-moment upper bound for the continuum gap. -/
theorem subsequentialLaplaceGap_nonneg_and_le
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {t p : ℝ} (ht : 0 < t) (hp : 0 ≤ p) :
    0 ≤ subsequentialLaplaceGap g t p ∧
      subsequentialLaplaceGap g t p ≤ (p ^ 2 / 2) *
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 2 := by
  let u : ℝ → ℝ := fun x ↦ gluedExhaustionLimit g t x
  have hucont := subsequential_slice_continuous_for_gap m data phi g hlim ht
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hsecond : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0) := by
    simpa only [u] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht 2 (by norm_num)
  let μ := halfLineDensityMeasure u
  have hsecondμ : IntegrableOn (fun x : ℝ ↦ x ^ 2) (Ici 0) μ := by
    rw [integrableOn_halfLineDensityMeasure_iff u (fun x : ℝ ↦ x ^ 2)
      hucont hunonneg]
    exact hsecond
  have hbound := integratedLaplaceSecondGap_nonneg_and_le μ hp hsecondμ
  rw [← subsequentialLaplaceGap_eq_integrated m data phi g hphi hlim ht hp,
    positiveHalfLineMoment_halfLineDensityMeasure u 2 hucont hunonneg] at hbound
  simpa only [u] using hbound

/-- The gap is strictly positive for positive Laplace parameter. -/
theorem subsequentialLaplaceGap_pos
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    0 < subsequentialLaplaceGap g t p := by
  let u : ℝ → ℝ := fun x ↦ gluedExhaustionLimit g t x
  have hucont := subsequential_slice_continuous_for_gap m data phi g hlim ht
  have hunonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ u x := by
    intro x hx
    exact gluedExhaustionLimit_nonneg m data.law data.arity data.critical
      phi g hphi hlim ht hx
  have hi : ∀ r : ℕ, r ≤ 2 →
      IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici 0) := by
    intro r hr
    simpa only [u] using subsequentialMoment_integrable
      m data.law data.arity data.critical data.third data.notBinaryFixedPoint
        phi g hphi hlim t ht r (hr.trans (by norm_num))
  let μ := halfLineDensityMeasure u
  have hiμ : ∀ r : ℕ, r ≤ 2 →
      IntegrableOn (fun x : ℝ ↦ x ^ r) (Ici 0) μ := by
    intro r hr
    rw [integrableOn_halfLineDensityMeasure_iff u (fun x : ℝ ↦ x ^ r)
      hucont hunonneg]
    exact hi r hr
  obtain ⟨C, hC, hb⟩ := subsequentialMoment_bounds m data phi g hphi hlim
  have hA1μ : positiveHalfLineMoment 1 μ = 1 := by
    rw [positiveHalfLineMoment_halfLineDensityMeasure u 1 hucont hunonneg]
    simpa only [u] using (hb t ht).2.1
  have hpos := integratedLaplaceSecondGap_pos μ hp
    (by simpa only [pow_one] using hiμ 1 (by norm_num))
    (hiμ 2 (by norm_num)) hA1μ
  rwa [← subsequentialLaplaceGap_eq_integrated
    m data phi g hphi hlim ht hp.le] at hpos

/-- Exact source equation `eq:ZODE`. -/
theorem subsequentialLaplaceGap_hasDerivAt
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p t : ℝ) (hp : 0 ≤ p) (ht : 0 < t) :
    HasDerivAt (fun s ↦ subsequentialLaplaceGap g s p)
      (continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 0 *
          subsequentialLaplaceGap g t p +
        (1 / 2 : ℝ) * (subsequentialLaplaceGap g t p ^ 2 - p ^ 2)) t := by
  let A0 : ℝ → ℝ := fun s ↦
    continuumMoment (fun x ↦ gluedExhaustionLimit g s x) 0
  let beta : ℝ → ℝ := fun s ↦ gluedExhaustionLimit g s 0
  let U : ℝ → ℝ → ℝ := fun s q ↦
    continuumLaplace (fun x ↦ gluedExhaustionLimit g s x) q
  have hmom := (subsequentialMomentODE m data phi g hphi hlim).1 t ht
  have hlap := subsequentialLaplaceODE m data phi g hphi hlim p hp t ht
  have hlap' : HasDerivAt (fun s ↦ U s p)
      (p * U t p + (1 / 2 : ℝ) * U t p ^ 2 - beta t) t := by
    convert hlap using 1 <;> simp only [U, beta] <;> ring
  simpa only [subsequentialLaplaceGap, momentLaplaceGap, A0, beta, U] using
    hasDerivAt_momentLaplaceGap A0 beta U t p hmom hlap'

end

end DerridaRetaux.FixedArity
