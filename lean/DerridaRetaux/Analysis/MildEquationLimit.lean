import DerridaRetaux.Analysis.TerminalReadoutLimit
import DerridaRetaux.Analysis.InitialSegmentLimit
import DerridaRetaux.Analysis.QuadraticSegmentLimit
import DerridaRetaux.Analysis.HigherSegmentFloorLimit

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- The exact discrete Duhamel decomposition passes to the glued continuum
limit at every strictly positive spatial point. -/
theorem gluedExhaustionLimit_mild_pos_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / profileScale s)
    (hSup : ∀ s : ℕ,
      WeightedSupThreeLE (profileScale s)
        (positiveTiltedDensity m (orbit m p₀ s))
        (B / profileScale s ^ 2))
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t₀ t x : ℝ) (R : ℕ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 < x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    gluedExhaustionLimit g t x =
      gluedExhaustionLimit g t₀ (x + t - t₀) +
        ∫ s in t₀..t, (1 / 2 : ℝ) * positiveSelfConvolution
          (fun y ↦ gluedExhaustionLimit g s y) (x + t - s) := by
  let a : ℕ → ℕ := fun n ↦ gridIndex (phi n) t₀
  let b : ℕ → ℕ := fun n ↦ gridIndex (phi n) t
  let j : ℕ → ℕ := fun n ↦ gridIndex (phi n) x
  let initial : ℕ → ℝ := fun n ↦ (phi n : ℝ) ^ 2 *
    densityInitialSegment m p₀ (a n) (b n) (j n)
  let quadratic : ℕ → ℝ := fun n ↦ (phi n : ℝ) ^ 2 *
    densityQuadraticSegment m p₀ (a n) (b n) (j n)
  let higher : ℕ → ℝ := fun n ↦ (phi n : ℝ) ^ 2 *
    densityHigherSegment m p₀ (a n) (b n) (j n)
  let terminal : ℕ → ℝ := fun n ↦ (phi n : ℝ) ^ 2 *
    positiveTiltedDensity m (orbit m p₀ (b n)) (j n)
  have htpos : 0 < t := ht₀.trans_le ht
  have hterminal : Tendsto terminal atTop
      (nhds (gluedExhaustionLimit g t x)) := by
    simpa only [terminal, b, j] using scaled_terminalDensity_tendsto
      m p₀ phi g t x R htpos hx.le (by linarith [hR]) hphi hlim
  have hinitial : Tendsto initial atTop
      (nhds (gluedExhaustionLimit g t₀ (x + t - t₀))) := by
    simpa only [initial, a, b, j] using
      scaled_densityInitialSegment_tendsto_of_H1a
        m p₀ hm hcrit hthird hnonconstant hExcess phi g t₀ t x R
          ht₀ ht hx.le hR hphi hlim
  have hquadratic : Tendsto quadratic atTop
      (nhds (∫ s in t₀..t, (1 / 2 : ℝ) * positiveSelfConvolution
        (fun y ↦ gluedExhaustionLimit g s y) (x + t - s))) := by
    simpa only [quadratic, a, b, j] using
      scaled_densityQuadraticSegment_tendsto_of_H1a
        m p₀ hm hcrit hthird hnonconstant hExcess phi g t₀ t x R
          ht₀ ht hx hR hphi hlim
  have hhigher : Tendsto higher atTop (nhds 0) := by
    simpa only [higher, a, b, j] using
      scaled_densityHigherSegment_floor_tendsto_zero
        m p₀ hm hcrit hthird A B hA hB hL1 hSup phi hphi t₀ t x ht₀ ht
  have hright : Tendsto (fun n ↦ initial n + quadratic n + higher n)
      atTop (nhds
        (gluedExhaustionLimit g t₀ (x + t - t₀) +
          ∫ s in t₀..t, (1 / 2 : ℝ) * positiveSelfConvolution
            (fun y ↦ gluedExhaustionLimit g s y) (x + t - s))) := by
    simpa only [add_zero] using (hinitial.add hquadratic).add hhigher
  have hsplit : ∀ n, terminal n = initial n + quadratic n + higher n := by
    intro n
    have hab : a n ≤ b n := gridIndex_mono_of_nonneg ht₀.le ht (phi n)
    have hs := congrFun
      (positiveTiltedDensity_eq_initial_add_quadratic_add_higher
        m p₀ hm hcrit hab) (j n)
    dsimp only [terminal, initial, quadratic, higher]
    rw [hs]
    simp only [Pi.add_apply]
    ring
  have hterminal' : Tendsto terminal atTop (nhds
      (gluedExhaustionLimit g t₀ (x + t - t₀) +
        ∫ s in t₀..t, (1 / 2 : ℝ) * positiveSelfConvolution
          (fun y ↦ gluedExhaustionLimit g s y) (x + t - s))) := by
    apply hright.congr'
    exact Eventually.of_forall fun n ↦ (hsplit n).symm
  exact tendsto_nhds_unique hterminal hterminal'

end

end DerridaRetaux
