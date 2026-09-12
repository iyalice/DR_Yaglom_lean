import DerridaRetaux.Analysis.MildEquationLimit
import DerridaRetaux.Analysis.MildIntegralContinuity

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace DerridaRetaux

noncomputable section

/-- Continuity of the glued limit and of the convolution integral extends the
mild equation from positive spatial points to the boundary `x = 0`. -/
theorem gluedExhaustionLimit_mild_zero_of_H1a
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
    (t₀ t : ℝ) (R : ℕ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t)
    (hR : t + 2 ≤ (R : ℝ))
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    gluedExhaustionLimit g t 0 =
      gluedExhaustionLimit g t₀ (t - t₀) +
        ∫ s in t₀..t, (1 / 2 : ℝ) * positiveSelfConvolution
          (fun y ↦ gluedExhaustionLimit g s y) (t - s) := by
  let u : ℝ → ℝ → ℝ := gluedExhaustionLimit g
  let lhs : ℝ → ℝ := fun x ↦ u t x
  let rhs : ℝ → ℝ := fun x ↦
    u t₀ (x + t - t₀) +
      ∫ s in t₀..t, (1 / 2 : ℝ) *
        positiveSelfConvolution (u s) (x + t - s)
  let box : Set (ℝ × ℝ) :=
    Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ)
  have heta : 0 < t₀ / 2 := half_pos ht₀
  have hetaT : t₀ / 2 ≤ t + 1 := by linarith
  have huBox : ContinuousOn (Function.uncurry u) box := by
    simpa only [u, box] using continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m p₀) phi g hlim
        (t₀ / 2) (t + 1) (R : ℝ) heta hetaT (by linarith [hR])
  have hlhs : ContinuousOn lhs (Icc (0 : ℝ) 1) := by
    apply huBox.comp (continuous_const.prodMk continuous_id).continuousOn
    intro x hx
    exact ⟨⟨by linarith, by linarith⟩,
      hx.1, hx.2.trans (by linarith [hR])⟩
  have hinitial : ContinuousOn (fun x ↦ u t₀ (x + t - t₀))
      (Icc (0 : ℝ) 1) := by
    apply huBox.comp
      (continuous_const.prodMk
        (continuous_id.add continuous_const |>.sub continuous_const)).continuousOn
    intro x hx
    change (t₀, x + t - t₀) ∈ Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ)
    constructor
    · exact ⟨by linarith, by linarith⟩
    · constructor
      · change 0 ≤ x + t - t₀
        linarith [hx.1, ht]
      · change x + t - t₀ ≤ (R : ℝ)
        linarith [hx.2, hR]
  have huSmall : ContinuousOn (Function.uncurry u)
      (Icc t₀ t ×ˢ Icc (0 : ℝ) (R : ℝ)) := by
    exact huBox.mono fun p hp ↦
      ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  have hintegral : ContinuousOn
      (fun x ↦ ∫ s in t₀..t, (1 / 2 : ℝ) *
        positiveSelfConvolution (u s) (x + t - s))
      (Icc (0 : ℝ) 1) :=
    continuousOn_shiftedConvolutionTimeIntegral u t₀ t (R : ℝ)
      ht₀ ht (by linarith [hR]) huSmall
  have hrhs : ContinuousOn rhs (Icc (0 : ℝ) 1) := by
    exact hinitial.add hintegral
  have heqPos : EqOn lhs rhs (Ioc (0 : ℝ) 1) := by
    intro x hx
    exact gluedExhaustionLimit_mild_pos_of_H1a
      m p₀ hm hcrit hthird hnonconstant hExcess
      A B hA hB hL1 hSup phi g t₀ t x R ht₀ ht hx.1
        (by linarith [hx.2, hR]) hphi hlim
  have hclosure : Icc (0 : ℝ) 1 ⊆ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
  have heq := heqPos.of_subset_closure hlhs hrhs Ioc_subset_Icc_self hclosure
  simpa only [lhs, rhs, u, zero_add] using
    heq ⟨(le_rfl : (0 : ℝ) ≤ 0), zero_le_one⟩

end

end DerridaRetaux
