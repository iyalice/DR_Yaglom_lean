import DerridaRetaux.Analysis.PositiveConvolutionThirdMoment
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- Pointwise binomial expansion of a weighted positive convolution. -/
theorem pow_mul_positiveSelfConvolution_eq_sum
    (u : ℝ → ℝ) (r : ℕ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    {x : ℝ} (hx : 0 ≤ x) :
    x ^ r * positiveSelfConvolution u x =
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        positiveConvolutionMomentTerm u k (r - k) x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp [positiveSelfConvolution, positiveConvolutionMomentTerm]
  have huI : ContinuousOn u (Icc (0 : ℝ) x) :=
    hucont.mono fun _ hy ↦ hy.1
  have hrev : ContinuousOn (fun y : ℝ ↦ u (x - y)) (Icc 0 x) :=
    huI.comp (continuous_const.sub continuous_id).continuousOn
      (fun y hy ↦ ⟨sub_nonneg.mpr hy.2, by linarith [hy.1]⟩)
  have hsub : ContinuousOn (fun y : ℝ ↦ x - y) (Icc 0 x) :=
    (continuous_const.sub continuous_id).continuousOn
  have hinterval : ∀ k ∈ Finset.range (r + 1), IntervalIntegrable
      (fun y : ℝ ↦ (r.choose k : ℝ) *
        ((y ^ k * u y) * ((x - y) ^ (r - k) * u (x - y))))
      volume 0 x := by
    intro k hk
    exact ((continuousOn_const.mul ((((continuousOn_id.pow k).mul huI).mul
      ((hsub.pow (r - k)).mul hrev)))).intervalIntegrable_of_Icc hxpos.le)
  calc
    x ^ r * positiveSelfConvolution u x =
        ∫ y in (0 : ℝ)..x, x ^ r * (u y * u (x - y)) := by
      simp only [positiveSelfConvolution, intervalIntegral.integral_const_mul]
    _ = ∫ y in (0 : ℝ)..x,
        ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
          ((y ^ k * u y) * ((x - y) ^ (r - k) * u (x - y))) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hpow : x ^ r = ∑ k ∈ Finset.range (r + 1),
          y ^ k * (x - y) ^ (r - k) * (r.choose k : ℝ) := by
        conv_lhs => rw [show x = y + (x - y) by ring]
        exact add_pow y (x - y) r
      rw [hpow]
      change (∑ k ∈ Finset.range (r + 1),
        y ^ k * (x - y) ^ (r - k) * (r.choose k : ℝ)) *
          (u y * u (x - y)) = _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ Finset.range (r + 1),
        ∫ y in (0 : ℝ)..x, (r.choose k : ℝ) *
          ((y ^ k * u y) * ((x - y) ^ (r - k) * u (x - y))) := by
      exact intervalIntegral.integral_finset_sum hinterval
    _ = ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        positiveConvolutionMomentTerm u k (r - k) x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- Finite input moments through order `r` imply integrability of the
`r`-th moment of the positive self-convolution. -/
theorem integrableOn_pow_mul_positiveSelfConvolution
    (u : ℝ → ℝ) (r : ℕ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hmom : ∀ k : ℕ, k ≤ r →
      IntegrableOn (fun x : ℝ ↦ x ^ k * u x) (Ici 0)) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ r * positiveSelfConvolution u x) (Ici 0) := by
  let term : ℕ → ℝ → ℝ := fun k x ↦
    (r.choose k : ℝ) * positiveConvolutionMomentTerm u k (r - k) x
  have hterm : ∀ k ∈ Finset.range (r + 1),
      IntegrableOn (term k) (Ici (0 : ℝ)) := by
    intro k hk
    have hkr : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact (integrableOn_positiveConvolutionMomentTerm u k (r - k)
      (hmom k hkr) (hmom (r - k) (Nat.sub_le r k))).const_mul _
  have hsum : IntegrableOn
      (fun x : ℝ ↦ ∑ k ∈ Finset.range (r + 1), term k x)
      (Ici (0 : ℝ)) :=
    integrable_finset_sum (Finset.range (r + 1)) hterm
  refine hsum.congr_fun ?_ measurableSet_Ici
  intro x hx
  symm
  simpa only [term] using
    pow_mul_positiveSelfConvolution_eq_sum u r hucont hx

/-- The full binomial formula for every finite half-line convolution moment. -/
theorem continuumMoment_positiveSelfConvolution
    (u : ℝ → ℝ) (r : ℕ)
    (hucont : ContinuousOn u (Ici (0 : ℝ)))
    (hmom : ∀ k : ℕ, k ≤ r →
      IntegrableOn (fun x : ℝ ↦ x ^ k * u x) (Ici 0)) :
    continuumMoment (positiveSelfConvolution u) r =
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        continuumMoment u k * continuumMoment u (r - k) := by
  let term : ℕ → ℝ → ℝ := fun k x ↦
    (r.choose k : ℝ) * positiveConvolutionMomentTerm u k (r - k) x
  have hterm : ∀ k ∈ Finset.range (r + 1),
      IntegrableOn (term k) (Ici (0 : ℝ)) := by
    intro k hk
    have hkr : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact (integrableOn_positiveConvolutionMomentTerm u k (r - k)
      (hmom k hkr) (hmom (r - k) (Nat.sub_le r k))).const_mul _
  unfold continuumMoment
  rw [setIntegral_congr_fun measurableSet_Ici
    (fun x hx ↦ pow_mul_positiveSelfConvolution_eq_sum u r hucont hx)]
  rw [integral_finset_sum (Finset.range (r + 1)) hterm]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [integral_const_mul,
    integral_positiveConvolutionMomentTerm u k (r - k)
      (hmom k hkr) (hmom (r - k) (Nat.sub_le r k))]
  simp only [continuumMoment]
  ring

end

end DerridaRetaux
