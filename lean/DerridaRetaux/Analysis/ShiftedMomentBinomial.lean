import DerridaRetaux.Analysis.HalfLineShiftMoments
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- Binomial expansion of an arbitrary translated half-line moment. -/
theorem shiftedHalfLineMoment_eq_sum
    (v : ℝ → ℝ) (r : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (hmom : ∀ k : ℕ, k ≤ r →
      IntegrableOn (fun x : ℝ ↦ x ^ k * v x) (Ici 0)) :
    shiftedHalfLineMoment v r h =
      ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) *
        (-h) ^ (r - k) * halfLineTailMoment v k h := by
  rw [shiftedHalfLineMoment_eq_integral_Ici v r hh]
  have hterm : ∀ k ∈ Finset.range (r + 1), IntegrableOn
      (fun y : ℝ ↦ (r.choose k : ℝ) * (-h) ^ (r - k) *
        (y ^ k * v y)) (Ici h) := by
    intro k hk
    have hkr : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact ((hmom k hkr).mono_set (fun _ hy ↦ hh.trans hy)).const_mul _
  rw [setIntegral_congr_fun measurableSet_Ici]
  · rw [integral_finset_sum (Finset.range (r + 1)) hterm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul,
      integral_Ici_eq_halfLineTailMoment v k hh
        (hmom k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))]
  · intro y hy
    have hpow : (y - h) ^ r =
        ∑ k ∈ Finset.range (r + 1),
          y ^ k * (-h) ^ (r - k) * (r.choose k : ℝ) := by
      rw [sub_eq_add_neg, add_pow]
    change (y - h) ^ r * v y =
      ∑ k ∈ Finset.range (r + 1),
        (r.choose k : ℝ) * (-h) ^ (r - k) * (y ^ k * v y)
    rw [hpow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring

end

end DerridaRetaux
