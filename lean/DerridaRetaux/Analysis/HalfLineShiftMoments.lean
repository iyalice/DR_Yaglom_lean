import DerridaRetaux.Analysis.PositiveConvolutionLaplace
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- A translated half-line moment. -/
def shiftedHalfLineMoment (u : ℝ → ℝ) (r : ℕ) (h : ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ), x ^ r * u (x + h)

/-- The part of a moment remaining to the right of a moving cutoff. -/
def halfLineTailMoment (u : ℝ → ℝ) (r : ℕ) (h : ℝ) : ℝ :=
  continuumMoment u r - ∫ x in (0 : ℝ)..h, x ^ r * u x

/-- Translation of Lebesgue measure converts a shifted half-line moment into
an integral over the translated half-line. -/
theorem shiftedHalfLineMoment_eq_integral_Ici
    (u : ℝ → ℝ) (r : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    shiftedHalfLineMoment u r h =
      ∫ y in Ici h, (y - h) ^ r * u y := by
  rw [shiftedHalfLineMoment, ← integral_indicator measurableSet_Ici,
    ← integral_indicator measurableSet_Ici]
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun y : ℝ ↦ (Ici h).indicator (fun z ↦ (z - h) ^ r * u z) y) h]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Set.indicator]
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [if_pos hx, if_pos]
    · ring
    · have hx0 : 0 ≤ x := hx
      exact show h ≤ x + h by linarith
  · rw [if_neg hx, if_neg]
    intro hxh
    have hx0 : h ≤ x + h := hxh
    have hxnonneg : 0 ≤ x := by linarith
    exact hx hxnonneg
/-- Splitting `[0,∞)` at a nonnegative cutoff. -/
theorem integral_Ici_eq_interval_add_Ici
    (f : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hf : IntegrableOn f (Ici (0 : ℝ))) :
    (∫ x in Ici (0 : ℝ), f x) =
      (∫ x in (0 : ℝ)..h, f x) + ∫ x in Ici h, f x := by
  have hsub : Ico (0 : ℝ) h ⊆ Ici (0 : ℝ) := fun _ hx ↦ hx.1
  have hdisj : Disjoint (Ico (0 : ℝ) h) (Ici h) := by
    rw [Set.disjoint_left]
    intro x hx hxh
    exact (not_le_of_gt hx.2) hxh
  have hunion : Ico (0 : ℝ) h ∪ Ici h = Ici (0 : ℝ) :=
    Ico_union_Ici_eq_Ici hh
  have hsplit := setIntegral_union hdisj measurableSet_Ici
    (hf.mono_set hsub) (hf.mono_set fun _ hx ↦ hh.trans hx)
  rw [hunion] at hsplit
  have hinter : (∫ x in (0 : ℝ)..h, f x) = ∫ x in Ico (0 : ℝ) h, f x := by
    rw [intervalIntegral.integral_of_le hh,
      integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
  rw [hinter]
  exact hsplit

theorem integral_Ici_eq_halfLineTailMoment
    (u : ℝ → ℝ) (r : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (hr : IntegrableOn (fun x : ℝ ↦ x ^ r * u x) (Ici 0)) :
    (∫ y in Ici h, y ^ r * u y) = halfLineTailMoment u r h := by
  have hsplit := integral_Ici_eq_interval_add_Ici
    (fun x : ℝ ↦ x ^ r * u x) hh hr
  unfold halfLineTailMoment continuumMoment
  linarith

/-- Exact translated mass identity. -/
theorem shiftedHalfLineMoment_zero
    (u : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (h0 : IntegrableOn u (Ici 0)) :
    shiftedHalfLineMoment u 0 h = halfLineTailMoment u 0 h := by
  rw [shiftedHalfLineMoment_eq_integral_Ici u 0 hh]
  simpa only [pow_zero, one_mul] using
    integral_Ici_eq_halfLineTailMoment u 0 hh (by simpa using h0)

/-- Exact translated second-moment identity. -/
theorem shiftedHalfLineMoment_two
    (u : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (h0 : IntegrableOn u (Ici 0))
    (h1 : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici 0))
    (h2 : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0)) :
    shiftedHalfLineMoment u 2 h =
      halfLineTailMoment u 2 h - 2 * h * halfLineTailMoment u 1 h +
        h ^ 2 * halfLineTailMoment u 0 h := by
  rw [shiftedHalfLineMoment_eq_integral_Ici u 2 hh]
  have h0I : IntegrableOn u (Ici h) := h0.mono_set fun _ hx ↦ hh.trans hx
  have h1I : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici h) :=
    h1.mono_set fun _ hx ↦ hh.trans hx
  have h2I : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici h) :=
    h2.mono_set fun _ hx ↦ hh.trans hx
  have hpoint : ∀ y : ℝ,
      (y - h) ^ 2 * u y = y ^ 2 * u y -
        (2 * h) * (y * u y) + h ^ 2 * u y := by
    intro y
    ring
  rw [setIntegral_congr_fun measurableSet_Ici (fun y _ ↦ hpoint y)]
  have hs1 :
      (∫ y in Ici h, y ^ 2 * u y - (2 * h) * (y * u y)) =
        (∫ y in Ici h, y ^ 2 * u y) -
          (∫ y in Ici h, (2 * h) * (y * u y)) := by
    simpa only [Pi.sub_apply] using integral_sub h2I (h1I.const_mul (2 * h))
  have hs2 :
      (∫ y in Ici h,
        (y ^ 2 * u y - (2 * h) * (y * u y)) + h ^ 2 * u y) =
        (∫ y in Ici h, y ^ 2 * u y - (2 * h) * (y * u y)) +
          (∫ y in Ici h, h ^ 2 * u y) := by
    simpa only [Pi.add_apply] using
      integral_add (h2I.sub (h1I.const_mul (2 * h))) (h0I.const_mul (h ^ 2))
  rw [hs2, hs1, integral_const_mul, integral_const_mul]
  have ht1 : (∫ y in Ici h, y * u y) = halfLineTailMoment u 1 h := by
    simpa only [pow_one] using
      integral_Ici_eq_halfLineTailMoment u 1 hh (by simpa using h1)
  have ht0 : (∫ y in Ici h, u y) = halfLineTailMoment u 0 h := by
    simpa only [pow_zero, one_mul] using
      integral_Ici_eq_halfLineTailMoment u 0 hh (by simpa using h0)
  rw [integral_Ici_eq_halfLineTailMoment u 2 hh h2, ht1, ht0]
/-- Exact translated third-moment identity. -/
theorem shiftedHalfLineMoment_three
    (u : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (h0 : IntegrableOn u (Ici 0))
    (h1 : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici 0))
    (h2 : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici 0))
    (h3 : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u x) (Ici 0)) :
    shiftedHalfLineMoment u 3 h =
      halfLineTailMoment u 3 h - 3 * h * halfLineTailMoment u 2 h +
        3 * h ^ 2 * halfLineTailMoment u 1 h -
          h ^ 3 * halfLineTailMoment u 0 h := by
  rw [shiftedHalfLineMoment_eq_integral_Ici u 3 hh]
  have h0I : IntegrableOn u (Ici h) := h0.mono_set fun _ hx ↦ hh.trans hx
  have h1I : IntegrableOn (fun x : ℝ ↦ x * u x) (Ici h) :=
    h1.mono_set fun _ hx ↦ hh.trans hx
  have h2I : IntegrableOn (fun x : ℝ ↦ x ^ 2 * u x) (Ici h) :=
    h2.mono_set fun _ hx ↦ hh.trans hx
  have h3I : IntegrableOn (fun x : ℝ ↦ x ^ 3 * u x) (Ici h) :=
    h3.mono_set fun _ hx ↦ hh.trans hx
  have hpoint : ∀ y : ℝ,
      (y - h) ^ 3 * u y =
        ((y ^ 3 * u y - (3 * h) * (y ^ 2 * u y)) +
          (3 * h ^ 2) * (y * u y)) - h ^ 3 * u y := by
    intro y
    ring
  rw [setIntegral_congr_fun measurableSet_Ici (fun y _ ↦ hpoint y)]
  have hs1 :
      (∫ y in Ici h, y ^ 3 * u y - (3 * h) * (y ^ 2 * u y)) =
        (∫ y in Ici h, y ^ 3 * u y) -
          (∫ y in Ici h, (3 * h) * (y ^ 2 * u y)) := by
    simpa only [Pi.sub_apply] using integral_sub h3I (h2I.const_mul (3 * h))
  have hs2 :
      (∫ y in Ici h,
        (y ^ 3 * u y - (3 * h) * (y ^ 2 * u y)) +
          (3 * h ^ 2) * (y * u y)) =
        (∫ y in Ici h, y ^ 3 * u y - (3 * h) * (y ^ 2 * u y)) +
          (∫ y in Ici h, (3 * h ^ 2) * (y * u y)) := by
    simpa only [Pi.add_apply] using
      integral_add (h3I.sub (h2I.const_mul (3 * h)))
        (h1I.const_mul (3 * h ^ 2))
  have hs3 :
      (∫ y in Ici h,
        ((y ^ 3 * u y - (3 * h) * (y ^ 2 * u y)) +
          (3 * h ^ 2) * (y * u y)) - h ^ 3 * u y) =
        (∫ y in Ici h,
          (y ^ 3 * u y - (3 * h) * (y ^ 2 * u y)) +
            (3 * h ^ 2) * (y * u y)) -
          (∫ y in Ici h, h ^ 3 * u y) := by
    simpa only [Pi.sub_apply] using
      integral_sub ((h3I.sub (h2I.const_mul (3 * h))).add
        (h1I.const_mul (3 * h ^ 2))) (h0I.const_mul (h ^ 3))
  rw [hs3, hs2, hs1, integral_const_mul, integral_const_mul,
    integral_const_mul]
  have ht1 : (∫ y in Ici h, y * u y) = halfLineTailMoment u 1 h := by
    simpa only [pow_one] using
      integral_Ici_eq_halfLineTailMoment u 1 hh (by simpa using h1)
  have ht0 : (∫ y in Ici h, u y) = halfLineTailMoment u 0 h := by
    simpa only [pow_zero, one_mul] using
      integral_Ici_eq_halfLineTailMoment u 0 hh (by simpa using h0)
  rw [integral_Ici_eq_halfLineTailMoment u 3 hh h3,
    integral_Ici_eq_halfLineTailMoment u 2 hh h2, ht1, ht0]

end

end DerridaRetaux
