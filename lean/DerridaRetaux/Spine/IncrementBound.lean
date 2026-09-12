import DerridaRetaux.Spine.Allocation
import Mathlib.Tactic

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-!
# Arithmetic bound for the cubic-spine increment

The definitions below copy the numerator and denominator of source
`eq:incformula`.  The main theorem isolates the deterministic last step: the
size-biased Cauchy--Schwarz estimate implies the quotient is at most four.
-/

def spineIncrementNumerator (m : ℕ) (x b g : ℝ) : ℝ :=
  x ^ (m - 1) * (g + cubicChi m * b) +
    3 * ((m : ℝ) - 1) * b ^ 2 +
      6 * cubicChi m * b + 3 * cubicChi m ^ 2 / ((m : ℝ) - 1)

def spineIncrementDenominator (m : ℕ) (b g : ℝ) : ℝ :=
  g + (3 + cubicChi m) * b + 2 * cubicChi m / ((m : ℝ) - 1)

def spineIncrementRatio (m : ℕ) (x b g : ℝ) : ℝ :=
  spineIncrementNumerator m x b g / spineIncrementDenominator m b g

theorem spineIncrementNumerator_nonneg
    (m : ℕ) (hm : 2 ≤ m) (x b g : ℝ)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (hg : 0 ≤ g) :
    0 ≤ spineIncrementNumerator m x b g := by
  have hchi := cubicChi_nonneg m hm
  have hden : 0 < (m : ℝ) - 1 := by
    have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  unfold spineIncrementNumerator
  positivity

theorem spineIncrementDenominator_nonneg
    (m : ℕ) (hm : 2 ≤ m) (b g : ℝ) (hb : 0 ≤ b) (hg : 0 ≤ g) :
    0 ≤ spineIncrementDenominator m b g := by
  have hchi := cubicChi_nonneg m hm
  have hden : 0 < (m : ℝ) - 1 := by
    have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  unfold spineIncrementDenominator
  positivity

theorem spineIncrementNumerator_le_four_denominator
    (m : ℕ) (hm : 2 ≤ m) (x b g : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hcauchy : b ^ 2 ≤ (g + b) / ((m : ℝ) - 1)) :
    spineIncrementNumerator m x b g ≤
      4 * spineIncrementDenominator m b g := by
  have hchi0 := cubicChi_nonneg m hm
  have hchi1 := cubicChi_le_one m hm
  have hden : 0 < (m : ℝ) - 1 := by
    have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hxpow0 : 0 ≤ x ^ (m - 1) := pow_nonneg hx0 _
  have hxpow1 : x ^ (m - 1) ≤ 1 := pow_le_one₀ hx0 hx1
  have hgb : 0 ≤ g + cubicChi m * b :=
    add_nonneg hg (mul_nonneg hchi0 hb)
  have hfirst :
      x ^ (m - 1) * (g + cubicChi m * b) ≤ g + cubicChi m * b := by
    nlinarith [mul_le_mul_of_nonneg_right hxpow1 hgb]
  have hcauchyScaled :
      3 * ((m : ℝ) - 1) * b ^ 2 ≤ 3 * (g + b) := by
    have hmul :
        (3 * ((m : ℝ) - 1)) * b ^ 2 ≤
          (3 * ((m : ℝ) - 1)) * ((g + b) / ((m : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hcauchy (mul_nonneg (by norm_num) hden.le)
    calc
      3 * ((m : ℝ) - 1) * b ^ 2 =
          (3 * ((m : ℝ) - 1)) * b ^ 2 := by ring
      _ ≤ (3 * ((m : ℝ) - 1)) * ((g + b) / ((m : ℝ) - 1)) := hmul
      _ = 3 * (g + b) := by
        field_simp
        ring
  have hchiSq :
      3 * cubicChi m ^ 2 / ((m : ℝ) - 1) ≤
        8 * cubicChi m / ((m : ℝ) - 1) := by
    apply (div_le_div_iff₀ hden hden).2
    nlinarith [sq_nonneg (cubicChi m),
      mul_nonneg hchi0 (sub_nonneg.mpr hchi1)]
  have hcoeff :
      (3 + 7 * cubicChi m) * b ≤ (12 + 4 * cubicChi m) * b := by
    apply mul_le_mul_of_nonneg_right _ hb
    linarith
  unfold spineIncrementNumerator spineIncrementDenominator
  calc
    x ^ (m - 1) * (g + cubicChi m * b) +
          3 * ((m : ℝ) - 1) * b ^ 2 + 6 * cubicChi m * b +
            3 * cubicChi m ^ 2 / ((m : ℝ) - 1) ≤
        4 * g + (3 + 7 * cubicChi m) * b +
          3 * cubicChi m ^ 2 / ((m : ℝ) - 1) := by
      nlinarith
    _ ≤ 4 * g + (12 + 4 * cubicChi m) * b +
          8 * cubicChi m / ((m : ℝ) - 1) := by
      nlinarith
    _ = 4 * (g + (3 + cubicChi m) * b +
          2 * cubicChi m / ((m : ℝ) - 1)) := by ring

theorem spineIncrementRatio_le_four
    (m : ℕ) (hm : 2 ≤ m) (x b g : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hcauchy : b ^ 2 ≤ (g + b) / ((m : ℝ) - 1)) :
    spineIncrementRatio m x b g ≤ 4 := by
  have hN := spineIncrementNumerator_nonneg m hm x b g hx0 hb hg
  have hD := spineIncrementDenominator_nonneg m hm b g hb hg
  have hND := spineIncrementNumerator_le_four_denominator
    m hm x b g hx0 hx1 hb hg hcauchy
  by_cases hzero : spineIncrementDenominator m b g = 0
  · have hNzero : spineIncrementNumerator m x b g = 0 := by
      apply le_antisymm
      · simpa [hzero] using hND
      · exact hN
    simp [spineIncrementRatio, hzero, hNzero]
  · have hDpos : 0 < spineIncrementDenominator m b g := lt_of_le_of_ne hD (Ne.symm hzero)
    rw [spineIncrementRatio, div_le_iff₀ hDpos]
    simpa [mul_comm] using hND

end

end DerridaRetaux
