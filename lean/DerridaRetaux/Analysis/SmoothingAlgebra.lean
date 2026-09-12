import DerridaRetaux.Model.DensityRecursion
import Mathlib.Tactic

/-!
# Coefficient algebra for the smoothing recursion

This file contains only the finite coefficient algebra behind source equations
`eq:rhoshort`, `eq:Bevolution`, and `eq:R`.  No norm estimate or nonlocal hypothesis is
used here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- Convolution is additive in its left input, coefficient by coefficient. -/
theorem conv_seq_add_left (a b e : Seq) :
    conv (a + b) e = conv a e + conv b e := by
  funext n
  simp only [conv_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Convolution is additive in its right input, coefficient by coefficient. -/
theorem conv_seq_add_right (a b e : Seq) :
    conv a (b + e) = conv a b + conv a e := by
  rw [conv_comm, conv_seq_add_left]
  simp only [conv_comm a b, conv_comm a e]

/-- A scalar in the left input factors out of convolution. -/
theorem conv_seq_smul_left (c : ℝ) (a b : Seq) :
    conv (c • a) b = c • conv a b := by
  funext n
  simp only [conv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A scalar in the right input factors out of convolution. -/
theorem conv_seq_smul_right (c : ℝ) (a b : Seq) :
    conv a (c • b) = c • conv a b := by
  rw [conv_comm, conv_seq_smul_left]
  rw [conv_comm b a]

@[simp]
theorem conv_zero_seq_left (a : Seq) : conv (0 : Seq) a = 0 := by
  simpa only [Pi.zero_apply] using conv_zero_left a

@[simp]
theorem conv_zero_seq_right (a : Seq) : conv a (0 : Seq) = 0 := by
  simpa only [Pi.zero_apply] using conv_zero_right a

@[simp]
theorem convPow_two_eq (a : Seq) : convPow 2 a = conv a a := by
  rw [show 2 = 1 + 1 by omega, convPow_succ, convPow_one]

@[simp]
theorem convPow_three_eq (a : Seq) : convPow 3 a = conv (conv a a) a := by
  rw [show 3 = 2 + 1 by omega, convPow_succ, convPow_two_eq]

@[simp]
theorem convPow_four_eq (a : Seq) : convPow 4 a = conv (conv a a) (conv a a) := by
  rw [show 4 = 2 + 2 by omega, convPow_add, convPow_two_eq]

/-- First coefficient identity displayed immediately before source equation
`eq:Bevolution`. -/
theorem conv_shiftLeft_self (rho : Seq) :
    conv (shiftLeft rho) (shiftLeft rho) =
      shiftLeft (shiftLeft (conv rho rho)) -
        (2 * rho 0) • shiftLeft (shiftLeft rho) := by
  funext n
  have hleft := conv_succ_left rho (shiftLeft rho) n
  have hright := conv_succ_right rho rho (n + 1)
  simp only [shiftLeft_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hleft hright ⊢
  rw [show n + 1 + 1 = n + 2 by omega] at hleft hright ⊢
  linarith

/-- Second coefficient identity displayed immediately before source equation
`eq:Bevolution`. -/
theorem conv_shiftLeft_conv_self (rho : Seq) :
    conv (shiftLeft rho) (conv rho rho) =
      shiftLeft (convPow 3 rho) - rho 0 • shiftLeft (conv rho rho) := by
  funext n
  have h := conv_succ_left rho (conv rho rho) n
  have hpow : conv rho (conv rho rho) = convPow 3 rho := by
    rw [convPow_three_eq, conv_comm rho (conv rho rho)]
  rw [hpow] at h
  simp only [shiftLeft_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  linarith

/-- The short one-step density update `c S rho + d (rho * rho) + E`. -/
def shortDensityStep (c d : ℝ) (rho E : Seq) : Seq :=
  c • shiftLeft rho + d • conv rho rho + E

/-- The complete six-term remainder in source equation `eq:R`. -/
def smoothingRemainder (c d : ℝ) (rho E : Seq) : Seq :=
  (-2 * c ^ 2 * rho 0) • shiftLeft (shiftLeft rho) +
    (2 * c * d) • shiftLeft (convPow 3 rho) +
    (-2 * c * d * rho 0) • shiftLeft (conv rho rho) +
    d ^ 2 • convPow 4 rho +
    2 • conv (c • shiftLeft rho + d • conv rho rho) E +
    conv E E

/-- Pure algebraic form of `eq:Bevolution`: squaring the short density update produces
the transported quadratic term and exactly the six terms of `eq:R`. -/
theorem conv_shortDensityStep_self
    (c d : ℝ) (rho E : Seq) :
    conv (shortDensityStep c d rho E) (shortDensityStep c d rho E) =
      c ^ 2 • shiftLeft (shiftLeft (conv rho rho)) +
        smoothingRemainder c d rho E := by
  rw [shortDensityStep]
  rw [conv_seq_add_left, conv_seq_add_right]
  rw [conv_seq_add_left, conv_seq_add_right]
  rw [conv_seq_add_left, conv_seq_add_right]
  rw [conv_seq_add_right E (c • shiftLeft rho + d • conv rho rho) E]
  rw [conv_seq_add_right E (c • shiftLeft rho) (d • conv rho rho)]
  rw [conv_comm E (c • shiftLeft rho), conv_comm E (d • conv rho rho)]
  simp_rw [conv_seq_smul_left, conv_seq_smul_right]
  rw [conv_comm (conv rho rho) (shiftLeft rho)]
  rw [smoothingRemainder]
  rw [conv_seq_add_left]
  simp_rw [conv_seq_smul_left]
  rw [conv_shiftLeft_self, conv_shiftLeft_conv_self]
  rw [convPow_four_eq]
  funext n
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Source notation `beta_s = rho_s(0)`. -/
def densityBeta (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : ℝ :=
  positiveTiltedDensity m (orbit m p₀ s) 0

/-- Source notation `B_s = rho_s * rho_s`. -/
def densityB (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  conv (positiveTiltedDensity m (orbit m p₀ s))
    (positiveTiltedDensity m (orbit m p₀ s))

/-- Source notation `d_s = d_{2,s}`. -/
def densityD (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : ℝ :=
  densityCoeff m 2 (orbit m p₀ s)

/-- Source notation `E_s = sum_{r=3}^m d_{r,s} T^(r-2) rho_s^(*r)`.
The interval is empty, definitionally and mathematically, at `m = 2`. -/
def densityE (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  fun j : ℕ ↦
    ∑ r ∈ Finset.Ico 3 (m + 1),
      densityCoeff m r (orbit m p₀ s) *
        shiftRightPow (r - 2)
          (convPow r (positiveTiltedDensity m (orbit m p₀ s))) j

/-- Offset-indexed presentation of `E_s`, used to split the `r = 2` term from the
coefficientwise density recursion. -/
theorem densityE_eq_offset
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m) (s : ℕ) :
    densityE m p₀ s = fun j : ℕ ↦
      ∑ t ∈ Finset.range (m - 2),
        densityCoeff m ((t + 1) + 2) (orbit m p₀ s) *
          shiftRightPow (t + 1)
            (convPow ((t + 1) + 2)
              (positiveTiltedDensity m (orbit m p₀ s))) j := by
  funext j
  rw [densityE, Finset.sum_Ico_eq_sum_range]
  have hlength : m + 1 - 3 = m - 2 := by omega
  rw [hlength]
  apply Finset.sum_congr rfl
  intro t _
  simp [Nat.add_comm]

/-- Source equation `eq:rhoshort`, before any analytic estimate. -/
theorem positiveTiltedDensity_orbit_succ_short
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (s : ℕ) :
    positiveTiltedDensity m (orbit m p₀ (s + 1)) =
      shortDensityStep
        (transportCoeff m (orbit m p₀ s)) (densityD m p₀ s)
        (positiveTiltedDensity m (orbit m p₀ s)) (densityE m p₀ s) := by
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  rw [orbit_succ, drStep_eq_drStepProb]
  rw [positiveTiltedDensity_drStepProb_offset m (orbit m p₀ s) hm hscrit]
  rw [densityE_eq_offset m p₀ hm s]
  funext j
  simp only [shortDensityStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul, densityD,
    densityB]
  have hlength : m - 1 = (m - 2) + 1 := by omega
  rw [hlength, Finset.sum_range_succ']
  simp only [Nat.zero_add, shiftRightPow_zero, convPow_two_eq]
  ring

/-- Source equation `eq:R`, with all six terms retained. -/
def densityR (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  smoothingRemainder
    (transportCoeff m (orbit m p₀ s)) (densityD m p₀ s)
    (positiveTiltedDensity m (orbit m p₀ s)) (densityE m p₀ s)

/-- Pointwise source-shaped expansion of the complete remainder `R_s`. -/
theorem densityR_apply (m : ℕ) (p₀ : ProbabilityMass) (s j : ℕ) :
    densityR m p₀ s j =
      -2 * transportCoeff m (orbit m p₀ s) ^ 2 * densityBeta m p₀ s *
          shiftLeft (shiftLeft (positiveTiltedDensity m (orbit m p₀ s))) j +
        2 * transportCoeff m (orbit m p₀ s) * densityD m p₀ s *
          shiftLeft (convPow 3 (positiveTiltedDensity m (orbit m p₀ s))) j -
        2 * transportCoeff m (orbit m p₀ s) * densityD m p₀ s *
          densityBeta m p₀ s * shiftLeft (densityB m p₀ s) j +
        densityD m p₀ s ^ 2 *
          convPow 4 (positiveTiltedDensity m (orbit m p₀ s)) j +
        2 * conv
          (transportCoeff m (orbit m p₀ s) •
              shiftLeft (positiveTiltedDensity m (orbit m p₀ s)) +
            densityD m p₀ s • densityB m p₀ s)
          (densityE m p₀ s) j +
        conv (densityE m p₀ s) (densityE m p₀ s) j := by
  simp only [densityR, smoothingRemainder, densityBeta, densityB, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

/-- Source equation `eq:Bevolution`, derived from `eq:rhoshort` and the two exact
coefficient identities above. -/
theorem densityB_orbit_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (s : ℕ) :
    densityB m p₀ (s + 1) =
      transportCoeff m (orbit m p₀ s) ^ 2 •
          shiftLeft (shiftLeft (densityB m p₀ s)) +
        densityR m p₀ s := by
  rw [densityB, positiveTiltedDensity_orbit_succ_short m p₀ hm hcrit s]
  simpa only [densityB, densityD, densityR] using
    conv_shortDensityStep_self
      (transportCoeff m (orbit m p₀ s)) (densityD m p₀ s)
      (positiveTiltedDensity m (orbit m p₀ s)) (densityE m p₀ s)

/-- The higher-order source term is exactly zero at binary arity. -/
@[simp]
theorem densityE_two (p₀ : ProbabilityMass) (s : ℕ) :
    densityE 2 p₀ s = 0 := by
  funext j
  simp [densityE]

/-- Binary specialization of `eq:rhoshort`; there is no hidden higher-order term. -/
theorem positiveTiltedDensity_orbit_succ_short_two
    (p₀ : ProbabilityMass) (hcrit : Critical 2 p₀) (s : ℕ) :
    positiveTiltedDensity 2 (orbit 2 p₀ (s + 1)) =
      transportCoeff 2 (orbit 2 p₀ s) •
          shiftLeft (positiveTiltedDensity 2 (orbit 2 p₀ s)) +
        densityD 2 p₀ s • densityB 2 p₀ s := by
  rw [positiveTiltedDensity_orbit_succ_short 2 p₀ (by norm_num) hcrit s]
  simp [shortDensityStep, densityB]

/-- At `m = 2`, the final two `E_s` terms of `eq:R` vanish exactly. -/
theorem densityR_two (p₀ : ProbabilityMass) (s : ℕ) :
    densityR 2 p₀ s =
      (-2 * transportCoeff 2 (orbit 2 p₀ s) ^ 2 * densityBeta 2 p₀ s) •
          shiftLeft (shiftLeft (positiveTiltedDensity 2 (orbit 2 p₀ s))) +
        (2 * transportCoeff 2 (orbit 2 p₀ s) * densityD 2 p₀ s) •
          shiftLeft (convPow 3 (positiveTiltedDensity 2 (orbit 2 p₀ s))) +
        (-2 * transportCoeff 2 (orbit 2 p₀ s) * densityD 2 p₀ s *
            densityBeta 2 p₀ s) • shiftLeft (densityB 2 p₀ s) +
        densityD 2 p₀ s ^ 2 •
          convPow 4 (positiveTiltedDensity 2 (orbit 2 p₀ s)) := by
  rw [densityR, densityE_two]
  simp [smoothingRemainder, densityBeta, densityB, conv_zero_right, conv_zero_left]

/-- Fully expanded binary form of `eq:Bevolution`. -/
theorem densityB_orbit_succ_two
    (p₀ : ProbabilityMass) (hcrit : Critical 2 p₀) (s : ℕ) :
    densityB 2 p₀ (s + 1) =
      transportCoeff 2 (orbit 2 p₀ s) ^ 2 •
          shiftLeft (shiftLeft (densityB 2 p₀ s)) +
        ((-2 * transportCoeff 2 (orbit 2 p₀ s) ^ 2 * densityBeta 2 p₀ s) •
            shiftLeft (shiftLeft (positiveTiltedDensity 2 (orbit 2 p₀ s))) +
          (2 * transportCoeff 2 (orbit 2 p₀ s) * densityD 2 p₀ s) •
            shiftLeft (convPow 3 (positiveTiltedDensity 2 (orbit 2 p₀ s))) +
          (-2 * transportCoeff 2 (orbit 2 p₀ s) * densityD 2 p₀ s *
              densityBeta 2 p₀ s) • shiftLeft (densityB 2 p₀ s) +
          densityD 2 p₀ s ^ 2 •
            convPow 4 (positiveTiltedDensity 2 (orbit 2 p₀ s))) := by
  rw [densityB_orbit_succ 2 p₀ (by norm_num) hcrit s, densityR_two]

end

end DerridaRetaux
