import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The third-order exponential remainder

This file isolates the pointwise estimate used in the small/large spatial split of the
Laplace-transform argument.  For nonnegative `p` and `x`, the source remainder is

`exp (-p * x) - 1 + p * x - (p * x)^2 / 2 + (p * x)^3 / 6`.

Both global upper bounds are proved: the fourth-order bound is useful on the small spatial
region, while the third-order bound requires no fourth moment and is useful on the tail.
-/

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-- The third-order remainder of `y ↦ exp (-y)` after the cubic term is moved to the
remainder side. -/
def expThirdRemainderCore (y : ℝ) : ℝ :=
  Real.exp (-y) - 1 + y - y ^ 2 / 2 + y ^ 3 / 6

/-- The source remainder `R_p(x)`, written through the dimensionless variable `p * x`. -/
def expThirdRemainder (p x : ℝ) : ℝ :=
  expThirdRemainderCore (p * x)

/-- `R_p(x)` expanded exactly in the source variables. -/
theorem expThirdRemainder_eq (p x : ℝ) :
    expThirdRemainder p x =
      Real.exp (-(p * x)) - 1 + p * x - p ^ 2 * x ^ 2 / 2 + p ^ 3 * x ^ 3 / 6 := by
  simp [expThirdRemainder, expThirdRemainderCore, mul_pow]

@[simp]
theorem expThirdRemainderCore_zero : expThirdRemainderCore 0 = 0 := by
  simp [expThirdRemainderCore]

@[simp]
theorem expThirdRemainder_zero_left (x : ℝ) : expThirdRemainder 0 x = 0 := by
  simp [expThirdRemainder]

@[simp]
theorem expThirdRemainder_zero_right (p : ℝ) : expThirdRemainder p 0 = 0 := by
  simp [expThirdRemainder]

theorem continuous_expThirdRemainderCore : Continuous expThirdRemainderCore := by
  unfold expThirdRemainderCore
  fun_prop

theorem continuous_expThirdRemainder (p : ℝ) : Continuous (expThirdRemainder p) := by
  unfold expThirdRemainder expThirdRemainderCore
  fun_prop

private def expFirstGap (y : ℝ) : ℝ := 1 - Real.exp (-y)

private def expSecondGap (y : ℝ) : ℝ := Real.exp (-y) - 1 + y

private def expThirdGap (y : ℝ) : ℝ := 1 - y + y ^ 2 / 2 - Real.exp (-y)

private def expFourthGap (y : ℝ) : ℝ := y ^ 4 / 24 - expThirdRemainderCore y

private theorem hasDerivAt_exp_neg (y : ℝ) :
    HasDerivAt (fun z : ℝ ↦ Real.exp (-z)) (-Real.exp (-y)) y := by
  convert (Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y) using 1
  all_goals ring

private theorem hasDerivAt_expSecondGap (y : ℝ) :
    HasDerivAt expSecondGap (expFirstGap y) y := by
  convert ((hasDerivAt_exp_neg y).sub_const 1).add (hasDerivAt_id y) using 1
  all_goals simp [expFirstGap, expSecondGap]
  all_goals ring

private theorem hasDerivAt_expThirdGap (y : ℝ) :
    HasDerivAt expThirdGap (expSecondGap y) y := by
  convert (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
    (((hasDerivAt_id y).pow 2).div_const 2)).sub (hasDerivAt_exp_neg y) using 1
  all_goals simp [expSecondGap, expThirdGap]
  all_goals ring

private theorem hasDerivAt_expThirdRemainderCore (y : ℝ) :
    HasDerivAt expThirdRemainderCore (expThirdGap y) y := by
  convert (((((hasDerivAt_exp_neg y).sub_const 1).add (hasDerivAt_id y)).sub
    (((hasDerivAt_id y).pow 2).div_const 2)).add
    (((hasDerivAt_id y).pow 3).div_const 6)) using 1
  all_goals simp [expThirdGap, expThirdRemainderCore]
  all_goals ring

private theorem hasDerivAt_expFourthGap (y : ℝ) :
    HasDerivAt expFourthGap (expThirdRemainderCore y) y := by
  convert ((((hasDerivAt_id y).pow 4).div_const 24).sub
    (hasDerivAt_expThirdRemainderCore y)) using 1
  all_goals simp [expThirdGap, expFourthGap, expThirdRemainderCore]
  all_goals ring

private theorem nonneg_of_deriv_nonneg_on_Ici
    (f f' : ℝ → ℝ)
    (hzero : f 0 = 0)
    (hderiv : ∀ y, HasDerivAt f (f' y) y)
    (hderiv_nonneg : ∀ y, 0 ≤ y → 0 ≤ f' y)
    {y : ℝ} (hy : 0 ≤ y) : 0 ≤ f y := by
  have hcontinuous : ContinuousOn f (Set.Ici 0) := by
    intro z hz
    exact (hderiv z).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcontinuous
    · intro z hz
      exact (hderiv z).hasDerivWithinAt
    · intro z hz
      apply hderiv_nonneg z
      rw [interior_Ici, Set.mem_Ioi] at hz
      exact hz.le
  have hle : f 0 ≤ f y := hmono (by simp) (by simpa) hy
  simpa [hzero] using hle

private theorem expFirstGap_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ expFirstGap y := by
  rw [expFirstGap]
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)]

private theorem expSecondGap_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ expSecondGap y := by
  apply nonneg_of_deriv_nonneg_on_Ici expSecondGap expFirstGap
  · simp [expSecondGap]
  · exact hasDerivAt_expSecondGap
  · intro z hz
    exact expFirstGap_nonneg hz
  · exact hy

private theorem expThirdGap_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ expThirdGap y := by
  apply nonneg_of_deriv_nonneg_on_Ici expThirdGap expSecondGap
  · simp [expThirdGap]
  · exact hasDerivAt_expThirdGap
  · intro z hz
    exact expSecondGap_nonneg hz
  · exact hy

/-- The source remainder is nonnegative on the nonnegative half-line. -/
theorem expThirdRemainderCore_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ expThirdRemainderCore y := by
  apply nonneg_of_deriv_nonneg_on_Ici expThirdRemainderCore expThirdGap
  · exact expThirdRemainderCore_zero
  · exact hasDerivAt_expThirdRemainderCore
  · intro z hz
    exact expThirdGap_nonneg hz
  · exact hy

/-- The global third-order upper bound; this is the estimate used on the large spatial
region because it only asks for a third moment. -/
theorem expThirdRemainderCore_le_cubic {y : ℝ} (hy : 0 ≤ y) :
    expThirdRemainderCore y ≤ y ^ 3 / 6 := by
  have hgap := expThirdGap_nonneg hy
  dsimp [expThirdGap, expThirdRemainderCore] at hgap ⊢
  linarith

/-- The global fourth-order upper bound used on the small spatial region. -/
theorem expThirdRemainderCore_le_quartic {y : ℝ} (hy : 0 ≤ y) :
    expThirdRemainderCore y ≤ y ^ 4 / 24 := by
  have hgap : 0 ≤ expFourthGap y := by
    apply nonneg_of_deriv_nonneg_on_Ici expFourthGap expThirdRemainderCore
    · simp [expFourthGap]
    · exact hasDerivAt_expFourthGap
    · intro z hz
      exact expThirdRemainderCore_nonneg hz
    · exact hy
  simpa [expFourthGap] using hgap

/-- The exact pointwise estimate quoted in the source. -/
theorem expThirdRemainderCore_le_min {y : ℝ} (hy : 0 ≤ y) :
    expThirdRemainderCore y ≤ min (y ^ 4 / 24) (y ^ 3 / 6) :=
  le_min (expThirdRemainderCore_le_quartic hy)
    (expThirdRemainderCore_le_cubic hy)

/-- Nonnegativity of `R_p(x)` under the source hypotheses. -/
theorem expThirdRemainder_nonneg {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) :
    0 ≤ expThirdRemainder p x := by
  exact expThirdRemainderCore_nonneg (mul_nonneg hp hx)

/-- The fourth-order bound for `R_p(x)`, in the factorized source variables. -/
theorem expThirdRemainder_le_quartic {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) :
    expThirdRemainder p x ≤ p ^ 4 * x ^ 4 / 24 := by
  simpa [expThirdRemainder, mul_pow] using
    expThirdRemainderCore_le_quartic (mul_nonneg hp hx)

/-- The third-order bound for `R_p(x)`, in the factorized source variables. -/
theorem expThirdRemainder_le_cubic {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) :
    expThirdRemainder p x ≤ p ^ 3 * x ^ 3 / 6 := by
  simpa [expThirdRemainder, mul_pow] using
    expThirdRemainderCore_le_cubic (mul_nonneg hp hx)

/-- The source's minimum of the fourth- and third-order upper bounds. -/
theorem expThirdRemainder_le_min {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) :
    expThirdRemainder p x ≤
      min (p ^ 4 * x ^ 4 / 24) (p ^ 3 * x ^ 3 / 6) :=
  le_min (expThirdRemainder_le_quartic hp hx)
    (expThirdRemainder_le_cubic hp hx)

/-- The two-sided pointwise remainder estimate in the notation of the source. -/
theorem expThirdRemainder_bounds {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) :
    0 ≤ expThirdRemainder p x ∧
      expThirdRemainder p x ≤ min (p ^ 4 * x ^ 4 / 24) (p ^ 3 * x ^ 3 / 6) := by
  exact ⟨expThirdRemainder_nonneg hp hx, expThirdRemainder_le_min hp hx⟩

/-- On `x ≤ δ`, the fourth-order estimate trades one power of `x` for the cutoff `δ`.
This is the pointwise small-region estimate used before integration against `x^3 u(t,x)`. -/
theorem expThirdRemainder_le_smallCutoff {p x δ : ℝ}
    (hp : 0 ≤ p) (hx : 0 ≤ x) (hxδ : x ≤ δ) :
    expThirdRemainder p x ≤ (p ^ 4 * δ / 24) * x ^ 3 := by
  calc
    expThirdRemainder p x ≤ p ^ 4 * x ^ 4 / 24 :=
      expThirdRemainder_le_quartic hp hx
    _ ≤ (p ^ 4 * δ / 24) * x ^ 3 := by
      have hp4 : 0 ≤ p ^ 4 := pow_nonneg hp 4
      have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx 3
      nlinarith [mul_le_mul_of_nonneg_right hxδ hx3]

/-- Tail-ready form of the third-order estimate.  It has no cutoff factor and hence needs
only an `x^3` tail estimate after integration. -/
theorem expThirdRemainder_le_largeTail {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) :
    expThirdRemainder p x ≤ (p ^ 3 / 6) * x ^ 3 := by
  simpa [div_mul_eq_mul_div, mul_assoc] using expThirdRemainder_le_cubic hp hx

end

end DerridaRetaux
