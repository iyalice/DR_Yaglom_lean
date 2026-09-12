import DerridaRetaux.Analysis.LocalACClosure
import DerridaRetaux.Analysis.QuadraticConvolutionLimit
import Mathlib.Tactic

/-!
# The time-integrated weak equation

This file records the exact scalar weak equation used after the mild limit.
The three terms of the weak generator are kept separate: the boundary trace,
the spatial transport term, and the quadratic double integral.  The main
closure theorem is deliberately conditional on the pointwise weak derivative;
deriving that derivative from the continuum mild equation requires the
space-time Fubini and translation arguments belonging to the mild-limit step.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace DerridaRetaux

noncomputable section

/-- Pair a test function with a density on the nonnegative half-line. -/
def halfLineTestPairing (phi v : ℝ → ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ), phi x * v x

/-- The quadratic term in the weak equation, displayed as the literal double
integral from the source. -/
def weakQuadraticPairing (phi v : ℝ → ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ),
    ∫ y in Ici (0 : ℝ), phi (x + y) * v x * v y

/-- The observable tested against a time-dependent density. -/
def weakObservable (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (t : ℝ) : ℝ :=
  halfLineTestPairing phi (u t)

/-- The right-hand side of the weak Derrida--Retaux equation.  In particular,
the transport boundary trace has the source-prescribed sign. -/
def weakEquationRhs (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (t : ℝ) : ℝ :=
  -phi 0 * u t 0 - halfLineTestPairing (deriv phi) (u t) +
    (1 / 2 : ℝ) * weakQuadraticPairing phi (u t)

/-- A global representative of a compactly supported `C¹` test function on
the half-line.  Only its values on `Ici 0` enter the weak equation. -/
def IsCompactC1HalfLineTest (phi : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 phi ∧ HasCompactSupport phi

/-- Time-integrated weak identity on every ordered subinterval of `K`. -/
def HasTimeIntegratedWeakEquationOn
    (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∀ a : ℝ, a ∈ K → ∀ b : ℝ, b ∈ K → a ≤ b →
    weakObservable u phi b - weakObservable u phi a =
      ∫ s in a..b, weakEquationRhs u phi s

/-- The weak equation on `K` means the integrated identity for every compactly
supported `C¹` test function. -/
def HasWeakEquationOn (u : ℝ → ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∀ phi : ℝ → ℝ, IsCompactC1HalfLineTest phi →
    HasTimeIntegratedWeakEquationOn u phi K

/-- Continuity of the three displayed weak terms gives continuity of the full
weak generator. -/
theorem continuousOn_weakEquationRhs
    (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (K : Set ℝ)
    (hboundary : ContinuousOn (fun t ↦ u t 0) K)
    (htransport : ContinuousOn
      (fun t ↦ halfLineTestPairing (deriv phi) (u t)) K)
    (hquadratic : ContinuousOn
      (fun t ↦ weakQuadraticPairing phi (u t)) K) :
    ContinuousOn (weakEquationRhs u phi) K := by
  exact (((continuousOn_const.neg.mul hboundary).sub htransport).add
    (continuousOn_const.mul hquadratic))

/-- A continuous pointwise weak derivative integrates to the exact weak
identity on every subinterval of a compact positive-time window.  This is the
analytic closure needed once the mild-equation translation/Fubini argument has
supplied `hderiv`. -/
theorem hasTimeIntegratedWeakEquationOn_of_pointwise_derivative
    (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (eta T : ℝ)
    (hobservable : ContinuousOn (weakObservable u phi) (Icc eta T))
    (hrhs : ContinuousOn (weakEquationRhs u phi) (Icc eta T))
    (hderiv : ∀ t ∈ Ioo eta T,
      HasDerivAt (weakObservable u phi) (weakEquationRhs u phi t) t) :
    HasTimeIntegratedWeakEquationOn u phi (Icc eta T) := by
  intro a ha b hb hab
  have hsubset : Icc a b ⊆ Icc eta T := by
    intro t ht
    exact ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
  have hobsab : ContinuousOn (weakObservable u phi) (Icc a b) :=
    hobservable.mono hsubset
  have hrhsab : ContinuousOn (weakEquationRhs u phi) (Icc a b) :=
    hrhs.mono hsubset
  have hderivab : ∀ t ∈ Ioo a b,
      HasDerivAt (weakObservable u phi) (weakEquationRhs u phi t) t := by
    intro t ht
    apply hderiv t
    exact ⟨ha.1.trans_lt ht.1, ht.2.trans_le hb.2⟩
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hobsab hderivab (hrhsab.intervalIntegrable_of_Icc hab)

/-- Termwise continuity plus the pointwise weak derivative implies the
time-integrated identity, with the boundary trace exposed in
`weakEquationRhs`. -/
theorem hasTimeIntegratedWeakEquationOn_of_weak_terms
    (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (eta T : ℝ)
    (hobservable : ContinuousOn (weakObservable u phi) (Icc eta T))
    (hboundary : ContinuousOn (fun t ↦ u t 0) (Icc eta T))
    (htransport : ContinuousOn
      (fun t ↦ halfLineTestPairing (deriv phi) (u t)) (Icc eta T))
    (hquadratic : ContinuousOn
      (fun t ↦ weakQuadraticPairing phi (u t)) (Icc eta T))
    (hderiv : ∀ t ∈ Ioo eta T,
      HasDerivAt (weakObservable u phi) (weakEquationRhs u phi t) t) :
    HasTimeIntegratedWeakEquationOn u phi (Icc eta T) := by
  apply hasTimeIntegratedWeakEquationOn_of_pointwise_derivative
    u phi eta T hobservable
    (continuousOn_weakEquationRhs
      u phi (Icc eta T) hboundary htransport hquadratic)
    hderiv

/-- All compactly supported `C¹` tests satisfy the integrated equation once
their observables and weak generators are continuous and have the displayed
pointwise derivative on the interior. -/
theorem hasWeakEquationOn_of_pointwise_weak_derivatives
    (u : ℝ → ℝ → ℝ) (eta T : ℝ)
    (hobservable : ∀ phi : ℝ → ℝ, IsCompactC1HalfLineTest phi →
      ContinuousOn (weakObservable u phi) (Icc eta T))
    (hrhs : ∀ phi : ℝ → ℝ, IsCompactC1HalfLineTest phi →
      ContinuousOn (weakEquationRhs u phi) (Icc eta T))
    (hderiv : ∀ phi : ℝ → ℝ, IsCompactC1HalfLineTest phi →
      ∀ t ∈ Ioo eta T,
        HasDerivAt (weakObservable u phi) (weakEquationRhs u phi t) t) :
    HasWeakEquationOn u (Icc eta T) := by
  intro phi hphi
  exact hasTimeIntegratedWeakEquationOn_of_pointwise_derivative
    u phi eta T (hobservable phi hphi) (hrhs phi hphi) (hderiv phi hphi)

/-- The integrated weak equation yields the `HasIntegralDerivativeOn`
interface consumed by the local absolute-continuity closure theorem U47. -/
theorem hasIntegralDerivativeOn_weakObservable_of_integratedWeakEquation
    (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (eta T : ℝ)
    (hrhs : ContinuousOn (weakEquationRhs u phi) (Icc eta T))
    (hweak : HasTimeIntegratedWeakEquationOn u phi (Icc eta T)) :
    HasIntegralDerivativeOn
      (weakObservable u phi) (weakEquationRhs u phi) (Icc eta T) := by
  refine ⟨hrhs.integrableOn_Icc, ?_⟩
  intro a ha b hb hab
  have hsubset : Ioc a b ⊆ Icc eta T := by
    intro t ht
    exact ⟨ha.1.trans ht.1.le, ht.2.trans hb.2⟩
  have hrestrict :
      (∫ s in Ioc a b, weakEquationRhs u phi s ∂(volume.restrict (Icc eta T))) =
        ∫ s in a..b, weakEquationRhs u phi s := by
    rw [Measure.restrict_restrict_of_subset hsubset,
      intervalIntegral.integral_of_le hab]
  rw [hrestrict]
  exact hweak a ha b hb hab

/-- Conversely, the U47 integral-derivative interface recovers the literal
interval-integral weak identity. -/
theorem hasTimeIntegratedWeakEquationOn_of_hasIntegralDerivativeOn
    (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (eta T : ℝ)
    (hderiv : HasIntegralDerivativeOn
      (weakObservable u phi) (weakEquationRhs u phi) (Icc eta T)) :
    HasTimeIntegratedWeakEquationOn u phi (Icc eta T) := by
  intro a ha b hb hab
  have hsubset : Ioc a b ⊆ Icc eta T := by
    intro t ht
    exact ⟨ha.1.trans ht.1.le, ht.2.trans hb.2⟩
  have hrestrict :
      (∫ s in Ioc a b, weakEquationRhs u phi s ∂(volume.restrict (Icc eta T))) =
        ∫ s in a..b, weakEquationRhs u phi s := by
    rw [Measure.restrict_restrict_of_subset hsubset,
      intervalIntegral.integral_of_le hab]
  rw [← hrestrict]
  exact hderiv.2 a ha b hb hab

/-- With a continuous weak generator, the literal time-integrated equation is
equivalent to the integral-derivative interface used in U47. -/
theorem hasTimeIntegratedWeakEquationOn_iff_hasIntegralDerivativeOn
    (u : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (eta T : ℝ)
    (hrhs : ContinuousOn (weakEquationRhs u phi) (Icc eta T)) :
    HasTimeIntegratedWeakEquationOn u phi (Icc eta T) ↔
      HasIntegralDerivativeOn
        (weakObservable u phi) (weakEquationRhs u phi) (Icc eta T) := by
  constructor
  · exact hasIntegralDerivativeOn_weakObservable_of_integratedWeakEquation
      u phi eta T hrhs
  · exact hasTimeIntegratedWeakEquationOn_of_hasIntegralDerivativeOn
      u phi eta T

end

end DerridaRetaux
