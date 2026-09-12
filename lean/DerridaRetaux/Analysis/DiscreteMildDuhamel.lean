import DerridaRetaux.Analysis.TruncatedTelescope
import Mathlib.Tactic

/-!
# The exact discrete Duhamel identity behind the mild limit

This file isolates the finite algebraic part of the passage from the density
recursion `eq:rhor` to the continuum mild equation.  It does not assume any
limit, Riemann-sum statement, or asymptotic estimate: the source is the literal
finite sum over convolution orders `2 ≤ r ≤ m`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- The complete nonlinear source in the source-indexed density recursion
`eq:rhor`.  Keeping this definition separate makes the subsequent Duhamel
identity visibly exhaustive in the convolution order. -/
def densityRhoSource
    (m : ℕ) (p₀ : ProbabilityMass) (s : ℕ) : Seq :=
  fun j : ℕ ↦
    ∑ r ∈ Finset.Ico 2 (m + 1),
      densityCoeff m r (orbit m p₀ s) *
        shiftRightPow (r - 2)
          (convPow r (positiveTiltedDensity m (orbit m p₀ s))) j

/-- The exact one-step orbit recurrence with the full `r=2,...,m` source
packaged as `densityRhoSource`. -/
theorem positiveTiltedDensity_orbit_succ_fullRhoSource
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (s : ℕ) :
    positiveTiltedDensity m (orbit m p₀ (s + 1)) =
      transportCoeff m (orbit m p₀ s) •
          shiftLeft (positiveTiltedDensity m (orbit m p₀ s)) +
        densityRhoSource m p₀ s := by
  rw [positiveTiltedDensity_orbit_succ m p₀ hm hcrit s]
  funext j
  rfl

/-- Coefficientwise form of the generic finite shifted Duhamel formula.
The homogeneous term moves the coefficient by `n-a`, while a source inserted
at time `s` moves it by `n-1-s`. -/
theorem seq_recurrence_apply_eq_transport_add_forcing
    (u : ℕ → Seq) (c : ℕ → ℝ) (forcing : ℕ → Seq)
    (hrec : ∀ s : ℕ,
      u (s + 1) = c s • shiftLeft (u s) + forcing s)
    {a n : ℕ} (han : a ≤ n) (j : ℕ) :
    u n j =
      transportBetween c a n * u a (j + (n - a)) +
        ∑ s ∈ Finset.Ico a n,
          terminalTransportWeight c s n *
            forcing s (j + (n - 1 - s)) := by
  have hduhamel :=
    seq_recurrence_eq_truncatedInitial_add_forcing
      u c forcing hrec a (n - a)
  rw [Nat.add_sub_of_le han] at hduhamel
  have hj := congrFun hduhamel j
  simpa only [truncatedInitialTerm, truncatedForcingTerm,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftLeft_iterate_apply] using hj

/-- Literal finite Duhamel identity obtained by iterating `eq:rhor` between
generations `a` and `n`.  This is the algebraic core of source obligation U43;
all products and both sums are finite, including the endpoint case `a=n`. -/
theorem positiveTiltedDensity_orbit_apply_eq_discreteMildDuhamel
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) {a n : ℕ} (han : a ≤ n) (j : ℕ) :
    positiveTiltedDensity m (orbit m p₀ n) j =
      transportBetween
          (fun i ↦ transportCoeff m (orbit m p₀ i)) a n *
        positiveTiltedDensity m (orbit m p₀ a) (j + (n - a)) +
      ∑ s ∈ Finset.Ico a n,
        terminalTransportWeight
            (fun i ↦ transportCoeff m (orbit m p₀ i)) s n *
          (∑ r ∈ Finset.Ico 2 (m + 1),
            densityCoeff m r (orbit m p₀ s) *
              shiftRightPow (r - 2)
                (convPow r
                  (positiveTiltedDensity m (orbit m p₀ s)))
                (j + (n - 1 - s))) := by
  let rho : ℕ → Seq :=
    fun s ↦ positiveTiltedDensity m (orbit m p₀ s)
  let c : ℕ → ℝ :=
    fun s ↦ transportCoeff m (orbit m p₀ s)
  let forcing : ℕ → Seq := densityRhoSource m p₀
  have hrec : ∀ s : ℕ,
      rho (s + 1) = c s • shiftLeft (rho s) + forcing s := by
    intro s
    simpa only [rho, c, forcing] using
      positiveTiltedDensity_orbit_succ_fullRhoSource m p₀ hm hcrit s
  have hduhamel :=
    seq_recurrence_apply_eq_transport_add_forcing
      rho c forcing hrec han j
  simpa only [rho, c, forcing, densityRhoSource] using hduhamel

end

end DerridaRetaux
