import DerridaRetaux.Analysis.SmoothingAlgebra
import DerridaRetaux.Analysis.WeightedNorm
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Exact truncated Duhamel and telescope identities

This file formalizes the finite algebra in `eq:split` and `eq:telescope`.
All sums are finite and all endpoint cases are explicit.  Analytic estimates
for the resulting terms are deliberately kept in later modules.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- Product of transport coefficients from time `a` through time `n-1`. -/
def transportBetween (c : ℕ → ℝ) (a n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico a n, c i

/-- The coefficient called `P_s` when the terminal time is `n`. -/
def terminalTransportWeight (c : ℕ → ℝ) (s n : ℕ) : ℝ :=
  transportBetween c (s + 1) n

/-- Homogeneous part of the recurrence, started at time `a`. -/
def truncatedInitialTerm
    (u : ℕ → Seq) (c : ℕ → ℝ) (a n : ℕ) : Seq :=
  transportBetween c a n • (shiftLeft^[n - a]) (u a)

/-- Finite Duhamel sum for a forcing sequence. -/
def truncatedForcingTerm
    (c : ℕ → ℝ) (forcing : ℕ → Seq) (a n : ℕ) : Seq :=
  fun j : ℕ ↦
    ∑ s ∈ Finset.Ico a n,
      terminalTransportWeight c s n *
        (shiftLeft^[n - 1 - s]) (forcing s) j

@[simp]
theorem transportBetween_self (c : ℕ → ℝ) (a : ℕ) :
    transportBetween c a a = 1 := by
  simp [transportBetween]

theorem transportBetween_succ_right
    (c : ℕ → ℝ) {a n : ℕ} (han : a ≤ n) :
    transportBetween c a (n + 1) = transportBetween c a n * c n := by
  exact Finset.prod_Ico_succ_top han c

/-- The exclusive transport product factors into its prefix through `a-1`
and the interval product from `a` through `n-1`. -/
theorem transportProduct_mul_transportBetween
    (m : ℕ) (p₀ : ProbabilityMass) {a n : ℕ} (han : a ≤ n) :
    transportProduct m p₀ a *
        transportBetween (fun s ↦ transportCoeff m (orbit m p₀ s)) a n =
      transportProduct m p₀ n := by
  simpa only [transportProduct, transportBetween] using
    Finset.prod_range_mul_prod_Ico
      (fun s ↦ transportCoeff m (orbit m p₀ s)) han

/-- Source-facing ratio form of the interval product, justified by strict
positivity of the prefix `C_a`. -/
theorem transportBetween_eq_transportProduct_div
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    {a n : ℕ} (han : a ≤ n) :
    transportBetween (fun s ↦ transportCoeff m (orbit m p₀ s)) a n =
      transportProduct m p₀ n / transportProduct m p₀ a := by
  have hCa := transportProduct_pos m p₀ hm hcrit hnotBinaryFixedPoint a
  apply (eq_div_iff hCa.ne').2
  simpa only [mul_comm] using transportProduct_mul_transportBetween m p₀ han

theorem terminalTransportWeight_succ_right
    (c : ℕ → ℝ) {s n : ℕ} (hsn : s < n) :
    terminalTransportWeight c s (n + 1) =
      terminalTransportWeight c s n * c n := by
  exact transportBetween_succ_right c (Nat.succ_le_iff.mpr hsn)

/-- A first-order shifted recurrence has the exact finite Duhamel expansion. -/
theorem seq_recurrence_eq_truncatedInitial_add_forcing
    (u : ℕ → Seq) (c : ℕ → ℝ) (forcing : ℕ → Seq)
    (hrec : ∀ s : ℕ,
      u (s + 1) = c s • shiftLeft (u s) + forcing s)
    (a h : ℕ) :
    u (a + h) =
      truncatedInitialTerm u c a (a + h) +
        truncatedForcingTerm c forcing a (a + h) := by
  induction h with
  | zero =>
      funext j
      simp [truncatedInitialTerm, truncatedForcingTerm, transportBetween]
  | succ h ih =>
      have han : a ≤ a + h := Nat.le_add_right a h
      rw [show a + (h + 1) = (a + h) + 1 by omega, hrec]
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftLeft_apply]
      rw [congrFun ih (j + 1)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        truncatedInitialTerm, truncatedForcingTerm]
      rw [transportBetween_succ_right c han]
      rw [Finset.sum_Ico_succ_top han]
      simp only [terminalTransportWeight, transportBetween_self, one_mul,
        Nat.add_sub_cancel_left, Function.iterate_zero_apply]
      rw [mul_add]
      rw [Finset.mul_sum]
      have hsum :
          c (a + h) *
              (∑ s ∈ Finset.Ico a (a + h),
                terminalTransportWeight c s (a + h) *
                  (shiftLeft^[a + h - 1 - s]) (forcing s) (j + 1)) =
            ∑ s ∈ Finset.Ico a (a + h),
              terminalTransportWeight c s (a + h + 1) *
                (shiftLeft^[a + h + 1 - 1 - s]) (forcing s) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        have hsn : s < a + h := (Finset.mem_Ico.mp hs).2
        rw [terminalTransportWeight_succ_right c hsn]
        rw [shiftLeft_iterate_apply, shiftLeft_iterate_apply]
        have hindex : j + (a + h + 1 - 1 - s) =
            j + 1 + (a + h - 1 - s) := by omega
        rw [hindex]
        ring
      dsimp only [terminalTransportWeight] at hsum
      rw [← Finset.mul_sum, hsum]
      rw [shiftLeft_iterate_apply, shiftLeft_iterate_apply]
      have hlast : a + h + 1 - 1 - (a + h) = 0 := by omega
      have hdiff : a + h + 1 - a = h + 1 := by omega
      simp only [hlast, Function.iterate_zero_apply, Nat.add_sub_cancel_left]
      rw [hdiff]
      simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      ring

/-- Duhamel forcing is additive in the source. -/
theorem truncatedForcingTerm_add
    (c : ℕ → ℝ) (f g : ℕ → Seq) (a n : ℕ) :
    truncatedForcingTerm c (fun s ↦ f s + g s) a n =
      truncatedForcingTerm c f a n + truncatedForcingTerm c g a n := by
  funext j
  simp only [truncatedForcingTerm, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [shiftLeft_iterate_apply, shiftLeft_iterate_apply, shiftLeft_iterate_apply]
  simp only [Pi.add_apply]
  ring

/-- Source notation for the homogeneous term `I_(a,n)`. -/
def densityInitialSegment
    (m : ℕ) (p₀ : ProbabilityMass) (a n : ℕ) : Seq :=
  truncatedInitialTerm
    (fun s ↦ positiveTiltedDensity m (orbit m p₀ s))
    (fun s ↦ transportCoeff m (orbit m p₀ s)) a n

/-- Source notation for the quadratic contribution `Q_(a,n)`. -/
def densityQuadraticSegment
    (m : ℕ) (p₀ : ProbabilityMass) (a n : ℕ) : Seq :=
  truncatedForcingTerm
    (fun s ↦ transportCoeff m (orbit m p₀ s))
    (fun s ↦ densityD m p₀ s • densityB m p₀ s) a n

/-- Source notation for the higher-order contribution `W_(a,n)`. -/
def densityHigherSegment
    (m : ℕ) (p₀ : ProbabilityMass) (a n : ℕ) : Seq :=
  truncatedForcingTerm
    (fun s ↦ transportCoeff m (orbit m p₀ s))
    (densityE m p₀) a n

/-- The late part `V_(a,n)=Q_(a,n)+W_(a,n)`. -/
def densityLateSegment
    (m : ℕ) (p₀ : ProbabilityMass) (a n : ℕ) : Seq :=
  densityQuadraticSegment m p₀ a n + densityHigherSegment m p₀ a n

/-- The homogeneous segment is exactly the manuscript term
`(C_n / C_a) S^(n-a) rho_a`. -/
theorem densityInitialSegment_eq_transportProduct_ratio
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    {a n : ℕ} (han : a ≤ n) :
    densityInitialSegment m p₀ a n =
      (transportProduct m p₀ n / transportProduct m p₀ a) •
        (shiftLeft^[n - a]) (positiveTiltedDensity m (orbit m p₀ a)) := by
  simp only [densityInitialSegment, truncatedInitialTerm]
  rw [transportBetween_eq_transportProduct_div
    m p₀ hm hcrit hnotBinaryFixedPoint han]

/-- Exact source-facing `eq:split`, with transport products left in finite
product form. -/
theorem positiveTiltedDensity_eq_initial_add_quadratic_add_higher
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) {a n : ℕ} (han : a ≤ n) :
    positiveTiltedDensity m (orbit m p₀ n) =
      densityInitialSegment m p₀ a n +
        densityQuadraticSegment m p₀ a n +
          densityHigherSegment m p₀ a n := by
  let rho : ℕ → Seq := fun s ↦ positiveTiltedDensity m (orbit m p₀ s)
  let c : ℕ → ℝ := fun s ↦ transportCoeff m (orbit m p₀ s)
  let quadratic : ℕ → Seq := fun s ↦ densityD m p₀ s • densityB m p₀ s
  let higher : ℕ → Seq := densityE m p₀
  have hrec : ∀ s : ℕ,
      rho (s + 1) = c s • shiftLeft (rho s) + (quadratic s + higher s) := by
    intro s
    simpa only [rho, c, quadratic, higher, shortDensityStep, densityB,
      add_assoc] using positiveTiltedDensity_orbit_succ_short m p₀ hm hcrit s
  have hduhamel := seq_recurrence_eq_truncatedInitial_add_forcing
    rho c (fun s ↦ quadratic s + higher s) hrec a (n - a)
  rw [Nat.add_sub_of_le han] at hduhamel
  rw [truncatedForcingTerm_add] at hduhamel
  simpa only [rho, c, quadratic, higher, densityInitialSegment,
    densityQuadraticSegment, densityHigherSegment, add_assoc] using hduhamel

/-- Equivalent two-part form `rho_n=I_(a,n)+V_(a,n)`. -/
theorem positiveTiltedDensity_eq_initial_add_late
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) {a n : ℕ} (han : a ≤ n) :
    positiveTiltedDensity m (orbit m p₀ n) =
      densityInitialSegment m p₀ a n + densityLateSegment m p₀ a n := by
  simpa only [densityLateSegment, add_assoc] using
    positiveTiltedDensity_eq_initial_add_quadratic_add_higher
      m p₀ hm hcrit han

/-- Fully source-shaped `eq:split`, including the displayed ratio `C_n/C_a`. -/
theorem positiveTiltedDensity_eq_transportRatio_add_quadratic_add_higher
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    {a n : ℕ} (han : a ≤ n) :
    positiveTiltedDensity m (orbit m p₀ n) =
      (transportProduct m p₀ n / transportProduct m p₀ a) •
          (shiftLeft^[n - a]) (positiveTiltedDensity m (orbit m p₀ a)) +
        densityQuadraticSegment m p₀ a n +
          densityHigherSegment m p₀ a n := by
  rw [positiveTiltedDensity_eq_initial_add_quadratic_add_higher
    m p₀ hm hcrit han]
  rw [densityInitialSegment_eq_transportProduct_ratio
    m p₀ hm hcrit hnotBinaryFixedPoint han]

/-- The coefficient `w_s=P_s d_s` in the quadratic Duhamel sum. -/
def densityQuadraticWeight
    (m : ℕ) (p₀ : ProbabilityMass) (s n : ℕ) : ℝ :=
  terminalTransportWeight
      (fun i ↦ transportCoeff m (orbit m p₀ i)) s n *
    densityD m p₀ s

/-- The transported quadratic kernel `K_s=S^(n-1-s) B_s`. -/
def densityQuadraticKernel
    (m : ℕ) (p₀ : ProbabilityMass) (n s : ℕ) : Seq :=
  (shiftLeft^[n - 1 - s]) (densityB m p₀ s)

@[simp]
theorem densityQuadraticKernel_terminal
    (m : ℕ) (p₀ : ProbabilityMass) (n : ℕ) :
    densityQuadraticKernel m p₀ n (n - 1) = densityB m p₀ (n - 1) := by
  simp [densityQuadraticKernel]

@[simp]
theorem densityQuadraticWeight_terminal
    (m : ℕ) (p₀ : ProbabilityMass) {n : ℕ} (hn : 1 ≤ n) :
    densityQuadraticWeight m p₀ (n - 1) n = densityD m p₀ (n - 1) := by
  have hindex : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simp [densityQuadraticWeight, terminalTransportWeight, hindex]

theorem densityQuadraticKernel_penultimate
    (m : ℕ) (p₀ : ProbabilityMass) {n : ℕ} (hn : 2 ≤ n) :
    densityQuadraticKernel m p₀ n (n - 2) =
      shiftLeft (densityB m p₀ (n - 2)) := by
  have hexponent : n - 1 - (n - 2) = 1 := by omega
  simp [densityQuadraticKernel, hexponent, Function.iterate_one]

/-- The abstract Duhamel definition of `Q_(a,n)` is its manuscript sum
`sum w_s K_s`. -/
theorem densityQuadraticSegment_eq_weightedKernelSum
    (m : ℕ) (p₀ : ProbabilityMass) (a n : ℕ) :
    densityQuadraticSegment m p₀ a n =
      fun j : ℕ ↦ ∑ s ∈ Finset.Ico a n,
        densityQuadraticWeight m p₀ s n *
          densityQuadraticKernel m p₀ n s j := by
  funext j
  simp only [densityQuadraticSegment, truncatedForcingTerm,
    densityQuadraticWeight, densityQuadraticKernel]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [shiftLeft_iterate_apply, shiftLeft_iterate_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Transported form of `eq:Bevolution` for adjacent kernels. -/
theorem densityQuadraticKernel_succ
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) {s n : ℕ} (hsn : s + 1 < n) :
    densityQuadraticKernel m p₀ n (s + 1) =
      transportCoeff m (orbit m p₀ s) ^ 2 •
          shiftLeft (densityQuadraticKernel m p₀ n s) +
        (shiftLeft^[n - 2 - s]) (densityR m p₀ s) := by
  funext j
  simp only [densityQuadraticKernel, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    shiftLeft_apply, shiftLeft_iterate_apply]
  rw [congrFun (densityB_orbit_succ m p₀ hm hcrit s)
    (j + (n - 1 - (s + 1)))]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    shiftLeft_apply, shiftLeft_iterate_apply]
  have hfirst :
      j + (n - 1 - (s + 1)) + 2 = j + 1 + (n - 1 - s) := by omega
  have hsecond :
      j + (n - 1 - (s + 1)) = j + (n - 2 - s) := by omega
  rw [hfirst, hsecond]

/-- Solved form of the kernel difference.  Positivity of the transport
coefficient is used only to justify the inverse square. -/
theorem discreteDerivative_densityQuadraticKernel
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    {s n : ℕ} (hsn : s + 1 < n) :
    discreteDerivative (densityQuadraticKernel m p₀ n s) =
      densityQuadraticKernel m p₀ n s -
        (transportCoeff m (orbit m p₀ s))⁻¹ ^ 2 •
          densityQuadraticKernel m p₀ n (s + 1) +
        (transportCoeff m (orbit m p₀ s))⁻¹ ^ 2 •
          (shiftLeft^[n - 2 - s]) (densityR m p₀ s) := by
  have hcpos := transportCoeff_pos m (orbit m p₀ s) (by omega)
    (orbit_critical m p₀ (by omega) hcrit s)
      (orbit_zeroTilt_pos m p₀ hm hcrit hnotBinaryFixedPoint s)
  have hkernel := densityQuadraticKernel_succ m p₀ hm hcrit hsn
  funext j
  have hj := congrFun hkernel j
  simp only [discreteDerivative_apply, shiftLeft_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftLeft_iterate_apply] at hj ⊢
  field_simp [hcpos.ne']
  nlinarith

/-- Finite weighted sum of kernels over `[a,n)`. -/
def weightedKernelSum
    (w : ℕ → ℝ) (K : ℕ → Seq) (a n : ℕ) : Seq :=
  ∑ s ∈ Finset.Ico a n, w s • K s

@[simp]
theorem weightedKernelSum_apply
    (w : ℕ → ℝ) (K : ℕ → Seq) (a n j : ℕ) :
    weightedKernelSum w K a n j =
      ∑ s ∈ Finset.Ico a n, w s * K s j := by
  simp [weightedKernelSum]

theorem densityQuadraticSegment_eq_weightedKernelSum_seq
    (m : ℕ) (p₀ : ProbabilityMass) (a n : ℕ) :
    densityQuadraticSegment m p₀ a n =
      weightedKernelSum (fun s ↦ densityQuadraticWeight m p₀ s n)
        (densityQuadraticKernel m p₀ n) a n := by
  rw [densityQuadraticSegment_eq_weightedKernelSum]
  funext j
  simp only [weightedKernelSum_apply]

theorem discreteDerivative_smul (c : ℝ) (f : Seq) :
    discreteDerivative (c • f) = c • discreteDerivative f := by
  funext j
  simp [discreteDerivative]
  ring

theorem discreteDerivative_weightedKernelSum
    (w : ℕ → ℝ) (K : ℕ → Seq) (a n : ℕ) :
    discreteDerivative (weightedKernelSum w K a n) =
      ∑ s ∈ Finset.Ico a n, w s • discreteDerivative (K s) := by
  funext j
  simp only [discreteDerivative_apply, weightedKernelSum_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- Finite summation by parts for the adjacent-kernel terms. -/
theorem weightedKernelSum_sub_succ_telescope
    (w z : ℕ → ℝ) (K : ℕ → Seq) {a n : ℕ} (hspan : a + 1 < n) :
    (∑ s ∈ Finset.Ico a (n - 1), w s • K s) -
        (∑ s ∈ Finset.Ico a (n - 1), (w s * z s) • K (s + 1)) =
      w a • K a - (w (n - 2) * z (n - 2)) • K (n - 1) +
        ∑ s ∈ Finset.Ico (a + 1) (n - 1),
          (w s - w (s - 1) * z (s - 1)) • K s := by
  have hab : a < n - 1 := by omega
  have habTop : a + 1 ≤ n - 1 := by omega
  have hreindex :
      (∑ s ∈ Finset.Ico a (n - 1), (w s * z s) • K (s + 1)) =
        ∑ s ∈ Finset.Ico (a + 1) n,
          (w (s - 1) * z (s - 1)) • K s := by
    have hshift := Finset.sum_Ico_add'
      (fun s ↦ (w (s - 1) * z (s - 1)) • K s) a (n - 1) 1
    simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel (by omega : 1 ≤ n)] using hshift
  have hsplitTop :
      (∑ s ∈ Finset.Ico (a + 1) n,
          (w (s - 1) * z (s - 1)) • K s) =
        (∑ s ∈ Finset.Ico (a + 1) (n - 1),
          (w (s - 1) * z (s - 1)) • K s) +
          (w (n - 2) * z (n - 2)) • K (n - 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.sub_sub,
      one_add_one_eq_two] using
        Finset.sum_Ico_succ_top habTop
          (fun s ↦ (w (s - 1) * z (s - 1)) • K s)
  rw [Finset.sum_eq_sum_Ico_succ_bot hab]
  rw [hreindex, hsplitTop]
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib]
  abel

/-- Exact endpoint-aware telescope for any family satisfying the solved
adjacent-kernel relation. -/
theorem discreteDerivative_weightedKernelSum_telescope
    (w z : ℕ → ℝ) (K remainder : ℕ → Seq) {a n : ℕ}
    (hspan : a + 1 < n)
    (hkernel : ∀ s ∈ Finset.Ico a (n - 1),
      discreteDerivative (K s) = K s - z s • K (s + 1) + remainder s) :
    discreteDerivative (weightedKernelSum w K a n) =
      w a • K a - (w (n - 2) * z (n - 2)) • K (n - 1) +
        w (n - 1) • discreteDerivative (K (n - 1)) +
        (∑ s ∈ Finset.Ico (a + 1) (n - 1),
          (w s - w (s - 1) * z (s - 1)) • K s) +
        ∑ s ∈ Finset.Ico a (n - 1), w s • remainder s := by
  have han : a ≤ n - 1 := by omega
  rw [discreteDerivative_weightedKernelSum]
  have hsplitTop :
      (∑ s ∈ Finset.Ico a n, w s • discreteDerivative (K s)) =
        (∑ s ∈ Finset.Ico a (n - 1), w s • discreteDerivative (K s)) +
          w (n - 1) • discreteDerivative (K (n - 1)) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      Finset.sum_Ico_succ_top han
        (fun s ↦ w s • discreteDerivative (K s))
  rw [hsplitTop]
  have hearly :
      (∑ s ∈ Finset.Ico a (n - 1), w s • discreteDerivative (K s)) =
        (∑ s ∈ Finset.Ico a (n - 1), w s • K s) -
          (∑ s ∈ Finset.Ico a (n - 1), (w s * z s) • K (s + 1)) +
          ∑ s ∈ Finset.Ico a (n - 1), w s • remainder s := by
    calc
      (∑ s ∈ Finset.Ico a (n - 1), w s • discreteDerivative (K s)) =
          ∑ s ∈ Finset.Ico a (n - 1),
            w s • (K s - z s • K (s + 1) + remainder s) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hkernel s hs]
      _ = _ := by
        simp_rw [smul_add, smul_sub, smul_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hearly]
  rw [weightedKernelSum_sub_succ_telescope w z K hspan]
  abel

/-- Exact `eq:telescope` for the quadratic part of the orbit recurrence. -/
theorem discreteDerivative_densityQuadraticSegment_telescope
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀)
    (hnotBinaryFixedPoint : ¬(m = 2 ∧ p₀ = diracMass 1))
    {a n : ℕ} (hspan : a + 1 < n) :
    discreteDerivative (densityQuadraticSegment m p₀ a n) =
      densityQuadraticWeight m p₀ a n •
          densityQuadraticKernel m p₀ n a -
        (densityQuadraticWeight m p₀ (n - 2) n *
            (transportCoeff m (orbit m p₀ (n - 2)))⁻¹ ^ 2) •
          densityQuadraticKernel m p₀ n (n - 1) +
        densityQuadraticWeight m p₀ (n - 1) n •
          discreteDerivative (densityQuadraticKernel m p₀ n (n - 1)) +
        (∑ s ∈ Finset.Ico (a + 1) (n - 1),
          (densityQuadraticWeight m p₀ s n -
              densityQuadraticWeight m p₀ (s - 1) n *
                (transportCoeff m (orbit m p₀ (s - 1)))⁻¹ ^ 2) •
            densityQuadraticKernel m p₀ n s) +
        ∑ s ∈ Finset.Ico a (n - 1),
          densityQuadraticWeight m p₀ s n •
            ((transportCoeff m (orbit m p₀ s))⁻¹ ^ 2 •
              (shiftLeft^[n - 2 - s]) (densityR m p₀ s)) := by
  let w : ℕ → ℝ := fun s ↦ densityQuadraticWeight m p₀ s n
  let z : ℕ → ℝ :=
    fun s ↦ (transportCoeff m (orbit m p₀ s))⁻¹ ^ 2
  let K : ℕ → Seq := densityQuadraticKernel m p₀ n
  let remainder : ℕ → Seq := fun s ↦
    z s • (shiftLeft^[n - 2 - s]) (densityR m p₀ s)
  have hkernel : ∀ s ∈ Finset.Ico a (n - 1),
      discreteDerivative (K s) = K s - z s • K (s + 1) + remainder s := by
    intro s hs
    have hsn : s + 1 < n := by
      have hslt := (Finset.mem_Ico.mp hs).2
      omega
    simpa only [K, z, remainder] using
      discreteDerivative_densityQuadraticKernel
        m p₀ hm hcrit hnotBinaryFixedPoint hsn
  have htel := discreteDerivative_weightedKernelSum_telescope
    w z K remainder hspan hkernel
  rw [densityQuadraticSegment_eq_weightedKernelSum_seq]
  simpa only [w, z, K, remainder] using htel

end

end DerridaRetaux
