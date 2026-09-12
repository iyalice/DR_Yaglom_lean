import DerridaRetaux.Analysis.CoefficientVariation
import DerridaRetaux.Analysis.LogRate
import DerridaRetaux.Analysis.TruncatedTelescope
import DerridaRetaux.Model.TransportLimit
import Mathlib.Tactic

/-!
# Coefficient limits for the discrete mild equation

This module records the cofinal-scale, floor-index, and moving-window limits used
when the exact discrete Duhamel formula is passed to a positive macroscopic time
window.  The orbit results use only the explicit H1a fact.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace DerridaRetaux

noncomputable section

/-- A positive real multiple of any cofinal natural scale has a cofinal natural
floor. -/
theorem natFloor_mul_cofinal_tendsto_atTop
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k : ℕ ↦ ⌊t * (scale k : ℝ)⌋₊) atTop atTop := by
  exact (tendsto_nat_floor_mul_atTop t ht).comp hscale

/-- Adding a fixed natural shift preserves cofinality of a positive floor
time. -/
theorem natFloor_mul_cofinal_add_const_tendsto_atTop
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (q : ℕ) :
    Tendsto (fun k : ℕ ↦ ⌊t * (scale k : ℝ)⌋₊ + q) atTop atTop := by
  exact (tendsto_add_atTop_nat q).comp
    (natFloor_mul_cofinal_tendsto_atTop scale hscale t ht)

/-- Subtracting a fixed natural shift also preserves cofinality of a positive
floor time. -/
theorem natFloor_mul_cofinal_sub_const_tendsto_atTop
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (q : ℕ) :
    Tendsto (fun k : ℕ ↦ ⌊t * (scale k : ℝ)⌋₊ - q) atTop atTop := by
  have hfloor := natFloor_mul_cofinal_tendsto_atTop scale hscale t ht
  rw [tendsto_atTop]
  intro b
  filter_upwards [hfloor.eventually_ge_atTop (b + q)] with k hk
  omega

/-- The floor of a positive macroscopic time, normalized by an arbitrary
cofinal scale, converges to that time. -/
theorem natFloor_mul_cofinal_div_tendsto
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) :
    Tendsto
      (fun k : ℕ ↦ (⌊t * (scale k : ℝ)⌋₊ : ℝ) / (scale k : ℝ))
      atTop (nhds t) := by
  have hscaleReal :
      Tendsto (fun k : ℕ ↦ (scale k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hscale
  simpa only [Function.comp_apply] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) ht.le).comp hscaleReal

/-- Adding a fixed natural shift to a macroscopic floor index does not change
its normalized limit. -/
theorem natFloor_mul_cofinal_add_const_div_tendsto
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (q : ℕ) :
    Tendsto
      (fun k : ℕ ↦ ((⌊t * (scale k : ℝ)⌋₊ + q : ℕ) : ℝ) /
        (scale k : ℝ))
      atTop (nhds t) := by
  have hfloor := natFloor_mul_cofinal_div_tendsto scale hscale t ht
  have hshift :
      Tendsto (fun k : ℕ ↦ (q : ℝ) / (scale k : ℝ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (q : ℝ)).comp hscale
  simpa only [Nat.cast_add, add_div, add_zero] using hfloor.add hshift

/-- Subtracting a fixed natural shift from a cofinal macroscopic floor index
does not change its normalized limit. -/
theorem natFloor_mul_cofinal_sub_const_div_tendsto
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (q : ℕ) :
    Tendsto
      (fun k : ℕ ↦ ((⌊t * (scale k : ℝ)⌋₊ - q : ℕ) : ℝ) /
        (scale k : ℝ))
      atTop (nhds t) := by
  have hfloor := natFloor_mul_cofinal_div_tendsto scale hscale t ht
  have hshift :
      Tendsto (fun k : ℕ ↦ (q : ℝ) / (scale k : ℝ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (q : ℝ)).comp hscale
  have hraw :
      Tendsto
        (fun k : ℕ ↦
          (⌊t * (scale k : ℝ)⌋₊ : ℝ) / (scale k : ℝ) -
            (q : ℝ) / (scale k : ℝ))
        atTop (nhds t) := by
    simpa only [sub_zero] using hfloor.sub hshift
  apply hraw.congr'
  have hfloorTop := natFloor_mul_cofinal_tendsto_atTop scale hscale t ht
  filter_upwards [hfloorTop.eventually_ge_atTop q] with k hk
  rw [Nat.cast_sub hk]
  ring

/-- Normalized floor error remains negligible after a fixed positive index
shift. -/
theorem natFloor_mul_cofinal_add_const_error_tendsto_zero
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (q : ℕ) :
    Tendsto
      (fun k : ℕ ↦ ((⌊t * (scale k : ℝ)⌋₊ + q : ℕ) : ℝ) /
        (scale k : ℝ) - t)
      atTop (nhds 0) := by
  simpa only [sub_self] using
    (natFloor_mul_cofinal_add_const_div_tendsto scale hscale t ht q).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ t) atTop (nhds t))

/-- Normalized floor error remains negligible after a fixed negative index
shift. -/
theorem natFloor_mul_cofinal_sub_const_error_tendsto_zero
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (q : ℕ) :
    Tendsto
      (fun k : ℕ ↦ ((⌊t * (scale k : ℝ)⌋₊ - q : ℕ) : ℝ) /
        (scale k : ℝ) - t)
      atTop (nhds 0) := by
  simpa only [sub_self] using
    (natFloor_mul_cofinal_sub_const_div_tendsto scale hscale t ht q).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ t) atTop (nhds t))

/-- The normalized difference of two floor times converges to the length of
the macroscopic time window. -/
theorem natFloor_window_div_cofinal_tendsto
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t₀ t : ℝ) (ht₀ : 0 < t₀) (hwindow : t₀ ≤ t) :
    Tendsto
      (fun k : ℕ ↦
        ((⌊t * (scale k : ℝ)⌋₊ - ⌊t₀ * (scale k : ℝ)⌋₊ : ℕ) : ℝ) /
          (scale k : ℝ))
      atTop (nhds (t - t₀)) := by
  have ht : 0 < t := ht₀.trans_le hwindow
  have htop := natFloor_mul_cofinal_div_tendsto scale hscale t ht
  have hbot := natFloor_mul_cofinal_div_tendsto scale hscale t₀ ht₀
  have hraw := htop.sub hbot
  apply hraw.congr'
  filter_upwards [] with k
  have hfloor :
      ⌊t₀ * (scale k : ℝ)⌋₊ ≤ ⌊t * (scale k : ℝ)⌋₊ := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right hwindow (Nat.cast_nonneg (scale k))
  rw [Nat.cast_sub hfloor]
  ring

/-- Any convergent natural-indexed family has the same limit along an
arbitrary positive floor time on an arbitrary cofinal scale. -/
theorem tendsto_along_natFloor_mul_cofinal
    {f : ℕ → ℝ} {x : ℝ} (hf : Tendsto f atTop (nhds x))
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k : ℕ ↦ f ⌊t * (scale k : ℝ)⌋₊) atTop (nhds x) := by
  exact hf.comp (natFloor_mul_cofinal_tendsto_atTop scale hscale t ht)

/-- Convergence at infinity is uniform over every moving tail whose lower
endpoint is cofinal. -/
theorem tendsto_uniform_after_cofinal
    {f : ℕ → ℝ} {x : ℝ} (hf : Tendsto f atTop (nhds x))
    (lower : ℕ → ℕ) (hlower : Tendsto lower atTop atTop) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, lower k ≤ n → |f n - x| < ε := by
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop, f n ∈ Metric.ball x ε :=
    hf (Metric.ball_mem_nhds x hε)
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  filter_upwards [hlower.eventually_ge_atTop N] with k hk
  intro n hkn
  simpa only [Metric.mem_ball, Real.dist_eq] using hN n (hk.trans hkn)

/-- H1a gives the source quadratic coefficient limit along every positive
moving grid time and every cofinal scale. -/
theorem orbit_densityD_natFloor_tendsto_half_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) :
    Tendsto
      (fun k : ℕ ↦ densityD m p₀ ⌊t * (scale k : ℝ)⌋₊)
      atTop (nhds ((1 : ℝ) / 2)) := by
  exact tendsto_along_natFloor_mul_cofinal
    (orbit_densityD_tendsto_half_of_excess
      m p₀ hm hcrit hthird hnonconstant hExcess)
    scale hscale t ht

/-- The moving-grid quadratic coefficient has the same limit after any fixed
positive index shift. -/
theorem orbit_densityD_natFloor_add_const_tendsto_half_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (q : ℕ) :
    Tendsto
      (fun k : ℕ ↦ densityD m p₀ (⌊t * (scale k : ℝ)⌋₊ + q))
      atTop (nhds ((1 : ℝ) / 2)) := by
  exact (orbit_densityD_tendsto_half_of_excess
    m p₀ hm hcrit hthird hnonconstant hExcess).comp
      (natFloor_mul_cofinal_add_const_tendsto_atTop
        scale hscale t ht q)

/-- The moving-grid quadratic coefficient has the same limit after any fixed
negative index shift. -/
theorem orbit_densityD_natFloor_sub_const_tendsto_half_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t : ℝ) (ht : 0 < t) (q : ℕ) :
    Tendsto
      (fun k : ℕ ↦ densityD m p₀ (⌊t * (scale k : ℝ)⌋₊ - q))
      atTop (nhds ((1 : ℝ) / 2)) := by
  exact (orbit_densityD_tendsto_half_of_excess
    m p₀ hm hcrit hthird hnonconstant hExcess).comp
      (natFloor_mul_cofinal_sub_const_tendsto_atTop
        scale hscale t ht q)

/-- The source quadratic coefficient is uniformly close to `1 / 2` at every
generation after a positive moving floor time.  In particular this is uniform
on every later compact macroscopic time window. -/
theorem orbit_densityD_uniform_after_natFloor_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∀ s : ℕ,
        ⌊t₀ * (scale k : ℝ)⌋₊ ≤ s →
          |densityD m p₀ s - (1 : ℝ) / 2| < ε := by
  exact tendsto_uniform_after_cofinal
    (orbit_densityD_tendsto_half_of_excess
      m p₀ hm hcrit hthird hnonconstant hExcess)
    (fun k : ℕ ↦ ⌊t₀ * (scale k : ℝ)⌋₊)
    (natFloor_mul_cofinal_tendsto_atTop scale hscale t₀ ht₀)

/-- A summable norm defect makes every finite product sufficiently far in the
tail uniformly close to one. -/
theorem transportBetween_tendsto_one_uniform_of_summable_norm
    (c : ℕ → ℝ) (hdefect : Summable (fun s : ℕ ↦ ‖c s - 1‖))
    (lower : ℕ → ℕ) (hlower : Tendsto lower atTop atTop) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∀ a n : ℕ, lower k ≤ a → a ≤ n →
        |transportBetween c a n - 1| < ε := by
  intro ε hε
  obtain ⟨s₀, hs₀⟩ := prod_vanishing_of_summable_norm
    (f := fun s : ℕ ↦ c s - 1) hdefect hε
  filter_upwards [hlower.eventually_gt_atTop (s₀.sup id)] with k hk
  intro a n hka _han
  have hdisjoint : Disjoint (Finset.Ico a n) s₀ := by
    rw [Finset.disjoint_left]
    intro i hiI his₀
    have hisup : i ≤ s₀.sup id := Finset.le_sup (f := id) his₀
    have hai : a ≤ i := (Finset.mem_Ico.mp hiI).1
    omega
  have hbound := hs₀ (Finset.Ico a n) hdisjoint
  have hproduct :
      (∏ i ∈ Finset.Ico a n, (1 + (c i - 1))) =
        transportBetween c a n := by
    unfold transportBetween
    apply Finset.prod_congr rfl
    intro i _hi
    ring
  rw [hproduct] at hbound
  simpa only [Real.norm_eq_abs] using hbound

/-- H1a specializes uniform tail-product convergence to the actual critical
orbit transport coefficients. -/
theorem transportBetween_orbit_tendsto_one_uniform_after_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (lower : ℕ → ℕ) (hlower : Tendsto lower atTop atTop) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∀ a n : ℕ, lower k ≤ a → a ≤ n →
        |transportBetween
          (fun s ↦ transportCoeff m (orbit m p₀ s)) a n - 1| < ε := by
  have hdefectRaw := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hdefect : Summable
      (fun s : ℕ ↦ ‖transportCoeff m (orbit m p₀ s) - 1‖) := by
    convert hdefectRaw using 1
    funext s
    rw [Real.norm_eq_abs, abs_sub_comm]
    change |orbitTransportDefect m p₀ s| = orbitTransportDefect m p₀ s
    rw [abs_of_nonneg (orbitTransportDefect_nonneg m p₀ (by omega) hcrit s)]
  exact transportBetween_tendsto_one_uniform_of_summable_norm
    (fun s ↦ transportCoeff m (orbit m p₀ s)) hdefect lower hlower

/-- A moving interval whose lower endpoint is cofinal has asymptotically
trivial orbit transport.  The upper endpoint may be any eventual extension of
the lower endpoint. -/
theorem transportBetween_orbit_tendsto_one_along_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (lower upper : ℕ → ℕ) (hlower : Tendsto lower atTop atTop)
    (horder : ∀ᶠ k : ℕ in atTop, lower k ≤ upper k) :
    Tendsto
      (fun k : ℕ ↦ transportBetween
        (fun s ↦ transportCoeff m (orbit m p₀ s)) (lower k) (upper k))
      atTop (nhds 1) := by
  have hnotBinaryFixedPoint : ¬ (m = 2 ∧ p₀ = diracMass 1) := by
    rintro ⟨_mTwo, hp₀⟩
    exact hnonconstant ⟨1, hp₀⟩
  have hdefectRaw := orbitTransportDefect_summable
    m p₀ hm hcrit hthird hnonconstant hExcess
  have hdefect : Summable
      (fun s : ℕ ↦ 1 - transportCoeff m (orbit m p₀ s)) := by
    simpa only [orbitTransportDefect] using hdefectRaw
  have hproduct := tendsto_transportProduct_of_defect_summable m p₀ hdefect
  have hupper : Tendsto upper atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hlower.eventually_ge_atTop b, horder] with k hk hkOrder
    exact hk.trans hkOrder
  have hlimitPos := transportProductLimit_pos_of_defect_summable
    m p₀ hm hcrit hnotBinaryFixedPoint hdefect
  have hratio := (hproduct.comp hupper).div (hproduct.comp hlower) hlimitPos.ne'
  have hratioOne :
      Tendsto
        (fun k : ℕ ↦ transportProduct m p₀ (upper k) /
          transportProduct m p₀ (lower k))
        atTop (nhds 1) := by
    simpa only [div_self hlimitPos.ne'] using hratio
  apply hratioOne.congr'
  filter_upwards [horder] with k hk
  exact (transportBetween_eq_transportProduct_div
    m p₀ hm hcrit hnotBinaryFixedPoint hk).symm

/-- Floor endpoints of every fixed positive macroscopic time window give an
interval transport product converging to one, along any cofinal scale. -/
theorem transportBetween_orbit_natFloor_window_tendsto_one_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t₀ t : ℝ) (ht₀ : 0 < t₀) (hwindow : t₀ ≤ t) :
    Tendsto
      (fun k : ℕ ↦ transportBetween
        (fun s ↦ transportCoeff m (orbit m p₀ s))
        ⌊t₀ * (scale k : ℝ)⌋₊ ⌊t * (scale k : ℝ)⌋₊)
      atTop (nhds 1) := by
  apply transportBetween_orbit_tendsto_one_along_of_H1a
    m p₀ hm hcrit hthird hnonconstant hExcess
    (fun k : ℕ ↦ ⌊t₀ * (scale k : ℝ)⌋₊)
    (fun k : ℕ ↦ ⌊t * (scale k : ℝ)⌋₊)
    (natFloor_mul_cofinal_tendsto_atTop scale hscale t₀ ht₀)
  filter_upwards [] with k
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right hwindow (Nat.cast_nonneg (scale k))

/-- Uniform form of the floor-window transport limit: every subinterval whose
left endpoint lies after the positive macroscopic lower time has product close
to one. -/
theorem transportBetween_orbit_uniform_on_natFloor_window_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∀ a n : ℕ,
        ⌊t₀ * (scale k : ℝ)⌋₊ ≤ a → a ≤ n →
          |transportBetween
            (fun s ↦ transportCoeff m (orbit m p₀ s)) a n - 1| < ε := by
  exact transportBetween_orbit_tendsto_one_uniform_after_of_H1a
    m p₀ hm hcrit hthird hnonconstant hExcess
    (fun k : ℕ ↦ ⌊t₀ * (scale k : ℝ)⌋₊)
    (natFloor_mul_cofinal_tendsto_atTop scale hscale t₀ ht₀)

/-- The terminal transport weights in the discrete Duhamel sum converge
uniformly to one over every fixed positive floor window. -/
theorem terminalTransportWeight_orbit_natFloor_window_uniform_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (scale : ℕ → ℕ) (hscale : Tendsto scale atTop atTop)
    (t₀ t : ℝ) (ht₀ : 0 < t₀) (_hwindow : t₀ ≤ t) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∀ s ∈
        Finset.Ico ⌊t₀ * (scale k : ℝ)⌋₊ ⌊t * (scale k : ℝ)⌋₊,
          |terminalTransportWeight
            (fun i ↦ transportCoeff m (orbit m p₀ i)) s
              ⌊t * (scale k : ℝ)⌋₊ - 1| < ε := by
  intro ε hε
  have huniform := transportBetween_orbit_uniform_on_natFloor_window_of_H1a
    m p₀ hm hcrit hthird hnonconstant hExcess scale hscale t₀ ht₀ ε hε
  filter_upwards [huniform] with k hk
  intro s hs
  have hlower : ⌊t₀ * (scale k : ℝ)⌋₊ ≤ s + 1 :=
    (Finset.mem_Ico.mp hs).1.trans (Nat.le_succ s)
  have hupper : s + 1 ≤ ⌊t * (scale k : ℝ)⌋₊ :=
    Nat.succ_le_iff.mpr (Finset.mem_Ico.mp hs).2
  simpa only [terminalTransportWeight] using
    hk (s + 1) ⌊t * (scale k : ℝ)⌋₊ hlower hupper

end

end DerridaRetaux
