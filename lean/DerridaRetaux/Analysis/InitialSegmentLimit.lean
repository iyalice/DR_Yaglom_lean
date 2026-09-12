import DerridaRetaux.Analysis.TimeRiemannLimit
import DerridaRetaux.Analysis.SpacetimeMovingReadout
import DerridaRetaux.Analysis.GluedCompactBox
import DerridaRetaux.Analysis.MildCoefficientLimits
import DerridaRetaux.Analysis.TruncatedTelescope

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Limit of the transported homogeneous part of the discrete Duhamel formula. -/
theorem scaled_densityInitialSegment_tendsto_of_H1a
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (hnonconstant : ¬ IsDirac p₀)
    (hExcess : CDHLSExcessFact m p₀ hm hcrit hthird hnonconstant)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (t₀ t x : ℝ) (R : ℕ)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 ≤ x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (p : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m p₀ (phi n))
          (p : ℝ × ℝ).1 (p : ℝ × ℝ).2)
      (fun p ↦ g k p) atTop) :
    Tendsto
      (fun n ↦ (phi n : ℝ) ^ 2 *
        densityInitialSegment m p₀
          (gridIndex (phi n) t₀) (gridIndex (phi n) t)
          (gridIndex (phi n) x))
      atTop (nhds (gluedExhaustionLimit g t₀ (x + t - t₀))) := by
  let a : ℕ → ℕ := fun n ↦ gridIndex (phi n) t₀
  let b : ℕ → ℕ := fun n ↦ gridIndex (phi n) t
  let j : ℕ → ℕ := fun n ↦ gridIndex (phi n) x
  let k : ℕ → ℕ := fun n ↦ j n + (b n - a n)
  let u : ℝ → ℝ → ℝ := gluedExhaustionLimit g
  have htime : Tendsto (fun n ↦ (a n : ℝ) / (phi n : ℝ))
      atTop (nhds t₀) := by
    simpa only [a] using (gridIndex_div_tendsto t₀ ht₀.le).comp hphi
  have hbtime : Tendsto (fun n ↦ (b n : ℝ) / (phi n : ℝ))
      atTop (nhds t) := by
    simpa only [b] using (gridIndex_div_tendsto t (ht₀.le.trans ht)).comp hphi
  have hjspace : Tendsto (fun n ↦ (j n : ℝ) / (phi n : ℝ))
      atTop (nhds x) := by
    simpa only [j] using (gridIndex_div_tendsto x hx).comp hphi
  have hab : ∀ n, a n ≤ b n := by
    intro n
    exact gridIndex_mono_of_nonneg ht₀.le ht (phi n)
  have hkEq : ∀ n, (k n : ℝ) / (phi n : ℝ) =
      (j n : ℝ) / (phi n : ℝ) +
        ((b n : ℝ) / (phi n : ℝ) - (a n : ℝ) / (phi n : ℝ)) := by
    intro n
    dsimp only [k]
    rw [Nat.cast_add, Nat.cast_sub (hab n), add_div, sub_div]
  have hspace : Tendsto (fun n ↦ (k n : ℝ) / (phi n : ℝ))
      atTop (nhds (x + t - t₀)) := by
    have hraw := hjspace.add (hbtime.sub htime)
    have hrawTarget : Tendsto
        (fun n ↦ (j n : ℝ) / (phi n : ℝ) +
          ((b n : ℝ) / (phi n : ℝ) - (a n : ℝ) / (phi n : ℝ)))
        atTop (nhds (x + t - t₀)) := by
      convert hraw using 1 <;> ring
    apply hrawTarget.congr'
    filter_upwards [] with n
    exact (hkEq n).symm
  have heta : 0 < t₀ / 2 := half_pos ht₀
  have hetaT : t₀ / 2 ≤ t + 1 := by linarith
  have hu : ContinuousOn (Function.uncurry u)
      (Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ)) := by
    exact continuousOn_gluedExhaustionLimit_compactBox
      (orbitScaledGrid m p₀) phi g hlim (t₀ / 2) (t + 1) (R : ℝ)
        heta hetaT (Nat.cast_nonneg R)
  have hlocal : LocallyUniformSpacetimeLatticeDensity
      (fun _n s ↦ positiveTiltedDensity m (orbit m p₀ s)) phi u :=
    locallyUniformSpacetimeLatticeDensity_orbit_of_gluedExhaustion
      m p₀ phi g hlim
  have htarget : (t₀, x + t - t₀) ∈
      Icc (t₀ / 2) (t + 1) ×ˢ Icc (0 : ℝ) (R : ℝ) := by
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    constructor
    · change 0 ≤ x + t - t₀
      linarith
    · change x + t - t₀ ≤ (R : ℝ)
      linarith [hR]
  have hindices : ∀ᶠ n : ℕ in atTop,
      t₀ / 2 * (phi n : ℝ) ≤ (a n : ℝ) ∧
      (a n : ℝ) ≤ (t + 1) * (phi n : ℝ) ∧
      k n ≤ R * phi n := by
    have hphiPos : ∀ᶠ n : ℕ in atTop, 0 < phi n := by
      have hge := hphi.eventually_ge_atTop 1
      exact hge.mono fun _ hn ↦ by omega
    have htimeLow : ∀ᶠ n : ℕ in atTop,
        t₀ / 2 ≤ (a n : ℝ) / (phi n : ℝ) :=
      htime (Ici_mem_nhds (by linarith))
    have htimeHigh : ∀ᶠ n : ℕ in atTop,
        (a n : ℝ) / (phi n : ℝ) ≤ t + 1 :=
      htime (Iic_mem_nhds (by linarith))
    have hspaceHigh : ∀ᶠ n : ℕ in atTop,
        (k n : ℝ) / (phi n : ℝ) < (R : ℝ) :=
      hspace (Iio_mem_nhds (by linarith [hR]))
    filter_upwards [hphiPos, htimeLow, htimeHigh, hspaceHigh] with
      n hn htl hth hkh
    have hNreal : (0 : ℝ) < (phi n : ℝ) := by exact_mod_cast hn
    refine ⟨(le_div_iff₀ hNreal).mp htl,
      (div_le_iff₀ hNreal).mp hth, ?_⟩
    have : (k n : ℝ) < ((R * phi n : ℕ) : ℝ) := by
      push_cast
      exact (div_lt_iff₀ hNreal).mp hkh
    exact_mod_cast this.le
  have hreadout : Tendsto
      (fun n ↦ (phi n : ℝ) ^ 2 *
        positiveTiltedDensity m (orbit m p₀ (a n)) (k n))
      atTop (nhds (u t₀ (x + t - t₀))) :=
    spacetimeLatticeDensity_tendsto_moving
      (fun _n s ↦ positiveTiltedDensity m (orbit m p₀ s))
      phi a k u (t₀ / 2) (t + 1) R t₀ (x + t - t₀)
      hphi heta hetaT hlocal hu htarget htime hspace hindices
  have htransport : Tendsto
      (fun n ↦ transportBetween
        (fun s ↦ transportCoeff m (orbit m p₀ s)) (a n) (b n))
      atTop (nhds 1) := by
    simpa only [a, b, gridIndex, max_eq_left ht₀.le,
      max_eq_left (ht₀.le.trans ht), mul_comm] using
      transportBetween_orbit_natFloor_window_tendsto_one_of_H1a
        m p₀ hm hcrit hthird hnonconstant hExcess phi hphi
          t₀ t ht₀ ht
  have hproduct := htransport.mul hreadout
  have hproduct' : Tendsto
      (fun n ↦ transportBetween
        (fun s ↦ transportCoeff m (orbit m p₀ s)) (a n) (b n) *
          ((phi n : ℝ) ^ 2 *
            positiveTiltedDensity m (orbit m p₀ (a n)) (k n)))
      atTop (nhds (u t₀ (x + t - t₀))) := by
    simpa only [one_mul] using hproduct
  apply hproduct'.congr'
  filter_upwards [] with n
  simp only [densityInitialSegment, truncatedInitialTerm,
    Pi.smul_apply, smul_eq_mul, shiftLeft_iterate_apply]
  dsimp only [a, b, j, k]
  ring

end

end DerridaRetaux
