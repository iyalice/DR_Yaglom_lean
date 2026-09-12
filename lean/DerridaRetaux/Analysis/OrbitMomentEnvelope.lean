import DerridaRetaux.Analysis.OrbitMomentBound

set_option autoImplicit false

namespace DerridaRetaux

noncomputable section

/-- A pointwise weighted-`l1` estimate gives the exact envelope used to pass
the zeroth, second, and third moment bounds to a continuum limit. -/
theorem orbit_scaledDiscreteMoment_le_envelope
    (m : ℕ) (p₀ : ProbabilityMass) (hm : 2 ≤ m)
    (hcrit : Critical m p₀) (hthird : TiltSummable m 3 p₀)
    (A : ℝ)
    (hL1 : ∀ s : ℕ,
      weightedL1Three (profileScale s)
          (positiveTiltedDensity m (orbit m p₀ s)) ≤
        A / profileScale s)
    (N s r : ℕ) (hN : 0 < N) (hr : r ≤ 3) :
    scaledDiscreteMoment
        (positiveTiltedDensity m (orbit m p₀ s)) r N ≤
      ((N : ℝ) / (N : ℝ) ^ r) *
        (profileScale s ^ r * (A / profileScale s)) := by
  have hscrit := orbit_critical m p₀ (by omega) hcrit s
  have hsthird := orbit_tiltSummable_three
    m p₀ (by omega) hcrit hthird s
  have hrho : ∀ j : ℕ,
      0 ≤ positiveTiltedDensity m (orbit m p₀ s) j :=
    positiveTiltedDensity_nonneg m (orbit m p₀ s) (by omega) hscrit
  have hmoment : Summable (fun j : ℕ ↦
      (j : ℝ) ^ r * positiveTiltedDensity m (orbit m p₀ s) j) := by
    have hzero := (positiveTiltedDensity_hasSum
      m (orbit m p₀ s) (by omega) hscrit).summable
    have hthree := positiveTiltedDensity_third_summable
      m (orbit m p₀ s) (by omega) hscrit hsthird
    exact moment_summable_of_zero_and_third _ r hr hrho hzero hthree
  have hweighted := weightedAbs_positiveTiltedDensity_orbit_summable
    m p₀ hm hcrit hthird s
  have hraw := scaledDiscreteMoment_le_weightedL1
    (positiveTiltedDensity m (orbit m p₀ s)) r N (profileScale s)
      hr hN (by unfold profileScale; positivity) hrho hmoment hweighted
  exact hraw.trans <| mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hL1 s) (pow_nonneg (by unfold profileScale; positivity) r))
    (by positivity)

end

end DerridaRetaux
