import DerridaRetaux.Main.ContinuumRemainder

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux.FixedArity

noncomputable section

/-- Lemma `lem:remainder`: the exact third-order expansion, its little-o statement, and the
stronger quantitative square-root estimate. -/
theorem thirdOrderTaylorRemainder
    (m : ℕ) (data : ProfileInitialData m)
    (phi : ℕ → ℕ)
    (g : ∀ k, BoundedContinuousFunction (gridExhaustionRectangle k) ℝ)
    (hphi : Tendsto phi atTop atTop)
    (hlim : ∀ k, TendstoUniformly
      (fun n (q : gridExhaustionRectangle k) ↦
        gridBilinearInterp (phi n) (orbitScaledGrid m data.law (phi n))
          (q : ℝ × ℝ).1 (q : ℝ × ℝ).2)
      (fun q ↦ g k q) atTop)
    (p : ℝ) (hp : 0 < p) :
    (∀ t : ℝ, 0 < t →
      subsequentialLaplaceGap g t p =
        (p ^ 2 / 2) * continuumMoment
            (fun x ↦ gluedExhaustionLimit g t x) 2 -
          (p ^ 3 / 6) * continuumMoment
            (fun x ↦ gluedExhaustionLimit g t x) 3 +
          subsequentialThirdRemainder g t p) ∧
    Tendsto
      (fun t : ℝ ↦ subsequentialThirdRemainder g t p /
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      |subsequentialThirdRemainder g t p /
        continuumMoment (fun x ↦ gluedExhaustionLimit g t x) 3| ≤
          K * Real.sqrt t := by
  refine ⟨?_, subsequentialThirdRemainder_normalized_tendsto_zero
    m data phi g hphi hlim p hp.le, ?_⟩
  · intro t ht
    exact subsequentialLaplaceGap_taylor m data phi g hphi hlim ht hp.le
  · obtain ⟨K, hK, hbound⟩ :=
      subsequentialThirdRemainder_normalized_le_sqrt
        m data phi g hphi hlim p hp.le
    exact ⟨K, hK, fun t ht _ ↦ hbound t ht⟩

end

end DerridaRetaux.FixedArity
