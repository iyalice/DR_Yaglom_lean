import DerridaRetaux.Analysis.GluedCompactBox
import Mathlib.Tactic

set_option autoImplicit false

open Filter Set Topology

namespace DerridaRetaux

noncomputable section

/-- Continuity on every bounded box upgrades to continuity on the whole
closed positive half-strip. -/
theorem continuousOn_positiveHalfStrip_of_compactBoxes
    (f : ℝ × ℝ → ℝ) (eta : ℝ)
    (hbox : ∀ T R : ℝ, eta ≤ T → 0 ≤ R →
      ContinuousOn f (Icc eta T ×ˢ Icc (0 : ℝ) R)) :
    ContinuousOn f (Ici eta ×ˢ Ici (0 : ℝ)) := by
  intro p hp
  let T : ℝ := p.1 + 1
  let R : ℝ := p.2 + 1
  have hetaT : eta ≤ T := hp.1.trans (le_add_of_nonneg_right zero_le_one)
  have hR : 0 ≤ R := hp.2.trans (le_add_of_nonneg_right zero_le_one)
  have hpbox : p ∈ Icc eta T ×ˢ Icc (0 : ℝ) R :=
    ⟨⟨hp.1, by dsimp only [T]; linarith⟩,
      ⟨hp.2, by dsimp only [R]; linarith⟩⟩
  have heq : (Ici eta ×ˢ Ici (0 : ℝ)) =ᶠ[𝓝 p]
      (Icc eta T ×ˢ Icc (0 : ℝ) R) := by
    filter_upwards [prod_mem_nhds
      (Iio_mem_nhds (show p.1 < T by dsimp only [T]; linarith))
      (Iio_mem_nhds (show p.2 < R by dsimp only [R]; linarith))] with q hq
    apply propext
    constructor
    · intro hqstrip
      exact ⟨⟨hqstrip.1, hq.1.le⟩, ⟨hqstrip.2, hq.2.le⟩⟩
    · intro hqbox
      exact ⟨hqbox.1.1, hqbox.2.1⟩
  rw [continuousWithinAt_congr_set heq]
  exact (hbox T R hetaT hR).continuousWithinAt hpbox

end

end DerridaRetaux
