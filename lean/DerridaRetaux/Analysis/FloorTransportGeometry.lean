import DerridaRetaux.Analysis.TimeRiemannLimit
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace DerridaRetaux

/-- Arithmetic of the transported lattice index in the Duhamel sum. -/
theorem floorTransportGeometry
    (N s : ℕ) (t₀ t x δ : ℝ) (R : ℕ)
    (hN : 0 < N) (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hx : 0 < x)
    (hR : x + t + 1 ≤ (R : ℝ))
    (hinvT : (N : ℝ)⁻¹ < t₀ / 2)
    (hinvX : (N : ℝ)⁻¹ < x / 2)
    (hinvδ : (N : ℝ)⁻¹ < δ / 3)
    (hs : s ∈ Finset.Ico (gridIndex N t₀) (gridIndex N t)) :
    let k := gridIndex N x + (gridIndex N t - 1 - s)
    let st := (s : ℝ) / (N : ℝ)
    let y := x + t - st
    t₀ / 2 ≤ st ∧ st ≤ t ∧
      x / 2 * (N : ℝ) ≤ (k : ℝ) ∧ k ≤ R * N ∧
      dist ((k : ℝ) / (N : ℝ)) y < δ := by
  dsimp only
  let a : ℕ := gridIndex N t₀
  let b : ℕ := gridIndex N t
  let j : ℕ := gridIndex N x
  let q : ℕ := b - 1 - s
  let k : ℕ := j + q
  let st : ℝ := (s : ℝ) / (N : ℝ)
  let y : ℝ := x + t - st
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hfloorA := gridIndex_div_floor_bounds N t₀ hN ht₀.le
  have hfloorB := gridIndex_div_floor_bounds N t hN (ht₀.le.trans ht)
  have hfloorJ := gridIndex_div_floor_bounds N x hN hx.le
  have has : a ≤ s := by simpa only [a, b] using (Finset.mem_Ico.mp hs).1
  have hsb : s < b := by simpa only [a, b] using (Finset.mem_Ico.mp hs).2
  have hstLower : t₀ / 2 ≤ st := by
    have haLower : t₀ - (N : ℝ)⁻¹ < (a : ℝ) / (N : ℝ) := by
      linarith [hfloorA.2]
    have hasReal : (a : ℝ) / (N : ℝ) ≤ st := by
      dsimp only [st]
      exact div_le_div_of_nonneg_right (by exact_mod_cast has) hNreal.le
    linarith
  have hstUpper : st ≤ t := by
    have hsbCast : (s : ℝ) / (N : ℝ) ≤ (b : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsb.le) hNreal.le
    exact hsbCast.trans hfloorB.1
  have hjLower : x / 2 ≤ (j : ℝ) / (N : ℝ) := by
    have hjRaw : x - (N : ℝ)⁻¹ < (j : ℝ) / (N : ℝ) := by
      linarith [hfloorJ.2]
    linarith
  have hkLower : x / 2 * (N : ℝ) ≤ (k : ℝ) := by
    exact (le_div_iff₀ hNreal).mp (hjLower.trans
      (div_le_div_of_nonneg_right (by
        dsimp only [k]
        push_cast
        exact le_add_of_nonneg_right (Nat.cast_nonneg q)) hNreal.le))
  have hkUpper : k ≤ R * N := by
    have hjCast : (j : ℝ) ≤ x * (N : ℝ) := by
      simpa only [j, mul_comm] using gridIndex_cast_le N x hx.le
    have hbCast : (b : ℝ) ≤ t * (N : ℝ) := by
      simpa only [b, mul_comm] using gridIndex_cast_le N t (ht₀.le.trans ht)
    have hqle : q ≤ b :=
      (Nat.sub_le (b - 1) s).trans (Nat.sub_le b 1)
    have hqCast : (q : ℝ) ≤ (b : ℝ) := by exact_mod_cast hqle
    have hkCast : (k : ℝ) ≤ (x + t) * (N : ℝ) := by
      rw [show (k : ℝ) = (j : ℝ) + (q : ℝ) by simp only [k, Nat.cast_add]]
      calc
        (j : ℝ) + (q : ℝ) ≤ x * (N : ℝ) + t * (N : ℝ) :=
          add_le_add hjCast (hqCast.trans hbCast)
        _ = (x + t) * (N : ℝ) := by ring
    have hkReal : (k : ℝ) ≤ ((R * N : ℕ) : ℝ) := by
      push_cast
      exact hkCast.trans (mul_le_mul_of_nonneg_right (by linarith [hR]) hNreal.le)
    exact_mod_cast hkReal
  have hqFormula : (q : ℝ) / (N : ℝ) =
      (b : ℝ) / (N : ℝ) - (N : ℝ)⁻¹ - st := by
    have hsucc : s + 1 ≤ b := Nat.succ_le_iff.mpr hsb
    have hqeq : q = b - (s + 1) := by dsimp only [q]; omega
    rw [hqeq, Nat.cast_sub hsucc]
    push_cast
    dsimp only [st]
    field_simp [hNreal.ne']
    ring
  have hkFormula : (k : ℝ) / (N : ℝ) =
      (j : ℝ) / (N : ℝ) + (b : ℝ) / (N : ℝ) -
        (N : ℝ)⁻¹ - st := by
    dsimp only [k]
    push_cast
    rw [add_div, hqFormula]
    ring
  have hargDist : dist ((k : ℝ) / (N : ℝ)) y < δ := by
    rw [Real.dist_eq, hkFormula]
    dsimp only [y]
    have hjErr : |(j : ℝ) / (N : ℝ) - x| < (N : ℝ)⁻¹ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hfloorJ.1)]
      linarith [hfloorJ.2]
    have hbErr : |(b : ℝ) / (N : ℝ) - t| < (N : ℝ)⁻¹ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hfloorB.1)]
      linarith [hfloorB.2]
    calc
      |(j : ℝ) / (N : ℝ) + (b : ℝ) / (N : ℝ) -
          (N : ℝ)⁻¹ - st - (x + t - st)| ≤
        |(j : ℝ) / (N : ℝ) - x| +
          |(b : ℝ) / (N : ℝ) - t| + (N : ℝ)⁻¹ := by
        rw [show (j : ℝ) / (N : ℝ) + (b : ℝ) / (N : ℝ) -
          (N : ℝ)⁻¹ - st - (x + t - st) =
          ((j : ℝ) / (N : ℝ) - x) +
            ((b : ℝ) / (N : ℝ) - t) - (N : ℝ)⁻¹ by ring]
        calc
          |_ + _ - (N : ℝ)⁻¹| ≤ |_ + _| + |-(N : ℝ)⁻¹| := abs_add _ _
          _ ≤ (|(j : ℝ) / (N : ℝ) - x| +
              |(b : ℝ) / (N : ℝ) - t|) + (N : ℝ)⁻¹ := by
            rw [abs_neg, abs_of_pos (inv_pos.mpr hNreal)]
            gcongr
            exact abs_add _ _
      _ < δ := by linarith
  exact ⟨hstLower, hstUpper, hkLower, hkUpper, hargDist⟩

end DerridaRetaux
