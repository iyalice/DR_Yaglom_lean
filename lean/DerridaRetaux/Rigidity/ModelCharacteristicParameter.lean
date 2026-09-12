import DerridaRetaux.Rigidity.ModelCharacteristicFinal

set_option autoImplicit false

open Real

namespace DerridaRetaux

noncomputable section

/-- Reparameterization of the explicit model characteristic from `p > 0` to
the whole negative spectral axis. -/
theorem modelEntranceString_hasSingularCharacteristic_of_neg
    {d lambda : ℝ} (hd : 0 < d) (hlambda : lambda < 0) :
    HasSingularCharacteristic (modelEntranceString d) lambda
      (-d * Real.sqrt (-lambda)) := by
  let p : ℝ := 2 * Real.sqrt (-lambda)
  have hneg : 0 < -lambda := neg_pos.mpr hlambda
  have hp : 0 < p := mul_pos (by norm_num) (Real.sqrt_pos.2 hneg)
  have hlambdaEq : lambda = -(p ^ 2 / 4) := by
    have hsqrt : (Real.sqrt (-lambda)) ^ 2 = -lambda := Real.sq_sqrt hneg.le
    dsimp only [p]
    nlinarith
  have h := modelEntranceString_hasSingularCharacteristic (d := d) (p := p) hd hp
  rw [← hlambdaEq] at h
  convert h using 1 <;> dsimp only [p] <;> ring

/-- Source-normalized model scale `d=2κ/3`. -/
theorem sourceModelEntranceString_hasSingularCharacteristic
    {κ lambda : ℝ} (hκ : 0 < κ) (hlambda : lambda < 0) :
    HasSingularCharacteristic (modelEntranceString (2 * κ / 3)) lambda
      (-(2 * κ / 3) * Real.sqrt (-lambda)) := by
  exact modelEntranceString_hasSingularCharacteristic_of_neg
    (div_pos (mul_pos (by norm_num) hκ) (by norm_num)) hlambda

end

end DerridaRetaux
