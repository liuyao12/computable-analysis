import ComputableAnalysis.ModularForms.UpperPowerDifferenceBounds

/-! Constructed quadratic remainder coefficients for all inverse powers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def powerRemainderCoefficient (B : Rat) : Nat → Rat
  | 0 => 0
  | k+1 => 2*B*powerRemainderCoefficient B k+128*B*B*B*(2*B)^k+
      16*B*B*powerDifferenceCoefficient B k

theorem powerRemainderCoefficient_nonnegative (B : Rat) (hB : 0≤B) (k : Nat) :
    0≤powerRemainderCoefficient B k := by
  induction k with
  | zero => exact Rat.le_refl
  | succ k ih =>
    change 0≤2*B*powerRemainderCoefficient B k+128*B*B*B*(2*B)^k+16*B*B*powerDifferenceCoefficient B k
    exact Rat.add_nonneg (Rat.add_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) ih)
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hB) hB)
        (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hB))))
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hB)
        (powerDifferenceCoefficient_nonnegative B hB k))

theorem latticePower_remainder_bound (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B T H : Rat) (hB : 0≤B) (hT : 0≤T) (hH : 0≤H)
    (hRa : Small (latticeInverse a ha u hu).val B)
    (hRz : Small (latticeInverse z hz u hu).val B)
    (hTs : Small (ofQComplex ⟨(u.y:Rat),0⟩) T)
    (hza : Small (sub z.val a.val) H) (k : Nat) :
    Small (latticePowerRemainder u hu a z ha hz k) (powerRemainderCoefficient B k*T*T*H*H) := by
  induction k with
  | zero =>
    have hb := Small.congr (ofQComplex_valid _) (latticePowerRemainder_valid u hu a z ha hz 0)
      (equiv_symm (latticePowerRemainder_zero u hu a z ha hz)) (Small.zero (by decide : (0:Rat)≤0))
    simpa only [powerRemainderCoefficient,Rat.zero_mul] using hb
  | succ k ih =>
    let ra := latticeInverse a ha u hu
    let rz := latticeInverse z hz u hu
    let recRem := DomainFunctions.remainder (latticeReciprocalMap u hu) a ha
      ((latticeReciprocalMap_holomorphic u hu).derivative a ha) z hz
    have hK : 0≤powerRemainderCoefficient B k*T*T*H*H :=
      Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
        (powerRemainderCoefficient_nonnegative B hB k) hT) hT) hH) hH
    have hD : 0≤powerDifferenceCoefficient B k*T*H :=
      Rat.mul_nonneg (Rat.mul_nonneg (powerDifferenceCoefficient_nonnegative B hB k) hT) hH
    have hE : 0≤8*B*B*T*H := Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hB) hT) hH
    have hR : 0≤64*B*B*B*T*T*H*H := Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
        (by decide) hB) hB) hB) hT) hT) hH) hH
    have hP := Rat.pow_nonneg (Rat.mul_nonneg (by decide : (0:Rat)≤2) hB) (n := k)
    have hleft := Small.mul (latticePowerRemainder_valid u hu a z ha hz k) ra.property hK hB ih hRa
    have hright := Small.mul (LocalODE.power_valid ra.val ra.property k)
      (DomainFunctions.remainder_valid _ _ _ _ _ _) hP hR
      (LocalODE.power_small ra.val ra.property B hB hRa k)
      (latticeReciprocal_remainder_bound u hu a z ha hz B T H hB hT hH hRa hRz hTs hza)
    have hcross := Small.mul (sub_valid (LocalODE.power_valid rz.val rz.property k)
      (LocalODE.power_valid ra.val ra.property k)) (sub_valid rz.property ra.property) hD hE
      (latticePower_difference_bound u hu a z ha hz B T H hB hT hH hRa hRz hTs hza k)
      (latticeReciprocal_difference_bound u hu a z ha hz B T H hB hT hH hRa hRz hTs hza)
    have hb := LocalODE.small_add (LocalODE.small_add hleft hright) hcross
    have he : (2*(powerRemainderCoefficient B k*T*T*H*H)*B+
        2*(2*B)^k*(64*B*B*B*T*T*H*H))+2*(powerDifferenceCoefficient B k*T*H)*(8*B*B*T*H)=
        powerRemainderCoefficient B (k+1)*T*T*H*H := by
      rw [powerRemainderCoefficient]
      grind only
    rw [he] at hb
    exact Small.congr
      (add_valid (add_valid (mul_valid (latticePowerRemainder_valid u hu a z ha hz k) ra.property)
        (mul_valid (LocalODE.power_valid ra.val ra.property k) (DomainFunctions.remainder_valid _ _ _ _ _ _)))
        (mul_valid (sub_valid (LocalODE.power_valid rz.val rz.property k)
          (LocalODE.power_valid ra.val ra.property k)) (sub_valid rz.property ra.property)))
      (latticePowerRemainder_valid u hu a z ha hz (k+1))
      (equiv_symm (latticePowerRemainder_succ u hu a z ha hz k)) hb

private theorem ratMulPower (x y : Rat) (k : Nat) : (x*y)^k=x^k*y^k := by
  induction k with
  | zero => simp only [Rat.pow_zero,Rat.one_mul]
  | succ k ih => simp only [Rat.pow_succ,ih]; grind only

theorem powerDifferenceCoefficient_scale (B s : Rat) (k : Nat) :
    powerDifferenceCoefficient (B*s) k=powerDifferenceCoefficient B k*s^(k+1) := by
  induction k with
  | zero => simp only [powerDifferenceCoefficient,Rat.zero_mul]
  | succ k ih =>
    rw [powerDifferenceCoefficient,powerDifferenceCoefficient,ih]
    have hp : (2*(B*s))^k=(2*B)^k*s^k := by
      have he : 2*(B*s)=(2*B)*s := by grind
      rw [he,ratMulPower]
    rw [hp]
    simp only [Rat.pow_succ]
    grind only

theorem powerRemainderCoefficient_scale (B s : Rat) (k : Nat) :
    powerRemainderCoefficient (B*s) k=powerRemainderCoefficient B k*s^(k+2) := by
  induction k with
  | zero => simp only [powerRemainderCoefficient,Rat.zero_mul]
  | succ k ih =>
    rw [powerRemainderCoefficient,powerRemainderCoefficient,ih,powerDifferenceCoefficient_scale]
    have hp : (2*(B*s))^k=(2*B)^k*s^k := by
      have he : 2*(B*s)=(2*B)*s := by grind
      rw [he,ratMulPower]
    rw [hp]
    simp only [Rat.pow_succ]
    grind only

end ComputableAnalysis.ModularForms
