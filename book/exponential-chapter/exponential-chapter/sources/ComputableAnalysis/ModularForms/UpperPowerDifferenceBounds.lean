import ComputableAnalysis.ModularForms.UpperReciprocalDifference

/-! Executable coefficient bounds for inverse-power first differences. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def powerDifferenceCoefficient (B : Rat) : Nat → Rat
  | 0 => 0
  | k+1 => 2*B*powerDifferenceCoefficient B k+16*B*B*(2*B)^k

theorem powerDifferenceCoefficient_nonnegative (B : Rat) (hB : 0≤B) (k : Nat) :
    0≤powerDifferenceCoefficient B k := by
  induction k with
  | zero => exact Rat.le_refl
  | succ k ih =>
    change 0≤2*B*powerDifferenceCoefficient B k+16*B*B*(2*B)^k
    exact Rat.add_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) ih)
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hB)
        (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hB)))

theorem latticePower_difference_bound (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (B T H : Rat) (hB : 0≤B) (hT : 0≤T) (hH : 0≤H)
    (hRa : Small (latticeInverse a ha u hu).val B)
    (hRz : Small (latticeInverse z hz u hu).val B)
    (hTs : Small (ofQComplex ⟨(u.y:Rat),0⟩) T)
    (hza : Small (sub z.val a.val) H) (k : Nat) :
    Small (sub (LocalODE.power (latticeInverse z hz u hu).val k)
      (LocalODE.power (latticeInverse a ha u hu).val k)) (powerDifferenceCoefficient B k*T*H) := by
  induction k with
  | zero =>
    have he : (sub (ofQComplex QComplex.one) (ofQComplex QComplex.one)).Equiv ComplexRaw.zero := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (ofQComplex_valid _) (ofQComplex_valid _)) (hright := ofQComplex_valid _)
      change (1:ScalarAlgebra.Value) + -1=0
      grind only
    have hb := Small.congr (ofQComplex_valid _) (sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
      (equiv_symm he) (Small.zero (by decide : (0:Rat)≤0))
    simp only [powerDifferenceCoefficient,Rat.zero_mul,LocalODE.power]
    change Small (sub (ofQComplex QComplex.one) (ofQComplex QComplex.one)) 0
    exact hb
  | succ k ih =>
    have hD := Rat.mul_nonneg (Rat.mul_nonneg (powerDifferenceCoefficient_nonnegative B hB k) hT) hH
    have hP := Rat.pow_nonneg (Rat.mul_nonneg (by decide : (0:Rat)≤2) hB) (n := k)
    have hE : 0≤8*B*B*T*H := Rat.mul_nonneg
      (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hB) hT) hH
    have hleft := Small.mul
      (sub_valid (LocalODE.power_valid _ (latticeInverse z hz u hu).property k)
        (LocalODE.power_valid _ (latticeInverse a ha u hu).property k))
      (latticeInverse z hz u hu).property hD hB ih hRz
    have hright := Small.mul (LocalODE.power_valid _ (latticeInverse a ha u hu).property k)
      (sub_valid (latticeInverse z hz u hu).property (latticeInverse a ha u hu).property) hP hE
      (LocalODE.power_small _ (latticeInverse a ha u hu).property B hB hRa k)
      (latticeReciprocal_difference_bound u hu a z ha hz B T H hB hT hH hRa hRz hTs hza)
    have hb := LocalODE.small_add hleft hright
    have he : 2*(powerDifferenceCoefficient B k*T*H)*B+2*(2*B)^k*(8*B*B*T*H)=
        powerDifferenceCoefficient B (k+1)*T*H := by
      rw [powerDifferenceCoefficient]
      grind only
    rw [he] at hb
    exact Small.congr
      (add_valid (mul_valid
        (sub_valid (LocalODE.power_valid _ (latticeInverse z hz u hu).property k)
          (LocalODE.power_valid _ (latticeInverse a ha u hu).property k)) (latticeInverse z hz u hu).property)
        (mul_valid (LocalODE.power_valid _ (latticeInverse a ha u hu).property k)
          (sub_valid (latticeInverse z hz u hu).property (latticeInverse a ha u hu).property)))
      (sub_valid (LocalODE.power_valid _ (latticeInverse z hz u hu).property (k+1))
        (LocalODE.power_valid _ (latticeInverse a ha u hu).property (k+1)))
      (equiv_symm (latticePower_difference_succ u hu a z ha hz k)) hb

end ComputableAnalysis.ModularForms
