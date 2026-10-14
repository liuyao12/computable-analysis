import ComputableAnalysis.ModularForms.IntegerPowerSquareRows
import ComputableAnalysis.ModularForms.IntegerReciprocalTranslation

/-! Integer translation of actual reciprocal-power prefixes and its boundary defect. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem integerReciprocalPowerMap_translation (z : Scalar)
    (hz : InUpperHalfPlane z.val) (j l : Int) (k : Nat) :
    ((integerReciprocalPowerMap l k).eval (integerShiftScalar z j)
      (integerShiftScalar_upper z hz j)).val.Equiv
      ((integerReciprocalPowerMap (j+l) k).eval z hz).val :=
  LocalODE.power_congr _ _
    (upperIntegerReciprocal (integerShiftScalar z j) (integerShiftScalar_upper z hz j) l).property
    (upperIntegerReciprocal z hz (j+l)).property (upperIntegerReciprocal_translation z hz j l) k

def integerReciprocalPowerClass (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (l : Int) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw ((integerReciprocalPowerMap l k).eval z hz).val
    ((integerReciprocalPowerMap l k).eval z hz).property

theorem integerReciprocalPowerClass_translation (z : Scalar)
    (hz : InUpperHalfPlane z.val) (j l : Int) (k : Nat) :
    integerReciprocalPowerClass (integerShiftScalar z j) (integerShiftScalar_upper z hz j) k l =
      integerReciprocalPowerClass z hz k (j+l) :=
  ComplexRawQuotient.ofRaw_eq_ofRaw (integerReciprocalPowerMap_translation z hz j l k)

theorem integerPowerRowPrefix_class (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k N : Nat) :
    ComplexRawQuotient.ofRaw (integerPowerRowPrefix z hz k N)
      (integerPowerRowPrefix_valid z hz k N) =
      symmetricLatticeSum (integerReciprocalPowerClass z hz k) N := by
  induction N with
  | zero =>
    change integerReciprocalPowerClass z hz k 0+0=integerReciprocalPowerClass z hz k 0
    grind only
  | succ N ih =>
    let I := integerReciprocalPowerClass z hz k 0
    let P := ComplexRawQuotient.ofRaw
      (ScalarSeries.block (fun n => (upperPairedIntegerPower z hz k (n+1)).val) 0 N)
      (ScalarSeries.block_valid _ (fun n => (upperPairedIntegerPower z hz k (n+1)).property) 0 N)
    change I+P=symmetricLatticeSum (integerReciprocalPowerClass z hz k) N at ih
    simp only [integerPowerRowPrefix,ScalarSeries.block.eq_2,Nat.zero_add,symmetricLatticeSum.eq_2]
    change I+(P+(integerReciprocalPowerClass z hz k (-((N+1:Nat):Int))+
      integerReciprocalPowerClass z hz k ((N+1:Nat):Int)))=
      symmetricLatticeSum (integerReciprocalPowerClass z hz k) N+
      integerReciprocalPowerClass z hz k (-((N+1:Nat):Int))+
      integerReciprocalPowerClass z hz k ((N+1:Nat):Int)
    rw [← ih]
    grind only

theorem integerPowerRowPrefix_translation_defect (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k N : Nat) :
    ComplexRawQuotient.ofRaw
      (integerPowerRowPrefix (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1) k N)
      (integerPowerRowPrefix_valid _ _ k N)-
    ComplexRawQuotient.ofRaw (integerPowerRowPrefix z hz k N)
      (integerPowerRowPrefix_valid z hz k N)=
      integerReciprocalPowerClass z hz k ((N:Int)+1)-
      integerReciprocalPowerClass z hz k (-(N:Int)) := by
  rw [integerPowerRowPrefix_class,integerPowerRowPrefix_class]
  have hf : integerReciprocalPowerClass (integerShiftScalar z 1)
      (integerShiftScalar_upper z hz 1) k=(fun l => integerReciprocalPowerClass z hz k (l+1)) := by
    funext l
    rw [integerReciprocalPowerClass_translation z hz 1 l k]
    congr 1
    omega
  rw [hf]
  exact symmetricLatticeSum_shift _ N

theorem integerReciprocalPower_boundary_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (R : Rat) (hR : 0≤R) (hsmall : Small z.val R)
    (k n : Nat) (hk : 2≤k) (hn : 0<n)
    (hlarge : 16*R*R≤pairedIntegerSquare n) (hRn : R≤(n:Rat)) :
    Small ((integerReciprocalPowerMap (n:Int) k).eval z hz).val
      ((32:Rat)^k*reciprocalSquare n) ∧
    Small ((integerReciprocalPowerMap (-(n:Int)) k).eval z hz).val
      ((32:Rat)^k*reciprocalSquare n) := by
  have hnR : (0:Rat)<(n:Rat) := by exact_mod_cast hn
  have hM : 0≤16*(1/(n:Rat)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hnR))
  have he : 2*(16*(1/(n:Rat)))=32*(n:Rat)⁻¹ := by
    rw [Rat.div_def,Rat.one_mul]
    grind only
  have hb := Rat.mul_le_mul_of_nonneg_left (reciprocal_integer_power_le_square n k hn hk)
    (Rat.pow_nonneg (a := (32:Rat)) (n := k) (by decide))
  constructor
  · have h := LocalODE.power_small _ (upperIntegerReciprocal z hz (n:Int)).property _ hM
      (upperIntegerReciprocal_plus_bound z hz R hR hsmall n hn hlarge hRn) k
    rw [he,LocalODE.rational_mul_pow] at h
    exact h.mono hb
  · have h := LocalODE.power_small _ (upperIntegerReciprocal z hz (-(n:Int))).property _ hM
      (upperIntegerReciprocal_minus_bound z hz R hR hsmall n hn hlarge hRn) k
    rw [he,LocalODE.rational_mul_pow] at h
    exact h.mono hb

end ComputableAnalysis.ModularForms
