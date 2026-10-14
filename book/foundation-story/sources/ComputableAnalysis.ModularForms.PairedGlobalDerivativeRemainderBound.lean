import ComputableAnalysis.ModularForms.IntegerReciprocalDerivativeRemainderBound

/-! Actual paired derivative remainders and regional inverse-fourth decay. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedGlobalDerivativeRemainder (n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) : Scalar :=
  scalarSum (integerReciprocalDerivativeRemainder (-((n+1:Nat):Int)) a z ha hz)
    (integerReciprocalDerivativeRemainder ((n+1:Nat):Int) a z ha hz)

theorem pairedGlobalDerivativeRemainder_bound (n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (H M : Rat) (hH : 0≤H) (hM : 0≤M) (hd : Small (sub z.val a.val) H)
    (ham : Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval a ha).val M)
    (haz : Small ((integerReciprocalMap ((n+1:Nat):Int)).eval a ha).val M)
    (hzm : Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval z hz).val M)
    (hzz : Small ((integerReciprocalMap ((n+1:Nat):Int)).eval z hz).val M) :
    Small (pairedGlobalDerivativeRemainder n a z ha hz).val (192*M*M*M*M*H*H) := by
  exact (LocalODE.small_add
    (integerReciprocalDerivativeRemainder_bound _ a z ha hz H M hH hM hd ham hzm)
    (integerReciprocalDerivativeRemainder_bound _ a z ha hz H M hH hM hd haz hzz)).mono (by grind only)

theorem pairedGlobalDerivativeRemainder_regional_bound (n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R H : Rat) (hR : 0≤R) (hH : 0≤H)
    (has : Small a.val R) (hzs : Small z.val R) (hd : Small (sub z.val a.val) H)
    (hlarge : 16*R*R≤pairedIntegerSquare (n+1)) (hRn : R≤((n+1:Nat):Rat)) :
    Small (pairedGlobalDerivativeRemainder n a z ha hz).val
      (12582912*(1/((n+1:Nat):Rat))*(1/((n+1:Nat):Rat))*
        (1/((n+1:Nat):Rat))*(1/((n+1:Nat):Rat))*H*H) := by
  have ham := upperIntegerReciprocal_minus_bound a ha R hR has (n+1) (by omega) hlarge hRn
  have hap := upperIntegerReciprocal_plus_bound a ha R hR has (n+1) (by omega) hlarge hRn
  have hzm := upperIntegerReciprocal_minus_bound z hz R hR hzs (n+1) (by omega) hlarge hRn
  have hzp := upperIntegerReciprocal_plus_bound z hz R hR hzs (n+1) (by omega) hlarge hRn
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hM : 0≤16*(1/((n+1:Nat):Rat)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  exact (pairedGlobalDerivativeRemainder_bound n a z ha hz H _ hH hM hd ham hap hzm hzp).mono (by grind only)

end ComputableAnalysis.ModularForms
