import ComputableAnalysis.ModularForms.IntegerPowerFiniteRowDerivative
import ComputableAnalysis.ModularForms.UpperPowerRemainderBounds
import ComputableAnalysis.RiemannHilbert.DomainDerivativeOverlap

/-! Quantitative remainders for actual integer reciprocal-power maps. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem integerVector_nonzero (l : Int) :
    (⟨l,1⟩ : QuadraticOrder163)≠QuadraticOrder163.zero := by
  intro h
  have hi := congrArg QuadraticOrder163.y h
  change (1:Int)=0 at hi
  omega

theorem integerReciprocalPowerMap_lattice_eval (l : Int) (k : Nat)
    (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalPowerMap l k).eval z hz).val=
      ((latticePowerMap ⟨l,1⟩ (integerVector_nonzero l) k).eval z hz).val := rfl

theorem integerReciprocalPowerMap_lattice_derivative (l : Int) (k : Nat)
    (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalPowerMap_holomorphic l k).derivative z hz).val.Equiv
      ((latticePowerMap_holomorphic ⟨l,1⟩ (integerVector_nonzero l) k).derivative z hz).val :=
  (integerReciprocalPowerMap_holomorphic l k).derivative_equiv_on_overlap
    (latticePowerMap_holomorphic ⟨l,1⟩ (integerVector_nonzero l) k)
    (fun z hz _ => equiv_refl _ ((integerReciprocalPowerMap l k).eval z hz).property) z hz hz

theorem integerReciprocalPowerMap_remainder_bound (l : Int) (k : Nat)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hIa : Small ((integerReciprocalMap l).eval a ha).val M)
    (hIz : Small ((integerReciprocalMap l).eval z hz).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (remainder (integerReciprocalPowerMap l k) a ha
      ((integerReciprocalPowerMap_holomorphic l k).derivative a ha) z hz)
      (powerRemainderCoefficient M k*H*H) := by
  have hs : Small (ofQComplex ⟨(1:Rat),0⟩) 1 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro n m; change (-1:Rat)≤1; decide +kernel
    · intro n m; change (1:Rat)≤1; decide +kernel
    · intro n m; change (-1:Rat)≤0; decide +kernel
    · intro n m; change (0:Rat)≤1; decide +kernel
  have hb : Small (latticePowerRemainder ⟨l,1⟩ (integerVector_nonzero l) a z ha hz k)
      (powerRemainderCoefficient M k*1*1*H*H) := latticePower_remainder_bound ⟨l,1⟩ (integerVector_nonzero l) a z ha hz
    M 1 H hM (by decide) hH hIa hIz hs hd k
  have hD := integerReciprocalPowerMap_lattice_derivative l k a ha
  have he : (remainder (integerReciprocalPowerMap l k) a ha
      ((integerReciprocalPowerMap_holomorphic l k).derivative a ha) z hz).Equiv
      (latticePowerRemainder ⟨l,1⟩ (integerVector_nonzero l) a z ha hz k) :=
    FunctionTheory.sub_congr
      (equiv_refl _ (sub_valid ((integerReciprocalPowerMap l k).eval z hz).property
        ((integerReciprocalPowerMap l k).eval a ha).property))
      (mul_equiv ((integerReciprocalPowerMap_holomorphic l k).derivative a ha).property
        ((latticePowerMap_holomorphic ⟨l,1⟩ (integerVector_nonzero l) k).derivative a ha).property
        (sub_valid z.property a.property) (sub_valid z.property a.property) hD
        (equiv_refl _ (sub_valid z.property a.property)))
  have h := Small.congr (latticePowerRemainder_valid ⟨l,1⟩ (integerVector_nonzero l) a z ha hz k)
    (DomainFunctions.remainder_valid (integerReciprocalPowerMap l k) a ha
      ((integerReciprocalPowerMap_holomorphic l k).derivative a ha) z hz) (equiv_symm he) hb
  simpa only [Rat.mul_one] using h

private theorem double_quadratic (c H : Rat) : c*H*H+c*H*H=2*c*H*H := by grind only

theorem pairedIntegerPowerMap_remainder_bound (k n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (M H : Rat) (hM : 0≤M) (hH : 0≤H)
    (hAm : Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval a ha).val M)
    (hAp : Small ((integerReciprocalMap ((n+1:Nat):Int)).eval a ha).val M)
    (hZm : Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval z hz).val M)
    (hZp : Small ((integerReciprocalMap ((n+1:Nat):Int)).eval z hz).val M)
    (hd : Small (sub z.val a.val) H) :
    Small (DomainFunctions.remainder (pairedIntegerPowerMap k n) a ha
      ((pairedIntegerPowerMap_holomorphic k n).derivative a ha) z hz)
      (2*powerRemainderCoefficient M k*H*H) := by
  have hm := integerReciprocalPowerMap_remainder_bound (-((n+1:Nat):Int)) k a z ha hz M H hM hH hAm hZm hd
  have hp := integerReciprocalPowerMap_remainder_bound ((n+1:Nat):Int) k a z ha hz M H hM hH hAp hZp hd
  have h := LocalODE.small_add hm hp
  have he := sum_remainder (integerReciprocalPowerMap (-((n+1:Nat):Int)) k)
    (integerReciprocalPowerMap ((n+1:Nat):Int) k)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) a ha
    ((integerReciprocalPowerMap_holomorphic (-((n+1:Nat):Int)) k).derivative a ha)
    ((integerReciprocalPowerMap_holomorphic ((n+1:Nat):Int) k).derivative a ha) z hz
  have hh := Small.congr
    (add_valid (DomainFunctions.remainder_valid (integerReciprocalPowerMap (-((n+1:Nat):Int)) k) a ha
      ((integerReciprocalPowerMap_holomorphic (-((n+1:Nat):Int)) k).derivative a ha) z hz)
      (DomainFunctions.remainder_valid (integerReciprocalPowerMap ((n+1:Nat):Int) k) a ha
        ((integerReciprocalPowerMap_holomorphic ((n+1:Nat):Int) k).derivative a ha) z hz))
    (DomainFunctions.remainder_valid (pairedIntegerPowerMap k n) a ha
      ((pairedIntegerPowerMap_holomorphic k n).derivative a ha) z hz) (equiv_symm he) h
  have hr : powerRemainderCoefficient M k*H*H+powerRemainderCoefficient M k*H*H=
      2*powerRemainderCoefficient M k*H*H := double_quadratic _ _
  rw [hr] at hh
  exact hh

end ComputableAnalysis.ModularForms
