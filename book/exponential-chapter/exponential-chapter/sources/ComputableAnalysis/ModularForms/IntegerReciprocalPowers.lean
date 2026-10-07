import ComputableAnalysis.ModularForms.PairedReciprocalTermHolomorphic

/-! Actual holomorphic integer reciprocal powers and their represented derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def integerReciprocalPowerMap (k : Int) (n : Nat) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨LocalODE.power ((integerReciprocalMap k).eval z hz).val n,
    LocalODE.power_valid _ ((integerReciprocalMap k).eval z hz).property n⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := LocalODE.power_congr _ _
    ((integerReciprocalMap k).eval z hz).property ((integerReciprocalMap k).eval w hw).property
    ((integerReciprocalMap k).eval_congr z w hz hw he) n

def integerReciprocalPowerMap_holomorphic (k : Int) : (n : Nat) → Holomorphic (integerReciprocalPowerMap k n)
  | 0 => (constantOn_holomorphic upperOpenData ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩).transfer
      (integerReciprocalPowerMap k 0) (fun _ hz => hz) ⟨upperRadius,upperRadius_inside⟩
      (fun _ _ => equiv_refl _ (ofQComplex_valid _))
  | n+1 =>
    ((integerReciprocalMap_holomorphic k).productOn (integerReciprocalPowerMap_holomorphic k n)
      (fun _ hz => hz)).transfer (integerReciprocalPowerMap k (n+1)) (fun _ hz => hz)
      ⟨upperRadius,upperRadius_inside⟩ (fun z hz => by
        apply ComplexRawQuotient.equiv_of_ofRaw_eq
          (hleft := mul_valid ((integerReciprocalMap k).eval z hz).property
            ((integerReciprocalPowerMap k n).eval z hz).property)
          (hright := ((integerReciprocalPowerMap k (n+1)).eval z hz).property)
        let I := ComplexRawQuotient.ofRaw ((integerReciprocalMap k).eval z hz).val
          ((integerReciprocalMap k).eval z hz).property
        let P := ComplexRawQuotient.ofRaw ((integerReciprocalPowerMap k n).eval z hz).val
          ((integerReciprocalPowerMap k n).eval z hz).property
        change I*P=P*I
        grind only)

theorem integerReciprocalPowerMap_derivative (k : Int) (n : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalPowerMap_holomorphic k n).derivative z hz).val.Equiv
      (neg (scaleRat (n:Rat) (LocalODE.power ((integerReciprocalMap k).eval z hz).val (n+1)))) := by
  induction n with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((integerReciprocalPowerMap_holomorphic k 0).derivative z hz).property)
      (hright := neg_valid (scaleRat_valid (LocalODE.power_valid _ ((integerReciprocalMap k).eval z hz).property 1)))
    change (0:ComplexRawQuotient.Value)= -ComplexRawQuotient.scaleRat 0
      (ComplexRawQuotient.ofRaw (LocalODE.power ((integerReciprocalMap k).eval z hz).val 1)
        (LocalODE.power_valid _ ((integerReciprocalMap k).eval z hz).property 1))
    rw [ComplexRawQuotient.scaleRat_zeroScalar]
    grind only
  | succ n ih =>
    let i := (integerReciprocalMap k).eval z hz
    let d := (integerReciprocalMap_holomorphic k).derivative z hz
    let e := (integerReciprocalPowerMap_holomorphic k n).derivative z hz
    have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
      (hright := (ReciprocalDifference.derivative (integerShiftScalar z k)
        (upperScalar_nonzero _ (integerShiftScalar_upper z hz k))).property)
      (integerReciprocalMap_derivative k z hz)
    have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := e.property)
      (hright := neg_valid (scaleRat_valid (r := (n:Rat)) (LocalODE.power_valid _ i.property (n+1)))) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((integerReciprocalPowerMap_holomorphic k (n+1)).derivative z hz).property)
      (hright := neg_valid (scaleRat_valid (r := ((n+1:Nat):Rat)) (LocalODE.power_valid _ i.property (n+1+1))))
    let I := ComplexRawQuotient.ofRaw i.val i.property
    let D := ComplexRawQuotient.ofRaw d.val d.property
    let E := ComplexRawQuotient.ofRaw e.val e.property
    change D= -(I*I) at hd
    change E= -ComplexRawQuotient.scaleRat (n:Rat)
      (ComplexRawQuotient.ofRaw (LocalODE.power i.val (n+1)) (LocalODE.power_valid _ i.property (n+1))) at he
    rw [ScalarAlgebra.ofRaw_power _ i.property,ScalarAlgebra.scale_natural] at he
    change D*ComplexRawQuotient.ofRaw (LocalODE.power i.val n) (LocalODE.power_valid _ i.property n)+I*E=
      -ComplexRawQuotient.scaleRat ((n+1:Nat):Rat)
        (ComplexRawQuotient.ofRaw (LocalODE.power i.val (n+1+1)) (LocalODE.power_valid _ i.property (n+1+1)))
    rw [ScalarAlgebra.ofRaw_power _ i.property,ScalarAlgebra.ofRaw_power _ i.property,ScalarAlgebra.scale_natural]
    change D*I^n+I*E= -(((n+1:Nat):ScalarAlgebra.Value)*I^(n+1+1))
    change E= -((n:ScalarAlgebra.Value)*I^(n+1)) at he
    generalize I=i,D=d,E=e at hd he ⊢
    grind only

end ComputableAnalysis.ModularForms
