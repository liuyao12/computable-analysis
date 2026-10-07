import ComputableAnalysis.ModularForms.IntegerPowerPairDerivatives
import ComputableAnalysis.ModularForms.NomeMomentLimitLinearity

/-! Exact full finite-row differentiation, with the central term included. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerPowerFiniteRowMap_derivative (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k N : Nat) :
    ((integerPowerFiniteRowMap_holomorphic k N).derivative z hz).val.Equiv
      (neg (scaleRat (k:Rat) (integerPowerRowPrefix z hz (k+1) N))) := by
  let a := ((integerReciprocalPowerMap 0 (k+1)).eval z hz)
  let b := ((pairedIntegerPowerFiniteMap (k+1) N).eval z hz)
  have h : (add ((integerReciprocalPowerMap_holomorphic 0 k).derivative z hz).val
      ((pairedIntegerPowerFiniteMap_holomorphic k N).derivative z hz).val).Equiv
      (add (neg (scaleRat (k:Rat) a.val)) (neg (scaleRat (k:Rat) b.val))) :=
    add_equiv (integerReciprocalPowerMap_derivative 0 k z hz)
      (pairedIntegerPowerFiniteMap_derivative z hz k N)
  apply equiv_trans ((integerPowerFiniteRowMap_holomorphic k N).derivative z hz).property
    (add_valid (neg_valid (scaleRat_valid (r := (k:Rat)) a.property))
      (neg_valid (scaleRat_valid (r := (k:Rat)) b.property)))
    (neg_valid (scaleRat_valid (r := (k:Rat)) (integerPowerRowPrefix_valid z hz (k+1) N))) h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (neg_valid (scaleRat_valid (r := (k:Rat)) a.property))
      (neg_valid (scaleRat_valid (r := (k:Rat)) b.property)))
    (hright := neg_valid (scaleRat_valid (r := (k:Rat)) (integerPowerRowPrefix_valid z hz (k+1) N)))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  change -ComplexRawQuotient.scaleRat (k:Rat) A+ -ComplexRawQuotient.scaleRat (k:Rat) B=
    -ComplexRawQuotient.scaleRat (k:Rat) (A+B)
  rw [ComplexRawQuotient.scaleRat_add]
  generalize ComplexRawQuotient.scaleRat (k:Rat) A=u,
    ComplexRawQuotient.scaleRat (k:Rat) B=v
  grind only

theorem integerPowerFiniteRowDerivative_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) (n : Nat) :
    Small (sub (neg (scaleRat (k:Rat) (integerPowerRowAssembly z hz (k+1) B)))
      ((integerPowerFiniteRowMap_holomorphic k (4*B+(n+1))).derivative z hz).val)
      ((k:Rat)*(((2*32^(k+1):Nat):Rat)*(((n+1:Nat):Rat))⁻¹)) := by
  let s : Scalar := ⟨integerPowerRowAssembly z hz (k+1) B,
    integerPowerRowAssembly_valid z hz (k+1) B (by omega) hB⟩
  let p : Scalar := ⟨integerPowerRowPrefix z hz (k+1) (4*B+(n+1)),
    integerPowerRowPrefix_valid z hz (k+1) (4*B+(n+1))⟩
  have h := SeriesLimitLaws.small_neg (represented_prefix_scale_close s p (k:Rat) _
    Rat.natCast_nonneg (integerPowerRowAssembly_close z hz (k+1) B (by omega) hB n))
  have he : (neg (sub (scaleRat (k:Rat) s.val) (scaleRat (k:Rat) p.val))).Equiv
      (sub (neg (scaleRat (k:Rat) s.val)) (neg (scaleRat (k:Rat) p.val))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid (scaleRat_valid (r := (k:Rat)) s.property)
        (scaleRat_valid (r := (k:Rat)) p.property)))
      (hright := sub_valid (neg_valid (scaleRat_valid (r := (k:Rat)) s.property))
        (neg_valid (scaleRat_valid (r := (k:Rat)) p.property)))
    let S := ComplexRawQuotient.ofRaw (scaleRat (k:Rat) s.val) (scaleRat_valid s.property)
    let P := ComplexRawQuotient.ofRaw (scaleRat (k:Rat) p.val) (scaleRat_valid p.property)
    change -(S-P)= -S- -P
    generalize S=u,P=v
    grind only
  have hD := integerPowerFiniteRowMap_derivative z hz k (4*B+(n+1))
  have he2 := FunctionTheory.sub_congr
    (equiv_refl _ (neg_valid (scaleRat_valid (r := (k:Rat)) s.property))) (equiv_symm hD)
  exact Small.congr (neg_valid (sub_valid (scaleRat_valid (r := (k:Rat)) s.property)
      (scaleRat_valid (r := (k:Rat)) p.property)))
    (sub_valid (neg_valid (scaleRat_valid (r := (k:Rat)) s.property))
      ((integerPowerFiniteRowMap_holomorphic k (4*B+(n+1))).derivative z hz).property)
    (equiv_trans (neg_valid (sub_valid (scaleRat_valid (r := (k:Rat)) s.property)
        (scaleRat_valid (r := (k:Rat)) p.property)))
      (sub_valid (neg_valid (scaleRat_valid (r := (k:Rat)) s.property))
        (neg_valid (scaleRat_valid (r := (k:Rat)) p.property)))
      (sub_valid (neg_valid (scaleRat_valid (r := (k:Rat)) s.property))
        ((integerPowerFiniteRowMap_holomorphic k (4*B+(n+1))).derivative z hz).property) he he2) h

end ComputableAnalysis.ModularForms
