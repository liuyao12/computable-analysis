import ComputableAnalysis.ModularForms.WideEulerFactorGeometricRemainder
import ComputableAnalysis.ModularForms.WideEulerFactorVariation
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
/-- Literal remainder using the proved executable whole-product slope. -/
def wideEulerTailRemainder (a z : Scalar) (N : Nat) : Scalar :=
  ⟨sub (sub (wideEulerTailPrefix z N).val (wideEulerTailPrefix a N).val)
    (mul (wideEulerTailSlope a N).val (sub z.val a.val)),
    sub_valid (sub_valid (wideEulerTailPrefix z N).property
      (wideEulerTailPrefix a N).property)
      (mul_valid (wideEulerTailSlope a N).property (sub_valid z.property a.property))⟩

theorem wideEulerTailRemainder_actual (a z : Scalar) (N : Nat) :
    (DomainFunctions.remainder (wideEulerTailMap N) a trivial
      ((wideEulerTailMap_holomorphic N).derivative a trivial) z trivial).Equiv
      (wideEulerTailRemainder a z N).val := by
  exact FunctionTheory.sub_congr
    (equiv_refl _ (sub_valid (wideEulerTailPrefix z N).property
      (wideEulerTailPrefix a N).property))
    (mul_equiv ((wideEulerTailMap_holomorphic N).derivative a trivial).property
      (wideEulerTailSlope a N).property (sub_valid z.property a.property)
      (sub_valid z.property a.property) (wideEulerTailSlope_actual a N)
      (equiv_refl _ (sub_valid z.property a.property)))

/-- Exposing the factor's deviation from one avoids exponential growth of
whole-product remainder bounds. Every slope here is the actual derivative. -/
theorem wideEulerTailRemainder_step (a z : Scalar) (N : Nat) :
    (wideEulerTailRemainder a z (N+1)).val.Equiv
      (add (add (wideEulerTailRemainder a z N).val
        (mul (wideEulerTailRemainder a z N).val
          (sub (tauEulerFactorValue z (N+2)).val one)))
        (add (mul (wideEulerTailPrefix a N).val
          (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap (N+2)) 24) a trivial
            ((tauMapPower_holomorphic (tauEulerFactorMap (N+2))
              (tauEulerFactorMap_holomorphic (N+2)) 24).derivative a trivial) z trivial))
          (mul (mul (wideEulerTailSlope a N).val (sub z.val a.val))
            (sub (tauEulerFactorValue z (N+2)).val (tauEulerFactorValue a (N+2)).val)))) := by
  let P := wideEulerTailPrefix a N
  let Q := wideEulerTailPrefix z N
  let F := tauEulerFactorValue a (N+2)
  let G := tauEulerFactorValue z (N+2)
  let D := wideEulerTailSlope a N
  let E := tauEulerFactorSlope a (N+2)
  let A := (tauMapPower_holomorphic (tauEulerFactorMap (N+2))
    (tauEulerFactorMap_holomorphic (N+2)) 24).derivative a trivial
  let H : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let R := wideEulerTailRemainder a z N
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := A.property)
    (hright := E.property) (tauEulerFactorSlope_actual a (N+2))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (wideEulerTailRemainder a z (N+1)).property)
    (hright := add_valid (add_valid R.property
      (mul_valid R.property (sub_valid G.property (ofQComplex_valid _))))
      (add_valid (mul_valid P.property (DomainFunctions.remainder_valid _ _ _ _ _ _))
        (mul_valid (mul_valid D.property H.property) (sub_valid G.property F.property))))
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let q := ComplexRawQuotient.ofRaw Q.val Q.property
  let f := ComplexRawQuotient.ofRaw F.val F.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let e := ComplexRawQuotient.ofRaw E.val E.property
  let av := ComplexRawQuotient.ofRaw A.val A.property
  let h := ComplexRawQuotient.ofRaw H.val H.property
  change av=e at hd
  change (q*g-p*f)-(d*f+p*e)*h =
    (((q-p)-d*h)+((q-p)-d*h)*(g-1))+(p*((g-f)-av*h)+(d*h)*(g-f))
  rw [hd]
  grind only

/-- Quantitative propagation through one actual Euler factor. The leading
remainder is retained once; only the deviation term incurs a product bound. -/
theorem wideEulerTailRemainder_step_bound (a z : Scalar) (N : Nat)
    (E B D H V L F : Rat)
    (hEn : 0≤E) (hBn : 0≤B) (hDn : 0≤D) (hHn : 0≤H)
    (hVn : 0≤V) (hLn : 0≤L) (hFn : 0≤F)
    (hE : Small (wideEulerTailRemainder a z N).val E)
    (hB : Small (wideEulerTailPrefix a N).val B)
    (hD : Small (wideEulerTailSlope a N).val D)
    (hH : Small (sub z.val a.val) H)
    (hV : Small (sub (tauEulerFactorValue z (N+2)).val one) V)
    (hL : Small (sub (tauEulerFactorValue z (N+2)).val (tauEulerFactorValue a (N+2)).val) L)
    (hF : Small (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap (N+2)) 24) a trivial
      ((tauMapPower_holomorphic (tauEulerFactorMap (N+2)) (tauEulerFactorMap_holomorphic (N+2)) 24).derivative a trivial)
      z trivial) F) :
    Small (wideEulerTailRemainder a z (N+1)).val
      ((E+2*E*V)+(2*B*F+2*(2*D*H)*L)) := by
  have h1 := Small.mul (wideEulerTailRemainder a z N).property
    (sub_valid (tauEulerFactorValue z (N+2)).property (ofQComplex_valid _)) hEn hVn hE hV
  have h2 := Small.mul (wideEulerTailPrefix a N).property
    (DomainFunctions.remainder_valid _ _ _ _ _ _) hBn hFn hB hF
  have h3 := Small.mul (wideEulerTailSlope a N).property (sub_valid z.property a.property) hDn hHn hD hH
  have h4 := Small.mul (mul_valid (wideEulerTailSlope a N).property
    (sub_valid z.property a.property))
    (sub_valid (tauEulerFactorValue z (N+2)).property (tauEulerFactorValue a (N+2)).property)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hDn) hHn) hLn h3 hL
  exact Small.congr
    (add_valid (add_valid (wideEulerTailRemainder a z N).property
      (mul_valid (wideEulerTailRemainder a z N).property
        (sub_valid (tauEulerFactorValue z (N+2)).property (ofQComplex_valid _))))
      (add_valid (mul_valid (wideEulerTailPrefix a N).property
        (DomainFunctions.remainder_valid _ _ _ _ _ _))
        (mul_valid (mul_valid (wideEulerTailSlope a N).property (sub_valid z.property a.property))
          (sub_valid (tauEulerFactorValue z (N+2)).property (tauEulerFactorValue a (N+2)).property))))
    (wideEulerTailRemainder a z (N+1)).property
    (equiv_symm (wideEulerTailRemainder_step a z N))
    (LocalODE.small_add (LocalODE.small_add hE h1) (LocalODE.small_add h2 h4))


end ComputableAnalysis.ModularForms
