import ComputableAnalysis.ModularForms.TauEulerGeometricRemainder
import ComputableAnalysis.ModularForms.TauFiniteProductDerivative

/-! Executable finite Euler-product remainders and their exact recurrence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Literal remainder using the proved executable whole-product slope. -/
def finiteDiscriminantEulerRemainder (a z : Scalar) (N : Nat) : Scalar :=
  ⟨sub (sub (finiteDiscriminantEulerProduct z N).val (finiteDiscriminantEulerProduct a N).val)
    (mul (finiteDiscriminantEulerSlope a N).val (sub z.val a.val)),
    sub_valid (sub_valid (finiteDiscriminantEulerProduct z N).property
      (finiteDiscriminantEulerProduct a N).property)
      (mul_valid (finiteDiscriminantEulerSlope a N).property (sub_valid z.property a.property))⟩

theorem finiteDiscriminantEulerRemainder_actual (a z : Scalar) (N : Nat) :
    (DomainFunctions.remainder (finiteDiscriminantEulerMap N) a trivial
      ((finiteDiscriminantEulerMap_holomorphic N).derivative a trivial) z trivial).Equiv
      (finiteDiscriminantEulerRemainder a z N).val := by
  exact FunctionTheory.sub_congr
    (equiv_refl _ (sub_valid (finiteDiscriminantEulerProduct z N).property
      (finiteDiscriminantEulerProduct a N).property))
    (mul_equiv ((finiteDiscriminantEulerMap_holomorphic N).derivative a trivial).property
      (finiteDiscriminantEulerSlope a N).property (sub_valid z.property a.property)
      (sub_valid z.property a.property) (finiteDiscriminantEulerSlope_actual a N)
      (equiv_refl _ (sub_valid z.property a.property)))

/-- Exposing the factor's deviation from one avoids exponential growth of
whole-product remainder bounds. Every slope here is the actual derivative. -/
theorem finiteDiscriminantEulerRemainder_step (a z : Scalar) (N : Nat) :
    (finiteDiscriminantEulerRemainder a z (N+1)).val.Equiv
      (add (add (finiteDiscriminantEulerRemainder a z N).val
        (mul (finiteDiscriminantEulerRemainder a z N).val
          (sub (tauEulerFactorValue z N).val one)))
        (add (mul (finiteDiscriminantEulerProduct a N).val
          (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap N) 24) a trivial
            ((tauMapPower_holomorphic (tauEulerFactorMap N)
              (tauEulerFactorMap_holomorphic N) 24).derivative a trivial) z trivial))
          (mul (mul (finiteDiscriminantEulerSlope a N).val (sub z.val a.val))
            (sub (tauEulerFactorValue z N).val (tauEulerFactorValue a N).val)))) := by
  let P := finiteDiscriminantEulerProduct a N
  let Q := finiteDiscriminantEulerProduct z N
  let F := tauEulerFactorValue a N
  let G := tauEulerFactorValue z N
  let D := finiteDiscriminantEulerSlope a N
  let E := tauEulerFactorSlope a N
  let A := (tauMapPower_holomorphic (tauEulerFactorMap N)
    (tauEulerFactorMap_holomorphic N) 24).derivative a trivial
  let H : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  let R := finiteDiscriminantEulerRemainder a z N
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := A.property)
    (hright := E.property) (tauEulerFactorSlope_actual a N)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (finiteDiscriminantEulerRemainder a z (N+1)).property)
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
theorem finiteDiscriminantEulerRemainder_step_bound (a z : Scalar) (N : Nat)
    (E B D H V L F : Rat)
    (hEn : 0≤E) (hBn : 0≤B) (hDn : 0≤D) (hHn : 0≤H)
    (hVn : 0≤V) (hLn : 0≤L) (hFn : 0≤F)
    (hE : Small (finiteDiscriminantEulerRemainder a z N).val E)
    (hB : Small (finiteDiscriminantEulerProduct a N).val B)
    (hD : Small (finiteDiscriminantEulerSlope a N).val D)
    (hH : Small (sub z.val a.val) H)
    (hV : Small (sub (tauEulerFactorValue z N).val one) V)
    (hL : Small (sub (tauEulerFactorValue z N).val (tauEulerFactorValue a N).val) L)
    (hF : Small (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap N) 24) a trivial
      ((tauMapPower_holomorphic (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) 24).derivative a trivial)
      z trivial) F) :
    Small (finiteDiscriminantEulerRemainder a z (N+1)).val
      ((E+2*E*V)+(2*B*F+2*(2*D*H)*L)) := by
  have h1 := Small.mul (finiteDiscriminantEulerRemainder a z N).property
    (sub_valid (tauEulerFactorValue z N).property (ofQComplex_valid _)) hEn hVn hE hV
  have h2 := Small.mul (finiteDiscriminantEulerProduct a N).property
    (DomainFunctions.remainder_valid _ _ _ _ _ _) hBn hFn hB hF
  have h3 := Small.mul (finiteDiscriminantEulerSlope a N).property (sub_valid z.property a.property) hDn hHn hD hH
  have h4 := Small.mul (mul_valid (finiteDiscriminantEulerSlope a N).property
    (sub_valid z.property a.property))
    (sub_valid (tauEulerFactorValue z N).property (tauEulerFactorValue a N).property)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hDn) hHn) hLn h3 hL
  exact Small.congr
    (add_valid (add_valid (finiteDiscriminantEulerRemainder a z N).property
      (mul_valid (finiteDiscriminantEulerRemainder a z N).property
        (sub_valid (tauEulerFactorValue z N).property (ofQComplex_valid _))))
      (add_valid (mul_valid (finiteDiscriminantEulerProduct a N).property
        (DomainFunctions.remainder_valid _ _ _ _ _ _))
        (mul_valid (mul_valid (finiteDiscriminantEulerSlope a N).property (sub_valid z.property a.property))
          (sub_valid (tauEulerFactorValue z N).property (tauEulerFactorValue a N).property))))
    (finiteDiscriminantEulerRemainder a z (N+1)).property
    (equiv_symm (finiteDiscriminantEulerRemainder_step a z N))
    (LocalODE.small_add (LocalODE.small_add hE h1) (LocalODE.small_add h2 h4))

end ComputableAnalysis.ModularForms
