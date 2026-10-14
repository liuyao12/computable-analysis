import ComputableAnalysis.ModularForms.WideEulerHolomorphic
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Executable derivative assembled from the proved finite and infinite-tail slopes. -/
def wideEulerDerivativeValue (q : Scalar) (hq : wideLambertFifthDomain q) : Scalar :=
  scalarSum (scalarProduct (finiteDiscriminantEulerSlope q 2) (wideEulerTailNomeMap.eval q hq))
    (scalarProduct (finiteDiscriminantEulerProduct q 2) (wideEulerTailDerivativeCandidate q hq))

theorem wideEulerDerivativeValue_actual (q : Scalar) (hq : wideLambertFifthDomain q) :
    (wideEulerDerivativeValue q hq).val.Equiv (wideEulerNomeMap_holomorphic.derivative q hq).val :=
  equiv_symm (wideEulerNomeMap_derivative q hq)

/-- Executable derivative of the actual normalized product. -/
def wideNormalizedEulerDerivativeValue (q : Scalar) (hq : wideLambertFifthDomain q) : Scalar :=
  scalarSum (scalarProduct (wideEulerDerivativeValue q hq) q) (wideEulerNomeMap.eval q hq)

/-- Constructed logarithmic derivative of the actual nonzero wider Euler product. -/
def wideEulerLogarithmicDerivative (q : Scalar) (hq : wideLambertFifthDomain q) : Scalar :=
  scalarProduct (wideEulerDerivativeValue q hq)
    (RepresentedReciprocal.inverse (wideEulerNomeMap.eval q hq) (wideEulerNomeMap_nonzero q hq))

/-- The actual logarithmic derivative reconstructs the actual derivative exactly. -/
theorem wideEulerLogarithmicDerivative_identity (q : Scalar) (hq : wideLambertFifthDomain q) :
    (mul (wideEulerLogarithmicDerivative q hq).val (wideEulerNomeMap.eval q hq).val).Equiv
      (wideEulerDerivativeValue q hq).val := by
  let P := wideEulerNomeMap.eval q hq
  let D := wideEulerDerivativeValue q hq
  let I := RepresentedReciprocal.inverse P (wideEulerNomeMap_nonzero q hq)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid P.property I.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse P (wideEulerNomeMap_nonzero q hq))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (wideEulerLogarithmicDerivative q hq).property P.property) (hright := D.property)
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let i := ComplexRawQuotient.ofRaw I.val I.property
  change p*i=1 at hi
  change (d*i)*p=d
  grind only

/-- Product differentiation for the actual normalized wider Euler evaluator. -/
theorem wideNormalizedEulerMap_derivative (q : Scalar) (hq : wideLambertFifthDomain q) :
    (wideNormalizedEulerMap_holomorphic.derivative q hq).val.Equiv
      (add (mul (wideEulerNomeMap_holomorphic.derivative q hq).val q.val)
        (wideEulerNomeMap.eval q hq).val) := by
  let D := wideEulerNomeMap_holomorphic.derivative q hq
  let P := wideEulerNomeMap.eval q hq
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (wideNormalizedEulerMap_holomorphic.derivative q hq).property)
    (hright := add_valid (mul_valid D.property q.property) P.property)
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  change d*Q+p*1=d*Q+p
  grind only

/-- The executable normalized derivative agrees with the actual holomorphic derivative. -/
theorem wideNormalizedEulerDerivativeValue_actual (q : Scalar) (hq : wideLambertFifthDomain q) :
    (wideNormalizedEulerDerivativeValue q hq).val.Equiv
      (wideNormalizedEulerMap_holomorphic.derivative q hq).val := by
  let A := wideNormalizedEulerDerivativeValue q hq
  let D := wideEulerNomeMap_holomorphic.derivative q hq
  let P := wideEulerNomeMap.eval q hq
  have he := add_equiv
    (mul_equiv (wideEulerDerivativeValue q hq).property D.property q.property q.property
      (wideEulerDerivativeValue_actual q hq) (equiv_refl _ q.property)) (equiv_refl _ P.property)
  exact equiv_trans A.property (add_valid (mul_valid D.property q.property) P.property)
    (wideNormalizedEulerMap_holomorphic.derivative q hq).property he
    (equiv_symm (wideNormalizedEulerMap_derivative q hq))

/-- Constructed normalized logarithmic derivative at every nonzero wider nome. -/
def wideNormalizedEulerLogarithmicDerivative (q : Scalar) (hq : wideLambertFifthDomain q)
    (hn : NonzeroBoxSearch.Nonzero q) : Scalar :=
  scalarProduct (wideNormalizedEulerDerivativeValue q hq)
    (RepresentedReciprocal.inverse (wideNormalizedEulerMap.eval q hq)
      ((wideNormalizedEulerMap_nonzero_iff q hq).mpr hn))

/-- Exact logarithmic product identity, with actual nonvanishing evidence. -/
theorem wideNormalizedEulerLogarithmicDerivative_identity (q : Scalar)
    (hq : wideLambertFifthDomain q) (hn : NonzeroBoxSearch.Nonzero q) :
    (mul q.val (wideNormalizedEulerLogarithmicDerivative q hq hn).val).Equiv
      (add one (mul q.val (wideEulerLogarithmicDerivative q hq).val)) := by
  let P := wideEulerNomeMap.eval q hq
  let D := wideEulerDerivativeValue q hq
  let F := wideNormalizedEulerMap.eval q hq
  let G := wideNormalizedEulerDerivativeValue q hq
  let I := RepresentedReciprocal.inverse P (wideEulerNomeMap_nonzero q hq)
  let J := RepresentedReciprocal.inverse F ((wideNormalizedEulerMap_nonzero_iff q hq).mpr hn)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid P.property I.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse P (wideEulerNomeMap_nonzero q hq))
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid F.property J.property)
    (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse F ((wideNormalizedEulerMap_nonzero_iff q hq).mpr hn))
  have hg := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := G.property)
    (hright := add_valid (mul_valid D.property q.property) P.property)
    (equiv_refl _ G.property)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid q.property (wideNormalizedEulerLogarithmicDerivative q hq hn).property)
    (hright := add_valid (ofQComplex_valid _) (mul_valid q.property (wideEulerLogarithmicDerivative q hq).property))
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  let i := ComplexRawQuotient.ofRaw I.val I.property
  let j := ComplexRawQuotient.ofRaw J.val J.property
  change p*i=1 at hi
  change (p*Q)*j=1 at hj
  change g=d*Q+p at hg
  change Q*(g*j)=1+Q*(d*i)
  have hqi : Q*j=i := by grind only
  rw [hg]
  grind only


/-- Executable logarithmic division reconstructs the actual holomorphic derivative. -/
theorem wideEulerLogarithmicDerivative_actual_identity (q : Scalar) (hq : wideLambertFifthDomain q) :
    (mul (wideEulerLogarithmicDerivative q hq).val (wideEulerNomeMap.eval q hq).val).Equiv
      (wideEulerNomeMap_holomorphic.derivative q hq).val :=
  equiv_trans (mul_valid (wideEulerLogarithmicDerivative q hq).property (wideEulerNomeMap.eval q hq).property)
    (wideEulerDerivativeValue q hq).property (wideEulerNomeMap_holomorphic.derivative q hq).property
    (wideEulerLogarithmicDerivative_identity q hq) (wideEulerDerivativeValue_actual q hq)

/-- Executable wider derivative values depend only on the represented nome. -/
theorem wideEulerDerivativeValue_congr (q w : Scalar) (hq : wideLambertFifthDomain q)
    (hw : wideLambertFifthDomain w) (he : q.val.Equiv w.val) :
    (wideEulerDerivativeValue q hq).val.Equiv (wideEulerDerivativeValue w hw).val :=
  equiv_trans (wideEulerDerivativeValue q hq).property (wideEulerNomeMap_holomorphic.derivative q hq).property
    (wideEulerDerivativeValue w hw).property (wideEulerDerivativeValue_actual q hq)
    (equiv_trans (wideEulerNomeMap_holomorphic.derivative q hq).property
      (wideEulerNomeMap_holomorphic.derivative w hw).property (wideEulerDerivativeValue w hw).property
      (wideEulerNomeMap_holomorphic.derivative_congr q w hq hw he)
      (equiv_symm (wideEulerDerivativeValue_actual w hw)))

end ComputableAnalysis.ModularForms
