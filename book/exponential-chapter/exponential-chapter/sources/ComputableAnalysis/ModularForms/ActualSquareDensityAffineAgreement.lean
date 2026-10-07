import ComputableAnalysis.ModularForms.SquareDerivativeRemainderSums

/-! Actual contour densities agree with their affine model plus the derivative remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem rationalPole_mul_values (p q : QComplex) :
    gridScalarValue (rationalRectangleScalar (QComplex.mul p q))=
      gridScalarValue (rationalRectangleScalar p)*gridScalarValue (rationalRectangleScalar q) := by
  have h := RationalReciprocal.raw_mul_constants p q
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (ofQComplex_valid p) (ofQComplex_valid q))
    (hright := ofQComplex_valid (QComplex.mul p q)) h
  rw [ComplexRawQuotient.ofRaw_mul _ _ (ofQComplex_valid p) (ofQComplex_valid q)] at hv
  exact hv.symm

theorem rationalPole_scale_values (r : Rat) (q : QComplex) :
    gridScalarValue (rationalRectangleScalar (QComplex.scaleRat r q))=
      ComplexRawQuotient.scaleRat r (gridScalarValue (rationalRectangleScalar q)) := by
  have h : (rationalRectangleScalar (QComplex.scaleRat r q)).val.Equiv
      (scaleRat r (rationalRectangleScalar q).val) := by
    rw [rationalRectangleScalar_scale]
    exact equiv_refl _ (scaleRat_valid (rationalRectangleScalar q).property)
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (rationalRectangleScalar (QComplex.scaleRat r q)).property)
    (hright := scaleRat_valid (rationalRectangleScalar q).property) h
  rw [ComplexRawQuotient.ofRaw_scaleRat] at hv
  exact hv

def orientedPoleProduct (z : Scalar) (edge : HalfEdge) (R u : Rat) : Scalar :=
  let p := scalarProduct (scalarProduct z (rationalSquaredKernel (QComplex.scaleRat R (point edge u))))
    (rationalRectangleScalar (QComplex.scaleRat R (velocity edge)))
  if edge.upper then p else scalarNeg p

theorem orientedPoleProduct_weight_agreement (z : Scalar) (edge : HalfEdge) (R u : Rat) :
    (scalarProduct z (rationalRectangleScalar (squaredPolePullback edge R u))).val.Equiv
      (orientedPoleProduct z edge R u).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct z (rationalRectangleScalar (squaredPolePullback edge R u))).property)
    (hright := (orientedPoleProduct z edge R u).property)
  have hk : gridScalarValue (rationalRectangleScalar (squaredPolePullback edge R u))=
      ComplexRawQuotient.scaleRat (orientation edge)
        ((gridScalarValue (rationalRectangleScalar (RationalReciprocal.inverse (QComplex.scaleRat R (point edge u))))*
          gridScalarValue (rationalRectangleScalar (RationalReciprocal.inverse (QComplex.scaleRat R (point edge u))))) *
          gridScalarValue (rationalRectangleScalar (QComplex.scaleRat R (velocity edge)))) := by
    dsimp only [squaredPolePullback]
    rw [rationalPole_scale_values,rationalPole_mul_values,rationalPole_mul_values]
  change gridScalarValue (scalarProduct z (rationalRectangleScalar (squaredPolePullback edge R u)))=
    gridScalarValue (orientedPoleProduct z edge R u)
  let Z := gridScalarValue z
  let K := gridScalarValue (rationalRectangleScalar (squaredPolePullback edge R u))
  let I := gridScalarValue (rationalRectangleScalar (RationalReciprocal.inverse (QComplex.scaleRat R (point edge u))))
  let V := gridScalarValue (rationalRectangleScalar (QComplex.scaleRat R (velocity edge)))
  change K=ComplexRawQuotient.scaleRat (orientation edge) ((I*I)*V) at hk
  cases edge with
  | mk quarter upper =>
    cases upper with
    | true =>
      change Z*K=(Z*(I*I))*V
      simp only [orientation,↓reduceIte,ComplexRawQuotient.scaleRat_one] at hk
      rw [hk]
      grind only
    | false =>
      change Z*K= -((Z*(I*I))*V)
      simp only [orientation,Bool.false_eq_true,↓reduceIte] at hk
      rw [←ComplexRawQuotient.neg_eq_scaleRat_neg_one] at hk
      rw [hk]
      grind only

theorem translatedAffineModel_error_equiv (f : DomainFunctions.Map) (c d q : Scalar)
    (hc : f.domain c) (hz : f.domain (Centered.translate c q)) :
    (sub (f.eval (Centered.translate c q) hz).val
      (affineMidpointModel (f.eval c hc) d q).val).Equiv
      (remainder f c hc d (Centered.translate c q) hz) := by
  let z := Centered.translate c q
  have he := add_equiv (equiv_refl _ (f.eval c hc).property)
    (mul_equiv d.property d.property (Centered.offset c z).property q.property
      (equiv_refl _ d.property) (Centered.offset_translate c q))
  have hs := FunctionTheory.sub_congr
    (equiv_refl _ (f.eval z hz).property) (equiv_symm he)
  exact equiv_trans
    (sub_valid (f.eval z hz).property (affineMidpointModel (f.eval c hc) d q).property)
    (sub_valid (f.eval z hz).property (affineMidpointModel (f.eval c hc) d (Centered.offset c z)).property)
    (remainder_valid f c hc d z hz) hs (localAffineModel_error_equiv f c d z hc hz)

theorem orientedPoleProduct_sub (a b : Scalar) (edge : HalfEdge) (R u : Rat) :
    (sub (orientedPoleProduct a edge R u).val (orientedPoleProduct b edge R u).val).Equiv
      (orientedPoleProduct ⟨sub a.val b.val,sub_valid a.property b.property⟩ edge R u).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (orientedPoleProduct a edge R u).property
      (orientedPoleProduct b edge R u).property)
    (hright := (orientedPoleProduct ⟨sub a.val b.val,sub_valid a.property b.property⟩ edge R u).property)
  let A := gridScalarValue a
  let B := gridScalarValue b
  let K := gridScalarValue (rationalSquaredKernel (QComplex.scaleRat R (point edge u)))
  let V := gridScalarValue (rationalRectangleScalar (QComplex.scaleRat R (velocity edge)))
  cases edge with
  | mk quarter upper =>
    cases upper with
    | true =>
      change (A*K)*V-(B*K)*V=((A-B)*K)*V
      grind only
    | false =>
      change -((A*K)*V)-(-((B*K)*V))= -(((A-B)*K)*V)
      grind only

theorem orientedPoleProduct_congr (a b : Scalar) (edge : HalfEdge) (R u : Rat)
    (h : a.val.Equiv b.val) :
    (orientedPoleProduct a edge R u).val.Equiv (orientedPoleProduct b edge R u).val := by
  let k := rationalSquaredKernel (QComplex.scaleRat R (point edge u))
  let v := rationalRectangleScalar (QComplex.scaleRat R (velocity edge))
  have hp := mul_equiv (mul_valid a.property k.property) (mul_valid b.property k.property)
    v.property v.property
    (mul_equiv a.property b.property k.property k.property h (equiv_refl _ k.property))
    (equiv_refl _ v.property)
  dsimp only [orientedPoleProduct]
  split
  · exact hp
  · exact neg_equiv hp

theorem actualSquareDensity_affine_remainder (c : Scalar) (edge : HalfEdge) (R u : Rat) :
    (sub (cartesianSquareKernelDensity c edge R u).val
      (affinePoleDensity (pairedEntireRiccatiMap.eval c trivial)
        (pairedEntireRiccatiMap_holomorphic.derivative c trivial) edge R u).val).Equiv
      (squareDerivativeRemainderDensity c edge R u).val := by
  let q := rationalRectangleScalar (QComplex.scaleRat R (point edge u))
  let f := pairedEntireRiccatiMap
  let d := pairedEntireRiccatiMap_holomorphic.derivative c trivial
  let F := f.eval (Centered.translate c q) trivial
  let A := affineMidpointModel (f.eval c trivial) d q
  have hf : (cartesianSquareKernelDensity c edge R u).val=
      (orientedPoleProduct F edge R u).val := by
    unfold cartesianSquareKernelDensity
    rw [cartesianSquarePoint_agreement]
    rfl
  have ha : (affinePoleDensity (f.eval c trivial) d edge R u).val.Equiv
      (orientedPoleProduct A edge R u).val := orientedPoleProduct_weight_agreement A edge R u
  have hs := FunctionTheory.sub_congr
    (equiv_refl _ (orientedPoleProduct F edge R u).property) ha
  have ht := orientedPoleProduct_sub F A edge R u
  have hn : (sub F.val A.val).Equiv (squareDerivativeRemainder c edge R u).val :=
    translatedAffineModel_error_equiv f c d q trivial trivial
  have hr := orientedPoleProduct_congr
    ⟨sub F.val A.val,sub_valid F.property A.property⟩
    (squareDerivativeRemainder c edge R u) edge R u hn
  rw [hf]
  exact equiv_trans
    (sub_valid (orientedPoleProduct F edge R u).property
      (affinePoleDensity (f.eval c trivial) d edge R u).property)
    (sub_valid (orientedPoleProduct F edge R u).property (orientedPoleProduct A edge R u).property)
    (squareDerivativeRemainderDensity c edge R u).property hs
    (equiv_trans
      (sub_valid (orientedPoleProduct F edge R u).property (orientedPoleProduct A edge R u).property)
      (orientedPoleProduct ⟨sub F.val A.val,sub_valid F.property A.property⟩ edge R u).property
      (squareDerivativeRemainderDensity c edge R u).property ht hr)

theorem actualSquareDensity_affine_error_bound (c : Scalar) (edge : HalfEdge)
    (R eps : QPos) (u : Rat) (hu : 0≤u) (hu1 : u≤1)
    (hR : R.val≤((pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eps).val) :
    Small (sub (cartesianSquareKernelDensity c edge R.val u).val
      (affinePoleDensity (pairedEntireRiccatiMap.eval c trivial)
        (pairedEntireRiccatiMap_holomorphic.derivative c trivial) edge R.val u).val)
      (8*eps.val) := by
  exact Small.congr (squareDerivativeRemainderDensity c edge R.val u).property
    (sub_valid (cartesianSquareKernelDensity c edge R.val u).property
      (affinePoleDensity (pairedEntireRiccatiMap.eval c trivial)
        (pairedEntireRiccatiMap_holomorphic.derivative c trivial) edge R.val u).property)
    (equiv_symm (actualSquareDensity_affine_remainder c edge R.val u))
    (squareDerivativeRemainderDensity_bound c edge R eps u hu hu1 hR)

end ComputableAnalysis.ModularForms
