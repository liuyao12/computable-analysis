import ComputableAnalysis.ModularForms.RepresentedSquareAffineResidue

/-! The actual derivative remainder survives the squared-pole weight with a uniform error. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem scaledSquarePoint_small (edge : HalfEdge) (R u : Rat) (hR : 0≤R)
    (hu : 0≤u) (hu1 : u≤1) : Small (ofQComplex (QComplex.scaleRat R (point edge u))) R := by
  apply (BoxApproximation.rational_small _).mono
  have hRu := Rat.mul_le_mul_of_nonneg_left hu1 hR
  have hRu0 := Rat.mul_nonneg hR hu
  cases edge with
  | mk quarter upper =>
    cases quarter <;> cases upper <;>
      unfold point rotation orientation QComplex.mul QComplex.scaleRat BoxApproximation.coordinateBound qabs <;>
      simp only [Rat.max_def] <;> grind only

noncomputable def squareDerivativeRemainder (c : Scalar) (edge : HalfEdge) (R u : Rat) : Scalar :=
  let z := Centered.translate c (rationalRectangleScalar (QComplex.scaleRat R (point edge u)))
  ⟨remainder pairedEntireRiccatiMap c trivial
    (pairedEntireRiccatiMap_holomorphic.derivative c trivial) z trivial,
    remainder_valid pairedEntireRiccatiMap c trivial
      (pairedEntireRiccatiMap_holomorphic.derivative c trivial) z trivial⟩

noncomputable def squareDerivativeRemainderDensity (c : Scalar) (edge : HalfEdge) (R u : Rat) : Scalar :=
  let p := scalarProduct (scalarProduct (squareDerivativeRemainder c edge R u)
    (rationalSquaredKernel (QComplex.scaleRat R (point edge u))))
    (rationalRectangleScalar (QComplex.scaleRat R (velocity edge)))
  if edge.upper then p else scalarNeg p

theorem squareDerivativeRemainder_small (c : Scalar) (edge : HalfEdge) (R eps : QPos)
    (u : Rat) (hu : 0≤u) (hu1 : u≤1)
    (hR : R.val≤((pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eps).val) :
    Small (squareDerivativeRemainder c edge R.val u).val (eps.val*R.val) := by
  let q := rationalRectangleScalar (QComplex.scaleRat R.val (point edge u))
  let z := Centered.translate c q
  have hq := scaledSquarePoint_small edge R.val u (Rat.le_of_lt R.property) hu hu1
  have hz : Small (sub z.val c.val) R.val :=
    Small.congr q.property (sub_valid z.property c.property)
      (equiv_symm (Centered.offset_translate c q)) hq
  exact (pairedEntireRiccatiMap_holomorphic.atPoint c trivial).estimate eps R z trivial hR hz

theorem squareDerivativeRemainderDensity_bound (c : Scalar) (edge : HalfEdge) (R eps : QPos)
    (u : Rat) (hu : 0≤u) (hu1 : u≤1)
    (hR : R.val≤((pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eps).val) :
    Small (squareDerivativeRemainderDensity c edge R.val u).val (8*eps.val) := by
  have hr := squareDerivativeRemainder_small c edge R eps u hu hu1 hR
  have hk := rationalSquaredKernel_separated_bound (QComplex.scaleRat R.val (point edge u)) R.val R.property
    (scaledSquarePoint_coordinate_separated edge u R.val)
  have hv := (BoxApproximation.rational_small _).mono
    (scaledSquareVelocity_coordinate_bound edge R.val (Rat.le_of_lt R.property))
  have hi : 0≤1/R.val := by
    rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr R.property)
  have hK : 0≤2*(1/R.val)*(1/R.val) := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hi) hi
  have he : 0≤eps.val*R.val := Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt R.property)
  have hp := Small.mul (squareDerivativeRemainder c edge R.val u).property
    (rationalSquaredKernel (QComplex.scaleRat R.val (point edge u))).property he hK hr hk
  have hb := Small.mul
    (scalarProduct (squareDerivativeRemainder c edge R.val u)
      (rationalSquaredKernel (QComplex.scaleRat R.val (point edge u)))).property
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity edge))).property
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) he) hK) (Rat.le_of_lt R.property) hp hv
  have hc : R.val*(1/R.val)=1 := by
    rw [Rat.div_def,Rat.one_mul]; exact Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
  have ha : 2*(2*(eps.val*R.val)*(2*(1/R.val)*(1/R.val)))*R.val=8*eps.val := by grind only
  rw [ha] at hb
  dsimp only [squareDerivativeRemainderDensity]
  split
  · exact hb
  · exact SeriesLimitLaws.small_neg hb

end ComputableAnalysis.ModularForms
