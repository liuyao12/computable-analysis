import ComputableAnalysis.ModularForms.SquareDerivativeRemainderBound

/-! Normalized finite contour bounds for the actual derivative remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squareMidpointParameter_unit (M v : Nat) (hM : 0<M) (hv : v<M) :
    0≤squareMidpointParameter M v ∧ squareMidpointParameter M v≤1 := by
  have hn : 0<(M:Rat) := Rat.natCast_pos.mpr hM
  have hi : 0≤(M:Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hn)
  have hc := Rat.natCast_le_natCast.mpr (show v+1≤M by omega)
  rw [Rat.natCast_add] at hc
  have hv0 : 0≤(v:Rat) := Rat.natCast_nonneg
  have hnum : (v:Rat)+1/2≤(M:Rat) := by change (v:Rat)+1≤(M:Rat) at hc; grind only
  have hlo := Rat.mul_nonneg (show 0≤(v:Rat)+1/2 by grind only) hi
  have hhi := Rat.mul_le_mul_of_nonneg_right hnum hi
  have he := Rat.mul_inv_cancel (M:Rat) (Rat.ne_of_gt hn)
  simp only [squareMidpointParameter,Rat.div_def]
  constructor
  · exact hlo
  · rw [he] at hhi; exact hhi

noncomputable def squareDerivativeRemainderHalfEdgeSum (c : Scalar) (edge : HalfEdge)
    (R : Rat) (M : Nat) : Scalar :=
  let terms := gridScalarSum M (fun v => squareDerivativeRemainderDensity c edge R
    (if edge.upper then squareMidpointParameter M v else 1-squareMidpointParameter M v))
  ⟨scaleRat ((M:Rat)⁻¹) terms.val,scaleRat_valid terms.property⟩

theorem squareDerivativeRemainderHalfEdgeSum_bound (c : Scalar) (edge : HalfEdge)
    (R eps : QPos) (M : Nat) (hM : 0<M)
    (hR : R.val≤((pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eps).val) :
    Small (squareDerivativeRemainderHalfEdgeSum c edge R.val M).val (8*eps.val) := by
  have hE : 0≤8*eps.val := Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property)
  have hb := gridScalarSum_bound M (fun v => squareDerivativeRemainderDensity c edge R.val
    (if edge.upper then squareMidpointParameter M v else 1-squareMidpointParameter M v)) (8*eps.val) hE (by
      intro v hv
      have hu := squareMidpointParameter_unit M v hM hv
      have hp : 0≤(if edge.upper then squareMidpointParameter M v else 1-squareMidpointParameter M v) ∧
          (if edge.upper then squareMidpointParameter M v else 1-squareMidpointParameter M v)≤1 := by
        split <;> constructor <;> grind only
      exact squareDerivativeRemainderDensity_bound c edge R eps _ hp.1 hp.2 hR)
  have hn : 0<(M:Rat) := Rat.natCast_pos.mpr hM
  have hs := LocalODE.small_scale (Rat.le_of_lt (Rat.inv_pos.mpr hn)) hb
  have he : (M:Rat)⁻¹*((M:Rat)*(8*eps.val))=8*eps.val := by
    have hc := Rat.inv_mul_cancel (M:Rat) (Rat.ne_of_gt hn)
    grind only
  rw [he] at hs
  exact hs

noncomputable def squareDerivativeRemainderEdgeList (c : Scalar) (R : Rat) (M : Nat) : List HalfEdge → Scalar
  | [] => ⟨zero,ofQComplex_valid _⟩
  | e::es => scalarSum (squareDerivativeRemainderHalfEdgeSum c e R M)
      (squareDerivativeRemainderEdgeList c R M es)

theorem squareDerivativeRemainderEdgeList_bound (c : Scalar) (R eps : QPos)
    (M : Nat) (hM : 0<M) (es : List HalfEdge)
    (hR : R.val≤((pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eps).val) :
    Small (squareDerivativeRemainderEdgeList c R.val M es).val ((es.length:Rat)*(8*eps.val)) := by
  induction es with
  | nil =>
    change Small zero (0*(8*eps.val))
    rw [Rat.zero_mul]
    exact Small.zero (by decide +kernel)
  | cons e es ih =>
    have hb := LocalODE.small_add (squareDerivativeRemainderHalfEdgeSum_bound c e R eps M hM hR) ih
    have he : 8*eps.val+(es.length:Rat)*(8*eps.val)=((es.length+1:Nat):Rat)*(8*eps.val) := by
      rw [Rat.natCast_add]
      change _=((es.length:Rat)+1)*(8*eps.val)
      grind only
    rw [he] at hb
    exact hb

theorem squareDerivativeRemainderContour_bound (c : Scalar) (R eps : QPos) (M : Nat) (hM : 0<M)
    (hR : R.val≤((pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eps).val) :
    Small (squareDerivativeRemainderEdgeList c R.val M PDE.CauchyContour.square).val (64*eps.val) := by
  have hb := squareDerivativeRemainderEdgeList_bound c R eps M hM PDE.CauchyContour.square hR
  have he : ((PDE.CauchyContour.square.length:Nat):Rat)*(8*eps.val)=64*eps.val := by
    change 8*(8*eps.val)=64*eps.val
    grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.ModularForms
