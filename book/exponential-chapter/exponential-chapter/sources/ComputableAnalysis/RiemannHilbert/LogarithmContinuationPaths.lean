import ComputableAnalysis.RiemannHilbert.LogarithmContinuation
import ComputableAnalysis.RiemannHilbert.ScalarPaths

/-! Whole-route coverage of logarithm continuation on all valid represented
real path parameters. The path is constructed from affine edges, and every
point is proved to avoid zero. -/
namespace ComputableAnalysis.RiemannHilbert.RelativeLogarithm
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch

theorem point_represented_affine (c : Scalar) (hc : Nonzero c) (p q : Scalar) (t : UnitInterval.Point) :
    (point c hc (RepresentedAffineSegment.point p q t)).val.Equiv
      (RepresentedAffineSegment.point (point c hc p) (point c hc q) t).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (point c hc (RepresentedAffineSegment.point p q t)).property)
    (hright := (RepresentedAffineSegment.point (point c hc p) (point c hc q) t).property)
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let T := ComplexRawQuotient.ofRaw (UnitInterval.scalar t).val (UnitInterval.scalar t).property
  change -1+R*(P+(Q-P)*T)=(-1+R*P)+((-1+R*Q)-(-1+R*P))*T
  grind only

theorem represented_disc_mem (R : QPos) (p q : Scalar) (hp : interior R.val p) (hq : interior R.val q)
    (t : UnitInterval.Point) : interior R.val (RepresentedAffineSegment.point p q t) := by
  have hc := RepresentedAffineSegment.mem ⟨zero,ofQComplex_valid _⟩ p q R.val
    (Centered.interior_congr R.val p (Centered.offset ⟨zero,ofQComplex_valid _⟩ p)
      (equiv_symm (MatrixExponential.offset_zero p)) hp)
    (Centered.interior_congr R.val q (Centered.offset ⟨zero,ofQComplex_valid _⟩ q)
      (equiv_symm (MatrixExponential.offset_zero q)) hq) t
  exact Centered.interior_congr R.val _ _ (MatrixExponential.offset_zero _) hc

theorem represented_affine_mem (c : Scalar) (hc : Nonzero c) (p q : Scalar)
    (hp : domain c hc p) (hq : domain c hc q) (t : UnitInterval.Point) :
    domain c hc (RepresentedAffineSegment.point p q t) :=
  Centered.interior_congr LocalLogarithm.radius.val _ _ (equiv_symm (point_represented_affine c hc p q t))
    (represented_disc_mem LocalLogarithm.radius (point c hc p) (point c hc q) hp hq t)

end ComputableAnalysis.RiemannHilbert.RelativeLogarithm

namespace ComputableAnalysis.RiemannHilbert.LogarithmContinuation
open ComplexRaw FunctionTheory LocalODE NonzeroBoxSearch

theorem edge_path_mem (c d : Scalar) (hc : Nonzero c) (hcd : RelativeLogarithm.domain c hc d)
    (t : UnitInterval.Point) : RelativeLogarithm.domain c hc ((ScalarPaths.affine c d).eval t) :=
  RelativeLogarithm.represented_affine_mem c hc c d (RelativeLogarithm.center_mem c hc) hcd t

def path {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d} : Chain c hc d hd → ScalarPaths.Path c d
  | .nil c _ => ScalarPaths.constant c
  | @Chain.step c d e _hc hd he _ tail => ScalarPaths.concatenate (ScalarPaths.affine c d) (path tail)

theorem path_nonzero {c d : Scalar} {hc : Nonzero c} {hd : Nonzero d}
    (p : Chain c hc d hd) (t : UnitInterval.Point) : Nonzero ((path p).eval t) := by
  induction p generalizing t with
  | nil c hc => exact hc
  | @step c d e hc hd he hcd tail ih =>
      exact ScalarPathConcatenation.image (ScalarPaths.affine c d).eval (path tail).eval d
        (ScalarPaths.affine c d).congr (path tail).congr (ScalarPaths.affine c d).target (path tail).source
        Nonzero (fun z w h => nonzero_congr z w h)
        (fun s => RelativeLogarithm.nonzero c hc _ (edge_path_mem c d hc hcd s)) ih t

end ComputableAnalysis.RiemannHilbert.LogarithmContinuation
