import ComputableAnalysis.ModularForms.SquareContourVanishing

/-! Rational cancellation of the constant term in the squared-pole residue calculation. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory PDE.CauchyContour

def squaredPolePullback (edge : HalfEdge) (R u : Rat) : QComplex :=
  let q := QComplex.scaleRat R (point edge u)
  let iq := RationalReciprocal.inverse q
  QComplex.scaleRat (orientation edge)
    (QComplex.mul (QComplex.mul iq iq) (QComplex.scaleRat R (velocity edge)))

def squaredPoleDensity (R u : Rat) : QComplex :=
  (PDE.CauchyContour.square.map (fun e => squaredPolePullback e R u)).foldr QComplex.add QComplex.zero

theorem squaredPoleDensity_zero (R u : Rat) : squaredPoleDensity R u=QComplex.zero := by
  simp only [squaredPoleDensity,PDE.CauchyContour.square,List.map_cons,List.map_nil,
    List.foldr_cons,List.foldr_nil,squaredPolePullback,point,velocity,rotation,orientation,
    Bool.false_eq_true,↓reduceIte,QComplex.mul,QComplex.scaleRat,RationalReciprocal.inverse,
    QComplex.normSq,QComplex.add,QComplex.zero,QComplex.mk.injEq]
  constructor <;> grind [Rat.div_def]

def linearPolePullback (edge : HalfEdge) (R u : Rat) : QComplex :=
  let q := QComplex.scaleRat R (point edge u)
  let iq := RationalReciprocal.inverse q
  QComplex.scaleRat (orientation edge)
    (QComplex.mul (QComplex.mul q (QComplex.mul iq iq)) (QComplex.scaleRat R (velocity edge)))

def simplePolePullback (edge : HalfEdge) (R u : Rat) : QComplex :=
  QComplex.scaleRat (orientation edge)
    (QComplex.mul (RationalReciprocal.inverse (QComplex.scaleRat R (point edge u)))
      (QComplex.scaleRat R (velocity edge)))

theorem linearPolePullback_simple (edge : HalfEdge) (R u : Rat) (hR : 0<R) :
    linearPolePullback edge R u=simplePolePullback edge R u := by
  dsimp only [linearPolePullback,simplePolePullback]
  rw [←QComplex.mul_assoc_cert,RationalReciprocal.mul_inverse _
    (scaledSquarePoint_normSq_nonzero edge u R hR),QComplex.one_mul_cert]

theorem simplePolePullback_scale_invariant (edge : HalfEdge) (R u : Rat) (hR : 0<R) :
    simplePolePullback edge R u=pullback edge u := by
  have he : QComplex.sub (QComplex.add QComplex.zero (QComplex.scaleRat R (point edge u)))
      QComplex.zero=QComplex.scaleRat R (point edge u) := by
    simp only [QComplex.sub,QComplex.add,QComplex.neg,QComplex.zero,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  have h := scaledPullback_eq QComplex.zero R (Rat.ne_of_gt hR) edge u
  unfold scaledPullback at h
  rw [he] at h
  exact h

theorem linearPole_square_density (R u : Rat) (hR : 0<R) :
    (PDE.CauchyContour.square.map (fun e => linearPolePullback e R u)).foldr QComplex.add QComplex.zero=
      ⟨0,8*ArctanGeometry.integralKernel u⟩ := by
  have he : (fun e => linearPolePullback e R u)=(fun e => pullback e u) := by
    funext e
    rw [linearPolePullback_simple e R u hR,simplePolePullback_scale_invariant e R u hR]
  rw [he]
  exact density_exact u

end ComputableAnalysis.ModularForms

