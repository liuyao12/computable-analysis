import ComputableAnalysis.RationalCircle

/-! Rational affine transformation of the existing signed triangle area.
The factor is the signed determinant, including for orientation reversal.
The law holds for all matrices; invertible matrices give the GL2 action.
No metric, angle, or curved-region area law is used in these proofs. -/
namespace ComputableAnalysis.RationalCircle

structure TriangleLinearMap where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  deriving Repr, DecidableEq

namespace TriangleLinearMap

def determinant (M : TriangleLinearMap) : Rat := M.a*M.d-M.b*M.c

def apply (M : TriangleLinearMap) (p : PiCirclePoint) : PiCirclePoint :=
  ⟨M.a*p.x+M.b*p.y,M.c*p.x+M.d*p.y⟩

def affine (M : TriangleLinearMap) (shift p : PiCirclePoint) : PiCirclePoint :=
  ⟨(M.apply p).x+shift.x,(M.apply p).y+shift.y⟩

def compose (M N : TriangleLinearMap) : TriangleLinearMap :=
  ⟨M.a*N.a+M.b*N.c,M.a*N.b+M.b*N.d,
    M.c*N.a+M.d*N.c,M.c*N.b+M.d*N.d⟩

def transpose (M : TriangleLinearMap) : TriangleLinearMap := ⟨M.a,M.c,M.b,M.d⟩

theorem apply_compose (M N : TriangleLinearMap) (p : PiCirclePoint) :
    (compose M N).apply p=M.apply (N.apply p) := by
  cases p
  simp only [apply,compose,PiCirclePoint.mk.injEq]
  constructor <;> grind

theorem determinant_compose (M N : TriangleLinearMap) :
    (compose M N).determinant=M.determinant*N.determinant := by
  unfold determinant compose
  grind

theorem dot_apply_gram (M : TriangleLinearMap) (u v : PiCirclePoint) :
    Stage.dot (M.apply u) (M.apply v)=
      Stage.dot u ((compose M.transpose M).apply v) := by
  unfold Stage.dot apply compose transpose
  grind

end TriangleLinearMap

/-- Area retains vertex orientation. Its value can be negative. -/
def triangleSignedArea (p q r : PiCirclePoint) : Rat := triangleTwiceArea p q r/2

theorem triangleTwiceArea_affine (M : TriangleLinearMap)
    (shift p q r : PiCirclePoint) :
    triangleTwiceArea (M.affine shift p) (M.affine shift q) (M.affine shift r)=
      M.determinant*triangleTwiceArea p q r := by
  unfold triangleTwiceArea TriangleLinearMap.affine
    TriangleLinearMap.apply TriangleLinearMap.determinant
  grind

/-- GL2 determinant covariance, proved in the stronger form that also
allows singular matrices and degenerate triangles. Translation cancels. -/
theorem triangleSignedArea_affine (M : TriangleLinearMap)
    (shift p q r : PiCirclePoint) :
    triangleSignedArea (M.affine shift p) (M.affine shift q) (M.affine shift r)=
      M.determinant*triangleSignedArea p q r := by
  unfold triangleSignedArea
  rw [triangleTwiceArea_affine]
  grind

theorem triangleSignedArea_SL2 (M : TriangleLinearMap) (hM : M.determinant=1)
    (shift p q r : PiCirclePoint) :
    triangleSignedArea (M.affine shift p) (M.affine shift q) (M.affine shift r)=
      triangleSignedArea p q r := by
  rw [triangleSignedArea_affine,hM]
  grind

theorem triangleSignedArea_singular (M : TriangleLinearMap) (hM : M.determinant=0)
    (shift p q r : PiCirclePoint) :
    triangleSignedArea (M.affine shift p) (M.affine shift q) (M.affine shift r)=0 := by
  rw [triangleSignedArea_affine,hM]
  grind

/-- Swapping the coordinate axes has determinant negative one and negates
the signed area, without restricting the triangle's original orientation. -/
theorem triangleSignedArea_swap_coordinates (p q r : PiCirclePoint) :
    triangleSignedArea ⟨p.y,p.x⟩ ⟨q.y,q.x⟩ ⟨r.y,r.x⟩ =
      -triangleSignedArea p q r := by
  unfold triangleSignedArea
  have h := triangleTwiceArea_affine ⟨0,1,1,0⟩ ⟨0,0⟩ p q r
  simp only [TriangleLinearMap.affine,TriangleLinearMap.apply,
    TriangleLinearMap.determinant] at h
  unfold triangleTwiceArea at h ⊢
  grind

end ComputableAnalysis.RationalCircle
