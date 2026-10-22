import ComputableAnalysis.RationalTriangleAreaTransform
open ComputableAnalysis ComputableAnalysis.RationalCircle

#check triangleSignedArea_affine
#print axioms triangleTwiceArea_affine
#print axioms triangleSignedArea_affine
#print axioms triangleSignedArea_SL2
#print axioms triangleSignedArea_singular
#print axioms triangleSignedArea_swap_coordinates
#print axioms TriangleLinearMap.determinant_compose
#print axioms TriangleLinearMap.dot_apply_gram

-- The same oriented unit triangle is sheared, scaled, reflected and collapsed.
private def p : PiCirclePoint := ⟨0,0⟩
private def q : PiCirclePoint := ⟨1,0⟩
private def r : PiCirclePoint := ⟨0,1⟩
private def shift : PiCirclePoint := ⟨7,-3⟩

example : triangleSignedArea p q r=1/2 := by decide +kernel
example : triangleSignedArea
    ((TriangleLinearMap.mk 1 2 0 1).affine shift p)
    ((TriangleLinearMap.mk 1 2 0 1).affine shift q)
    ((TriangleLinearMap.mk 1 2 0 1).affine shift r)=1/2 := by decide +kernel
example : triangleSignedArea
    ((TriangleLinearMap.mk 2 0 0 3).affine shift p)
    ((TriangleLinearMap.mk 2 0 0 3).affine shift q)
    ((TriangleLinearMap.mk 2 0 0 3).affine shift r)=3 := by decide +kernel
example : triangleSignedArea
    ((TriangleLinearMap.mk 0 1 1 0).affine shift p)
    ((TriangleLinearMap.mk 0 1 1 0).affine shift q)
    ((TriangleLinearMap.mk 0 1 1 0).affine shift r)=-(1/2) := by decide +kernel
example : triangleSignedArea
    ((TriangleLinearMap.mk 1 2 2 4).affine shift p)
    ((TriangleLinearMap.mk 1 2 2 4).affine shift q)
    ((TriangleLinearMap.mk 1 2 2 4).affine shift r)=0 := by decide +kernel
