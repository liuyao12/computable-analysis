import ComputableAnalysis.Basic

/-!
# A finite rational-complex triangle certificate

The vectors `(3,4)` and `(5,12)` have rational lengths `5` and `13`.  Their
sum has squared norm `320`, which is bounded by `(5+13)^2 = 324`.  This is a
concrete norm-level witness for item 91; the general norm theorem remains in
the reusable rational foundation.
-/

namespace ComputableAnalysis

def complexTriangleZ : QComplex := { re := 3, im := 4 }
def complexTriangleW : QComplex := { re := 5, im := 12 }

theorem complexTriangle_norms :
    QComplex.normSq complexTriangleZ = 25 /\
      QComplex.normSq complexTriangleW = 169 /\
      QComplex.normSq (QComplex.add complexTriangleZ complexTriangleW) = 320 := by
  native_decide

theorem complexTriangle_squared_norm_bound :
    QComplex.normSq (QComplex.add complexTriangleZ complexTriangleW) <=
      (5 + 13 : Rat) ^ 2 := by
  rw [complexTriangle_norms.2.2]
  native_decide

theorem complexTriangle_certificate :
    QComplex.normSq complexTriangleZ = 25 /\
      QComplex.normSq complexTriangleW = 169 /\
      QComplex.normSq (QComplex.add complexTriangleZ complexTriangleW) = 320 /\
      QComplex.normSq (QComplex.add complexTriangleZ complexTriangleW) <=
        (5 + 13 : Rat) ^ 2 := by
  exact ⟨complexTriangle_norms.1, complexTriangle_norms.2.1,
    complexTriangle_norms.2.2, complexTriangle_squared_norm_bound⟩

end ComputableAnalysis
