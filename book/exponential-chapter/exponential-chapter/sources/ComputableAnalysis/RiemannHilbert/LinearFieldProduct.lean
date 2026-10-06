import ComputableAnalysis.RiemannHilbert.UniformSegmentUniqueness

/-! Exact finite algebra for a varying linear map applied to a vector field.
The product remainder is derived before any analytic estimate is used. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalSystem
variable {n m : Nat}

abbrev Field (D : Scalar → Prop) := (z : Scalar) → D z → ValueMap (Fiber n) (Fiber m)

def product {D : Scalar → Prop} (G : Field (n := n) (m := m) D)
    (f : UniformSegment.Field (n := n) D) : UniformSegment.Field (n := m) D :=
  fun z hz => (G z hz).eval (f z hz)

def slope {D : Scalar → Prop} (G DG : Field (n := n) (m := m) D)
    (f df : UniformSegment.Field (n := n) D) : UniformSegment.Field (n := m) D :=
  fun z hz => Fiber.add ((DG z hz).eval (f z hz)) ((G z hz).eval (df z hz))

def vectorRemainder {D : Scalar → Prop} (f df : UniformSegment.Field (n := n) D)
    (w z : Scalar) (hw : D w) (hz : D z) : Fiber n :=
  Fiber.sub (Fiber.sub (f z hz) (f w hw))
    (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ (df w hw))

def operatorRemainder {D : Scalar → Prop} (G DG : Field (n := n) (m := m) D)
    (w z : Scalar) (hw : D w) (hz : D z) (x : Fiber n) : Fiber m :=
  Fiber.sub (Fiber.sub ((G z hz).eval x) ((G w hw).eval x))
    (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ ((DG w hw).eval x))

/-- Exact product remainder, preserving operator application order. -/
theorem product_remainder {D : Scalar → Prop} (G DG : Field (n := n) (m := m) D)
    (f df : UniformSegment.Field (n := n) D) (hG : ∀ z hz, IsLinear (G z hz))
    (w z : Scalar) (hw : D w) (hz : D z) :
    vectorRemainder (product G f) (slope G DG f df) w z hw hz ≈
      Fiber.add
        (Fiber.add ((G z hz).eval (vectorRemainder f df w z hw hz))
          ((ValueMap.difference (G z hz) (G w hw)).eval
            (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ (df w hw))))
        (operatorRemainder G DG w z hw hz (f w hw)) := by
  let d : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
  have hleft : (G z hz).eval (vectorRemainder f df w z hw hz) ≈
      Fiber.sub (Fiber.sub ((G z hz).eval (f z hz)) ((G z hz).eval (f w hw)))
        (Fiber.scale d ((G z hz).eval (df w hw))) :=
    Setoid.trans ((hG z hz).sub _ _) (Fiber.sub_congr ((hG z hz).sub _ _) ((hG z hz).2 d (df w hw)))
  have hcross : (ValueMap.difference (G z hz) (G w hw)).eval (Fiber.scale d (df w hw)) ≈
      Fiber.sub (Fiber.scale d ((G z hz).eval (df w hw))) (Fiber.scale d ((G w hw).eval (df w hw))) :=
    Fiber.sub_congr ((hG z hz).2 d (df w hw)) ((hG w hw).2 d (df w hw))
  apply Setoid.trans (Fiber.sub_congr (Setoid.refl _) (Fiber.scale_add d _ _))
  apply Setoid.trans (b := Fiber.add
    (Fiber.add
      (Fiber.sub (Fiber.sub ((G z hz).eval (f z hz)) ((G z hz).eval (f w hw)))
        (Fiber.scale d ((G z hz).eval (df w hw))))
      (Fiber.sub (Fiber.scale d ((G z hz).eval (df w hw))) (Fiber.scale d ((G w hw).eval (df w hw)))))
    (operatorRemainder G DG w z hw hz (f w hw)))
  · intro i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (Fiber.sub (Fiber.sub ((G z hz).eval (f z hz)) ((G w hw).eval (f w hw)))
        (Fiber.add (Fiber.scale d ((DG w hw).eval (f w hw))) (Fiber.scale d ((G w hw).eval (df w hw))))).property i)
      (hright := (Fiber.add (Fiber.add
        (Fiber.sub (Fiber.sub ((G z hz).eval (f z hz)) ((G z hz).eval (f w hw)))
          (Fiber.scale d ((G z hz).eval (df w hw))))
        (Fiber.sub (Fiber.scale d ((G z hz).eval (df w hw))) (Fiber.scale d ((G w hw).eval (df w hw)))))
        (operatorRemainder G DG w z hw hz (f w hw))).property i)
    change
      (ComplexRawQuotient.ofRaw (((G z hz).eval (f z hz)).val i) (((G z hz).eval (f z hz)).property i)-
        ComplexRawQuotient.ofRaw (((G w hw).eval (f w hw)).val i) (((G w hw).eval (f w hw)).property i))-
      (ComplexRawQuotient.ofRaw d.val d.property*
        ComplexRawQuotient.ofRaw (((DG w hw).eval (f w hw)).val i) (((DG w hw).eval (f w hw)).property i)+
       ComplexRawQuotient.ofRaw d.val d.property*
        ComplexRawQuotient.ofRaw (((G w hw).eval (df w hw)).val i) (((G w hw).eval (df w hw)).property i)) = _
    change _ =
      (((ComplexRawQuotient.ofRaw (((G z hz).eval (f z hz)).val i) (((G z hz).eval (f z hz)).property i)-
        ComplexRawQuotient.ofRaw (((G z hz).eval (f w hw)).val i) (((G z hz).eval (f w hw)).property i))-
        ComplexRawQuotient.ofRaw d.val d.property*
          ComplexRawQuotient.ofRaw (((G z hz).eval (df w hw)).val i) (((G z hz).eval (df w hw)).property i))+
      (ComplexRawQuotient.ofRaw d.val d.property*
        ComplexRawQuotient.ofRaw (((G z hz).eval (df w hw)).val i) (((G z hz).eval (df w hw)).property i)-
       ComplexRawQuotient.ofRaw d.val d.property*
        ComplexRawQuotient.ofRaw (((G w hw).eval (df w hw)).val i) (((G w hw).eval (df w hw)).property i)))+
      ((ComplexRawQuotient.ofRaw (((G z hz).eval (f w hw)).val i) (((G z hz).eval (f w hw)).property i)-
        ComplexRawQuotient.ofRaw (((G w hw).eval (f w hw)).val i) (((G w hw).eval (f w hw)).property i))-
        ComplexRawQuotient.ofRaw d.val d.property*
          ComplexRawQuotient.ofRaw (((DG w hw).eval (f w hw)).val i) (((DG w hw).eval (f w hw)).property i))
    grind
  · exact Setoid.symm (Fiber.add_congr (Fiber.add_congr hleft hcross) (Setoid.refl _))

end ComputableAnalysis.RiemannHilbert.LinearField
