import ComputableAnalysis.RiemannHilbert.LinearFieldProductBounds

/-! The represented connection change of frame is constructed from the frame,
its derivative and the old operator. Its compatibility identity and linearity
are derived; no horizontal-solution correspondence is assumed. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory LocalSystem

namespace ValueMap
variable {n m : Nat}
def sum (f g : ValueMap (Fiber n) (Fiber m)) : ValueMap (Fiber n) (Fiber m) :=
  ⟨fun x => Fiber.add (f.eval x) (g.eval x), fun h => Fiber.add_congr (f.congr h) (g.congr h)⟩

theorem sum_linear (f g : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f) (hg : IsLinear g) :
    IsLinear (sum f g) :=
  ⟨fun x y => Setoid.trans (Fiber.add_congr (hf.1 x y) (hg.1 x y)) (Fiber.add_four _ _ _ _),
   fun c x => Setoid.trans (Fiber.add_congr (hf.2 c x) (hg.2 c x)) (Setoid.symm (Fiber.scale_add c _ _))⟩
end ValueMap

namespace LinearField
variable {n m : Nat} {D : Scalar → Prop}

def Compatible (G DG : Field (n := n) (m := m) D)
    (A : UniformSegment.OperatorField (n := n) D) (B : UniformSegment.OperatorField (n := m) D) : Prop :=
  ∀ z hz x, Fiber.add ((DG z hz).eval x) ((G z hz).eval ((A z hz).eval x)) ≈ (B z hz).eval ((G z hz).eval x)

def frameOperator (G : (z : Scalar) → D z → LinearIso n n)
    (DG : Field (n := n) (m := n) D) (A : UniformSegment.OperatorField (n := n) D) :
    UniformSegment.OperatorField (n := n) D :=
  fun z hz => (G z hz).toValueIso.backward.followedBy
    (ValueMap.sum (DG z hz) ((A z hz).followedBy (G z hz).toValueIso.forward))

theorem frameOperator_linear (G : (z : Scalar) → D z → LinearIso n n)
    (DG : Field (n := n) (m := n) D) (A : UniformSegment.OperatorField (n := n) D)
    (hDG : ∀ z hz, IsLinear (DG z hz)) (hA : ∀ z hz, IsLinear (A z hz)) :
    ∀ z hz, IsLinear (frameOperator G DG A z hz) :=
  fun z hz => IsLinear.followedBy (G z hz).inverse.linear
    (ValueMap.sum_linear _ _ (hDG z hz) (IsLinear.followedBy (hA z hz) (G z hz).linear))

/-- With the convention that the frame sends old values to new values, the
constructed operator is (G' + G A) G⁻¹. Its action on G x is proved exactly. -/
theorem frameOperator_compatible (G : (z : Scalar) → D z → LinearIso n n)
    (DG : Field (n := n) (m := n) D) (A : UniformSegment.OperatorField (n := n) D) :
    Compatible (fun z hz => (G z hz).toValueIso.forward) DG A (frameOperator G DG A) := by
  intro z hz x
  exact Setoid.symm
    ((ValueMap.sum (DG z hz) ((A z hz).followedBy (G z hz).toValueIso.forward)).congr
      ((G z hz).toValueIso.backward_forward x))

theorem frameOperator_bound (G : (z : Scalar) → D z → LinearIso n n)
    (DG : Field (n := n) (m := n) D) (A : UniformSegment.OperatorField (n := n) D)
    (P Q U V : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hG : ∀ z hz B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound ((G z hz).toValueIso.forward.eval x) (P*B))
    (hInv : ∀ z hz B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound ((G z hz).toValueIso.backward.eval x) (V*B))
    (hDG : ∀ z hz B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound ((DG z hz).eval x) (Q*B))
    (hA : ∀ z hz B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound ((A z hz).eval x) (U*B))
    (z : Scalar) (hz : D z) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((frameOperator G DG A z hz).eval x) (((Q+P*U)*V)*B) := by
  let y := (G z hz).toValueIso.backward.eval x
  have hy := hInv z hz B hB x hx
  have hVB := Rat.mul_nonneg hV hB
  have hs := bound_add (hDG z hz (V*B) hVB y hy)
    (hG z hz (U*(V*B)) (Rat.mul_nonneg hU hVB) ((A z hz).eval y) (hA z hz (V*B) hVB y hy))
  have he : Q*(V*B)+P*(U*(V*B))=((Q+P*U)*V)*B := by grind
  rw [he] at hs
  exact hs

theorem product_congr (G : Field (n := n) (m := m) D) (f : UniformSegment.Field (n := n) D)
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (hf : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw) :
    ∀ z w hz hw, z.val.Equiv w.val → product G f z hz ≈ product G f w hw :=
  fun z w hz hw hzw => Setoid.trans ((G z hz).congr (hf z w hz hw hzw)) (hG z w hz hw hzw (f w hw))

/-- Multiplying a supplied horizontal field by a compatible varying map
produces a horizontal field with an explicitly constructed uniform modulus. -/
theorem horizontal_product_remainder (G DG : Field (n := n) (m := m) D)
    (A : UniformSegment.OperatorField (n := n) D) (Bop : UniformSegment.OperatorField (n := m) D)
    (f : UniformSegment.Field (n := n) D) (hlinear : ∀ z hz, IsLinear (G z hz))
    (hcompat : Compatible G DG A Bop)
    (P Q U B : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((G z hz).eval x) (P*E))
    (hDGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((DG z hz).eval x) (Q*E))
    (hAbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((A z hz).eval x) (U*E))
    (hfB : ∀ z hz, CoordinateBound (f z hz) B)
    (deltaF deltaG : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val w.val) H.val → CoordinateBound (UniformSegment.remainder A f w z hw hz) (eps.val*H.val))
    (hGrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) H.val → ∀ E, 0 ≤ E → ∀ x, CoordinateBound x E →
        CoordinateBound (operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*E))
    (eps H : QPos) (w z : Scalar) (hw : D w) (hz : D z)
    (hH : H.val ≤ (productDelta P Q B (U*B) hP hQ hB (Rat.mul_nonneg hU hB) deltaF deltaG eps).val)
    (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (UniformSegment.remainder Bop (product G f) w z hw hz) (eps.val*H.val) := by
  let df : UniformSegment.Field (n := n) D := fun z hz => (A z hz).eval (f z hz)
  have hs := product_uniform_remainder G DG f df hlinear P Q B (U*B) hP hQ hB (Rat.mul_nonneg hU hB)
    hGbound hDGbound hfB (fun z hz => hAbound z hz B hB (f z hz) (hfB z hz)) deltaF deltaG hfrem hGrem eps H w z hw hz hH hzw
  let d : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
  exact bound_congr (Fiber.sub_congr (Setoid.refl _)
    (Fiber.scale_congr (a := d) (b := d) (equiv_refl _ d.property) (hcompat w hw (f w hw)))) hs

end LinearField
end ComputableAnalysis.RiemannHilbert
