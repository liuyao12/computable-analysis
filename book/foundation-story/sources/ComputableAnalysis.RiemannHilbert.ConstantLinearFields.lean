import ComputableAnalysis.RiemannHilbert.LinearFieldProduct
import ComputableAnalysis.RiemannHilbert.NilpotentShearHolomorphic
import ComputableAnalysis.RiemannHilbert.LinearDifference

/-! Actual constant linear maps have zero uniform derivative error and
holomorphic coordinate evaluators, at arbitrary represented fiber values. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory LocalSystem

namespace ValueMap
def zeroBetween (n m : Nat) : ValueMap (Fiber n) (Fiber m) :=
  ⟨fun _ => Fiber.zero m, fun _ => Setoid.refl _⟩

theorem zeroBetween_linear (n m : Nat) : IsLinear (zeroBetween n m) :=
  ⟨fun _ _ => Setoid.symm (Fiber.zero_add (Fiber.zero m)),
    fun s _ => Setoid.symm (Fiber.scale_zero s)⟩
end ValueMap

namespace LinearField
variable {n m : Nat}

def constant (D : Scalar → Prop) (N : ValueMap (Fiber n) (Fiber m)) : Field (n := n) (m := m) D :=
  fun _ _ => N

theorem constant_remainder_zero (D : Scalar → Prop) (N : ValueMap (Fiber n) (Fiber m))
    (w z : Scalar) (hw : D w) (hz : D z) (x : Fiber n) :
    CoordinateBound (operatorRemainder (constant D N) (constant D (ValueMap.zeroBetween n m)) w z hw hz x) 0 := by
  let d : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
  have hs : CoordinateBound (Fiber.scale d (Fiber.zero m)) 0 :=
    bound_congr (Setoid.symm (Fiber.scale_zero d)) (bound_zero 0 (by decide +kernel))
  have hh := bound_sub (Fiber.sub_zero_bound (Setoid.refl (N.eval x))) hs
  change CoordinateBound (Fiber.sub (Fiber.sub (N.eval x) (N.eval x)) (Fiber.scale d (Fiber.zero m))) 0
  simpa only [Rat.zero_add] using hh

theorem constant_uniform_remainder (D : Scalar → Prop) (N : ValueMap (Fiber n) (Fiber m))
    (eps H : QPos) (w z : Scalar) (hw : D w) (hz : D z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) :
    CoordinateBound (operatorRemainder (constant D N) (constant D (ValueMap.zeroBetween n m)) w z hw hz x)
      ((eps.val*H.val)*E) :=
  fun i => (constant_remainder_zero D N w z hw hz x i).mono
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property)) hE)

def constantCoordinate (N : ValueMap (Fiber n) (Fiber m)) (x : Fiber n) (i : Fin m) : CertifiedFunctions.Map :=
  NilpotentShear.affineCoordinate (fun _ => N.eval x) (fun _ _ _ => Setoid.refl (N.eval x)) i

def constantCoordinate_holomorphic (N : ValueMap (Fiber n) (Fiber m)) (x : Fiber n) (i : Fin m) :
    CertifiedFunctions.Holomorphic (constantCoordinate N x i) :=
  NilpotentShear.affineCoordinate_holomorphic _ _ (Fiber.zero m)
    (fun _ _ => Setoid.trans (Fiber.bound_zero_equiv (Fiber.sub_zero_bound (Setoid.refl (N.eval x))))
      (Setoid.symm (Fiber.scale_zero _))) i

theorem constantCoordinate_value (N : ValueMap (Fiber n) (Fiber m)) (x : Fiber n) (i : Fin m) (z : Scalar) :
    (constantCoordinate N x i).eval z = (N.eval x).val i := rfl

end LinearField
end ComputableAnalysis.RiemannHilbert
