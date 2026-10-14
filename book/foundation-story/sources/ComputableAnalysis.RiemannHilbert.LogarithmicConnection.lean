import ComputableAnalysis.RiemannHilbert.ExponentialPullback
import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic

/-! The actual simple-pole coefficient A/z on the represented punctured
plane. Its entries are genuinely holomorphic, and multiplication by z
clears the pole to the constant represented residue on every vector. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmicConnection
open ComplexRaw FunctionTheory NonzeroBoxSearch
variable {n : Nat}

def coefficient (A : ValueMap (Fiber n) (Fiber n)) : LinearField.Field (n := n) (m := n) Nonzero :=
  fun z hz => A.followedBy (Fiber.scaleMap (RepresentedReciprocal.inverse z hz))

theorem coefficient_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (z : Scalar) (hz : Nonzero z) :
    IsLinear (coefficient A z hz) := IsLinear.followedBy hA (Fiber.scaleMap_linear _)

theorem coefficient_congr (A : ValueMap (Fiber n) (Fiber n))
    (z w : Scalar) (hz : Nonzero z) (hw : Nonzero w) (hzw : z.val.Equiv w.val) :
    (coefficient A z hz).Equiv (coefficient A w hw) :=
  fun _x => Fiber.scale_congr (RepresentedReciprocal.inverse_congr z w hz hw hzw) (Setoid.refl _)

def coefficient_holomorphic (A : ValueMap (Fiber n) (Fiber n)) :
    LinearField.MatrixHolomorphic (coefficient A) nonzero_congr (coefficient_congr A) := fun i j =>
  let h := ReciprocalHolomorphic.holomorphic.productOn
    (DomainFunctions.ofCertifiedHolomorphic (LinearField.constantCoordinate_holomorphic A (Fiber.basis i) j))
    (fun _ _ => True.intro)
  h.transfer (LinearField.entryMap (coefficient A) nonzero_congr (coefficient_congr A) i j)
    (fun _ hz => hz) h.openDomain
    (fun z hz => equiv_refl _ (((coefficient A z hz).eval (Fiber.basis i)).property j))

theorem pole_removed (A : ValueMap (Fiber n) (Fiber n)) (z : Scalar) (hz : Nonzero z) (x : Fiber n) :
    Fiber.scale z ((coefficient A z hz).eval x) ≈ A.eval x := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hz).property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse z hz)
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Fiber.scale z ((coefficient A z hz).eval x)).property i) (hright := (A.eval x).property i)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz).val (RepresentedReciprocal.inverse z hz).property
  let X := ComplexRawQuotient.ofRaw ((A.eval x).val i) ((A.eval x).property i)
  change Z*R=1 at hi
  change Z*(R*X)=X
  grind only

def clearedField (A : ValueMap (Fiber n) (Fiber n)) : LinearField.Field (n := n) (m := n) (fun _ => True) :=
  LinearField.constant (fun _ => True) A

def clearedField_holomorphic (A : ValueMap (Fiber n) (Fiber n)) :
    LinearField.MatrixHolomorphic (clearedField A) (fun _ _ _ => Iff.rfl)
      (fun _ _ _ _ _ _ => Setoid.refl _) :=
  fun i j => DomainFunctions.ofCertifiedHolomorphic (LinearField.constantCoordinate_holomorphic A (Fiber.basis i) j)

theorem pole_removal_extends (A : ValueMap (Fiber n) (Fiber n)) (z : Scalar) (hz : Nonzero z) :
    ((coefficient A z hz).followedBy (Fiber.scaleMap z)).Equiv (clearedField A z True.intro) := pole_removed A z hz

end ComputableAnalysis.RiemannHilbert.LogarithmicConnection
