import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixAction
import ComputableAnalysis.RiemannHilbert.DomainVectorHolomorphicLaws
import ComputableAnalysis.RiemannHilbert.ConstantLinearFields

/-! Actual compositions of holomorphic matrix fields have holomorphic
entries. The proof evaluates the first field on rational basis vectors,
then applies the second field; it preserves arbitrary represented inputs
and allows different finite ranks and nested open domains. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
variable {n m k : Nat} {D E : Scalar → Prop}

def MatrixHolomorphic.congr {G : Field (n := n) (m := m) D}
    {hD : ∀ z w, z ≈ w → (D z ↔ D w)}
    {hG : ∀ z w hz hw, z ≈ w → (G z hz).Equiv (G w hw)}
    (h : MatrixHolomorphic G hD hG) (H : Field (n := n) (m := m) D)
    (hH : ∀ z w hz hw, z ≈ w → (H z hz).Equiv (H w hw))
    (hGH : ∀ z hz, (G z hz).Equiv (H z hz)) : MatrixHolomorphic H hD hH :=
  fun i j => (h i j).transfer (entryMap H hD hH i j) (fun _ hz => hz)
    ⟨(h i j).openDomain.radius,(h i j).openDomain.inside⟩
    (fun z hz => hGH z hz (Fiber.basis i) j)

def constantMatrixHolomorphic (hD : ScalarTopology.OpenData D) (N : ValueMap (Fiber n) (Fiber m)) :
    MatrixHolomorphic (n := n) (m := m) (constant D N) hD.invariant (fun _ _ _ _ _ => ValueMap.equiv_refl N) :=
  fun i j => DomainFunctions.constantOn_holomorphic hD (Fiber.coordinate (N.eval (Fiber.basis i)) j)

def appliedToConstant (G : Field (n := n) (m := m) D)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w))
    (hG : ∀ z w hz hw, z ≈ w → (G z hz).Equiv (G w hw)) (x : Fiber n) :
    DomainVectorFunctions.Map m :=
  action G hG (DomainVectorFunctions.constantOn D hD x) (fun _ hz => hz)

def appliedToConstant_holomorphic (G : Field (n := n) (m := m) D)
    (hD : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z ≈ w → (G z hz).Equiv (G w hw))
    (hlinear : ∀ z hz, IsLinear (G z hz)) (hM : MatrixHolomorphic G hD.invariant hG)
    (x : Fiber n) : DomainVectorFunctions.Holomorphic (appliedToConstant G hD.invariant hG x) :=
  action_holomorphic G hD.invariant hG hlinear hM _
    (DomainVectorFunctions.constantOn_holomorphic hD x) (fun _ hz => hz)

def composeFields (G : Field (n := n) (m := m) D) (H : Field (n := m) (m := k) E)
    (hDE : ∀ z, D z → E z) : Field (n := n) (m := k) D :=
  fun z hz => (G z hz).followedBy (H z (hDE z hz))

theorem composeFields_congr (G : Field (n := n) (m := m) D) (H : Field (n := m) (m := k) E)
    (hDE : ∀ z, D z → E z)
    (hG : ∀ z w hz hw, z ≈ w → (G z hz).Equiv (G w hw))
    (hH : ∀ z w hz hw, z ≈ w → (H z hz).Equiv (H w hw))
    (z w : Scalar) (hz : D z) (hw : D w) (hzw : z ≈ w) :
    (composeFields G H hDE z hz).Equiv (composeFields G H hDE w hw) :=
  ValueMap.followedBy_congr (hG z w hz hw hzw) (hH z w (hDE z hz) (hDE w hw) hzw)

def composeFields_holomorphic (G : Field (n := n) (m := m) D) (H : Field (n := m) (m := k) E)
    (hD : ScalarTopology.OpenData D) (hE : ∀ z w, z ≈ w → (E z ↔ E w))
    (hDE : ∀ z, D z → E z)
    (hG : ∀ z w hz hw, z ≈ w → (G z hz).Equiv (G w hw))
    (hH : ∀ z w hz hw, z ≈ w → (H z hz).Equiv (H w hw))
    (hGl : ∀ z hz, IsLinear (G z hz)) (hHl : ∀ z hz, IsLinear (H z hz))
    (hGM : MatrixHolomorphic G hD.invariant hG) (hHM : MatrixHolomorphic H hE hH) :
    MatrixHolomorphic (composeFields G H hDE) hD.invariant (composeFields_congr G H hDE hG hH) :=
  fun i j => (action_holomorphic H hE hH hHl hHM
    (appliedToConstant G hD.invariant hG (Fiber.basis i))
    (appliedToConstant_holomorphic G hD hG hGl hGM (Fiber.basis i)) hDE).coordinates j

end ComputableAnalysis.RiemannHilbert.LinearField
