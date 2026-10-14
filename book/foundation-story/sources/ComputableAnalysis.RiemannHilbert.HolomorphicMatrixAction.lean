import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums
import ComputableAnalysis.RiemannHilbert.MatrixFieldJointContinuity
import ComputableAnalysis.RiemannHilbert.DomainVectorFunctions

/-! Holomorphic matrix fields act on actual represented holomorphic vector
fields. The finite sum/product construction is connected to the original
linear evaluator by exact matrix action, at every represented input. -/
namespace ComputableAnalysis.RiemannHilbert.ValueMap
variable {n m : Nat}

theorem imageBasisPrefix_congr_inputs (f g : ValueMap (Fiber n) (Fiber m))
    (hfg : f.Equiv g) (x y : Fiber n) (hxy : x ≈ y) (k : Nat) :
    imageBasisPrefix f x k ≈ imageBasisPrefix g y k := by
  induction k with
  | zero => exact Setoid.refl _
  | succ k ih =>
    rw [imageBasisPrefix,imageBasisPrefix]
    by_cases hk : k < n
    · rw [dif_pos hk,dif_pos hk]
      exact Fiber.add_congr ih (Fiber.scale_congr (hxy ⟨k,hk⟩) (hfg (Fiber.basis ⟨k,hk⟩)))
    · rw [dif_neg hk,dif_neg hk]
      exact ih

end ComputableAnalysis.RiemannHilbert.ValueMap

namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory DomainFunctions
variable {n m : Nat} {D : Scalar → Prop}

def entryMap (G : Field (n := n) (m := m) D)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w))
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (i : Fin n) (j : Fin m) : DomainFunctions.Map where
  domain := D
  eval := matrixEntry G i j
  domain_congr := hD
  eval_congr z w hz hw hzw := hG z w hz hw hzw (Fiber.basis i) j

abbrev MatrixHolomorphic (G : Field (n := n) (m := m) D)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w))
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw)) :=
  ∀ i j, DomainFunctions.Holomorphic (entryMap G hD hG i j)

def MatrixHolomorphic.continuous {G : Field (n := n) (m := m) D}
    {hD : ∀ z w, z ≈ w → (D z ↔ D w)}
    {hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw)}
    (h : MatrixHolomorphic G hD hG) : MatrixContinuous G :=
  fun i j => (h i j).continuous

def vectorOpenData (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f) :
    ScalarTopology.OpenData f.domain :=
  ⟨f.domain_congr,hf.openDomain.radius,hf.openDomain.inside⟩

def prefixMap (G : Field (n := n) (m := m) D)
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (f : DomainVectorFunctions.Map n) (hFD : ∀ z, f.domain z → D z) (k : Nat) (j : Fin m) :
    DomainFunctions.Map where
  domain := f.domain
  eval z hz := Fiber.coordinate (ValueMap.imageBasisPrefix (G z (hFD z hz)) (f.eval z hz) k) j
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := ValueMap.imageBasisPrefix_congr_inputs
    (G z (hFD z hz)) (G w (hFD w hw)) (hG z w _ _ hzw)
    (f.eval z hz) (f.eval w hw) (f.eval_congr z w hz hw hzw) k j

def prefixMap_holomorphic (G : Field (n := n) (m := m) D)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w))
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G hD hG) (f : DomainVectorFunctions.Map n)
    (hf : DomainVectorFunctions.Holomorphic f) (hFD : ∀ z, f.domain z → D z) :
    (k : Nat) → (j : Fin m) → DomainFunctions.Holomorphic (prefixMap G hG f hFD k j)
  | 0, j => (constantOn_holomorphic (vectorOpenData f hf) ⟨zero,ofQComplex_valid _⟩).transfer
      (prefixMap G hG f hFD 0 j) (fun _ hz => hz) ⟨hf.openDomain.radius,hf.openDomain.inside⟩
      (fun _ _ => equiv_refl _ (ofQComplex_valid _))
  | k+1, j => by
    by_cases hk : k < n
    · let i : Fin n := ⟨k,hk⟩
      have hentry := (hM i j).onDomain (vectorOpenData f hf) hFD
      have hterm := (hf.coordinates i).productOn hentry (fun _ hz => hz)
      have hsum := (prefixMap_holomorphic G hD hG hM f hf hFD k j).sumOn hterm (fun _ hz => hz)
      apply hsum.transfer (prefixMap G hG f hFD (k+1) j) (fun _ hz => hz)
        ⟨hf.openDomain.radius,hf.openDomain.inside⟩
      intro z hz
      change (add ((ValueMap.imageBasisPrefix (G z (hFD z hz)) (f.eval z hz) k).val j)
        (mul ((f.eval z hz).val i) (((G z (hFD z hz)).eval (Fiber.basis i)).val j))).Equiv
        ((ValueMap.imageBasisPrefix (G z (hFD z hz)) (f.eval z hz) (k+1)).val j)
      rw [ValueMap.imageBasisPrefix,dif_pos hk]
      exact equiv_refl _ (add_valid
        ((ValueMap.imageBasisPrefix (G z (hFD z hz)) (f.eval z hz) k).property j)
        (mul_valid ((f.eval z hz).property i) (((G z (hFD z hz)).eval (Fiber.basis i)).property j)))
    · apply (prefixMap_holomorphic G hD hG hM f hf hFD k j).transfer
        (prefixMap G hG f hFD (k+1) j) (fun _ hz => hz) ⟨hf.openDomain.radius,hf.openDomain.inside⟩
      intro z hz
      change ((ValueMap.imageBasisPrefix (G z (hFD z hz)) (f.eval z hz) k).val j).Equiv
        ((ValueMap.imageBasisPrefix (G z (hFD z hz)) (f.eval z hz) (k+1)).val j)
      rw [ValueMap.imageBasisPrefix,dif_neg hk]
      exact equiv_refl _ ((ValueMap.imageBasisPrefix (G z (hFD z hz)) (f.eval z hz) k).property j)

def action (G : Field (n := n) (m := m) D)
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (f : DomainVectorFunctions.Map n) (hFD : ∀ z, f.domain z → D z) : DomainVectorFunctions.Map m where
  domain := f.domain
  eval z hz := (G z (hFD z hz)).eval (f.eval z hz)
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := Setoid.trans
    ((G z (hFD z hz)).congr (f.eval_congr z w hz hw hzw))
    (hG z w _ _ hzw (f.eval w hw))

/-- The actual operator action preserves holomorphic vector fields.
Derivative moduli come from the proved finite sum/product rules and exact
value transfer; the domain and every valid represented input are retained. -/
def action_holomorphic (G : Field (n := n) (m := m) D)
    (hD : ∀ z w, z ≈ w → (D z ↔ D w))
    (hG : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (hlinear : ∀ z hz, IsLinear (G z hz)) (hM : MatrixHolomorphic G hD hG)
    (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f)
    (hFD : ∀ z, f.domain z → D z) : DomainVectorFunctions.Holomorphic (action G hG f hFD) where
  openDomain := ⟨hf.openDomain.radius,hf.openDomain.inside⟩
  coordinates j := (prefixMap_holomorphic G hD hG hM f hf hFD n j).transfer
    (DomainVectorFunctions.coordinate (action G hG f hFD) j) (fun _ hz => hz)
    ⟨hf.openDomain.radius,hf.openDomain.inside⟩
    (fun z hz => equiv_symm (ValueMap.matrix_action (G z (hFD z hz)) (hlinear z (hFD z hz)) (f.eval z hz) j))

end ComputableAnalysis.RiemannHilbert.LinearField
