import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixAction

/-! Effective continuity of finite matrix products on a represented base.
Finite coordinate sums construct the moduli for actual linear evaluators,
including empty source or target ranks. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory DomainFunctions
variable {n m k : Nat} {D : Scalar → Prop}

def baseContinuous_congr {f g : ∀ z, D z → Scalar}
    (hf : DomainFunctions.ContinuousOn D f) (hfg : ∀ z hz, f z hz ≈ g z hz) :
    DomainFunctions.ContinuousOn D g where
  delta := hf.delta
  estimate a ha eps z hz hza := Small.congr
    (sub_valid (f z hz).property (f a ha).property)
    (sub_valid (g z hz).property (g a ha).property)
    (FunctionTheory.sub_congr (hfg z hz) (hfg a ha)) (hf.estimate a ha eps z hz hza)

def baseConstantContinuous (D : Scalar → Prop) (c : Scalar) :
    DomainFunctions.ContinuousOn D (fun _ _ => c) where
  delta _ _ eps := eps
  estimate _ _ eps _ _ _ := Small.congr (ofQComplex_valid _) (sub_valid c.property c.property)
    (equiv_symm (add_neg_equiv _ c.property)) (Small.zero (Rat.le_of_lt eps.property))

def basePrefixCoordinate (G : Field (n := n) (m := m) D)
    (f : ∀ z, D z → Fiber n) (r : Nat) (j : Fin m) (z : Scalar) (hz : D z) : Scalar :=
  Fiber.coordinate (ValueMap.imageBasisPrefix (G z hz) (f z hz) r) j

def basePrefixContinuous (G : Field (n := n) (m := m) D) (hG : MatrixContinuous G)
    (f : ∀ z, D z → Fiber n)
    (hf : ∀ i, DomainFunctions.ContinuousOn D (fun z hz => Fiber.coordinate (f z hz) i)) :
    (r : Nat) → (j : Fin m) → DomainFunctions.ContinuousOn D (basePrefixCoordinate G f r j)
  | 0, _ => baseConstantContinuous D ⟨zero,ofQComplex_valid _⟩
  | r+1, j => by
    by_cases hr : r < n
    · let i : Fin n := ⟨r,hr⟩
      have hterm := DomainFunctions.productContinuous
        (fun z hz => Fiber.coordinate (f z hz) i) (matrixEntry G i j) (hf i) (hG i j)
      have hsum := DomainFunctions.sumContinuous (basePrefixCoordinate G f r j)
        (fun z hz => DomainFunctions.scalarProduct (Fiber.coordinate (f z hz) i) (matrixEntry G i j z hz))
        (basePrefixContinuous G hG f hf r j) hterm
      apply baseContinuous_congr hsum
      intro z hz
      change (add ((ValueMap.imageBasisPrefix (G z hz) (f z hz) r).val j)
        (mul ((f z hz).val i) (((G z hz).eval (Fiber.basis i)).val j))).Equiv
        ((ValueMap.imageBasisPrefix (G z hz) (f z hz) (r+1)).val j)
      rw [ValueMap.imageBasisPrefix,dif_pos hr]
      exact equiv_refl _ (add_valid ((ValueMap.imageBasisPrefix (G z hz) (f z hz) r).property j)
        (mul_valid ((f z hz).property i) (((G z hz).eval (Fiber.basis i)).property j)))
    · apply baseContinuous_congr (basePrefixContinuous G hG f hf r j)
      intro z hz
      change ((ValueMap.imageBasisPrefix (G z hz) (f z hz) r).val j).Equiv
        ((ValueMap.imageBasisPrefix (G z hz) (f z hz) (r+1)).val j)
      rw [ValueMap.imageBasisPrefix,dif_neg hr]
      exact equiv_refl _ ((ValueMap.imageBasisPrefix (G z hz) (f z hz) r).property j)

def baseActionContinuous (G : Field (n := n) (m := m) D)
    (hlinear : ∀ z hz, IsLinear (G z hz)) (hG : MatrixContinuous G)
    (f : ∀ z, D z → Fiber n)
    (hf : ∀ i, DomainFunctions.ContinuousOn D (fun z hz => Fiber.coordinate (f z hz) i))
    (j : Fin m) :
    DomainFunctions.ContinuousOn D (fun z hz => Fiber.coordinate ((G z hz).eval (f z hz)) j) :=
  baseContinuous_congr (basePrefixContinuous G hG f hf n j)
    (fun z hz => Setoid.symm (ValueMap.matrix_action (G z hz) (hlinear z hz) (f z hz) j))

def matrixCompositionContinuous (G : Field (n := n) (m := m) D)
    (H : Field (n := m) (m := k) D)
    (hHlinear : ∀ z hz, IsLinear (H z hz)) (hG : MatrixContinuous G) (hH : MatrixContinuous H) :
    MatrixContinuous (fun z hz => (G z hz).followedBy (H z hz)) :=
  fun i j => baseActionContinuous H hHlinear hH (fun z hz => (G z hz).eval (Fiber.basis i))
    (fun r => hG i r) j

end ComputableAnalysis.RiemannHilbert.LinearField
