import ComputableAnalysis.RiemannHilbert.ExponentialFrameHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainVectorHolomorphicLaws

/-! Actual exponential frames in supplied holomorphic scalar coordinates.
The entire evaluator supplies both inverse fields; the actual chain rule
constructs derivatives and the pulled-back connection compatibility. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem
set_option maxHeartbeats 800000
variable {n : Nat}

def pullbackVector (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (g : DomainFunctions.Map) : DomainVectorFunctions.Map n where
  domain := g.domain
  eval z hz := (value A hA (g.eval z hz)).eval x
  domain_congr := g.domain_congr
  eval_congr z w hz hw hzw := value_congr A A hA hA (fun _ => Setoid.refl _) _ _
    (g.eval_congr z w hz hw hzw) x x (Setoid.refl _)

def pullbackVector_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g) :
    DomainVectorFunctions.Holomorphic (pullbackVector A hA x g) :=
  (DomainVectorFunctions.pullback_holomorphic (vector A hA x) (vector_holomorphic A hA x) g hg).transfer
    (pullbackVector A hA x g) (fun _ hz => ⟨hz,True.intro⟩)
    ⟨hg.openDomain.radius,hg.openDomain.inside⟩ (fun _ _ => Setoid.refl _)

theorem pullbackVector_derivative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g) (z : Scalar) (hz : g.domain z) :
    DomainVectorFunctions.derivative (pullbackVector A hA x g) (pullbackVector_holomorphic A hA x g hg) z hz ≈
      Fiber.scale (hg.derivative z hz) (A.eval ((value A hA (g.eval z hz)).eval x)) :=
  Setoid.trans (DomainVectorFunctions.pullback_derivative (vector A hA x) (vector_holomorphic A hA x) g hg z ⟨hz,True.intro⟩)
    (Fiber.scale_congr (equiv_refl _ (hg.derivative z hz).property) (vector_derivative_ode A hA x (g.eval z hz)))

def pullbackFrame (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (g : DomainFunctions.Map) :
    (z : Scalar) → g.domain z → LinearIso n n := fun z hz => frame A hA (g.eval z hz)

theorem pullback_forward_congr (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (g : DomainFunctions.Map)
    (z w : Scalar) (hz : g.domain z) (hw : g.domain w) (hzw : z.val.Equiv w.val) :
    (LinearField.forwardField (pullbackFrame A hA g) z hz).Equiv
      (LinearField.forwardField (pullbackFrame A hA g) w hw) :=
  frame_congr A A hA hA (fun _ => Setoid.refl _) _ _ (g.eval_congr z w hz hw hzw)

theorem pullback_inverse_congr (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (g : DomainFunctions.Map)
    (z w : Scalar) (hz : g.domain z) (hw : g.domain w) (hzw : z.val.Equiv w.val) :
    (LinearField.inverseField (pullbackFrame A hA g) z hz).Equiv
      (LinearField.inverseField (pullbackFrame A hA g) w hw) :=
  frame_backward_congr A A hA hA (fun _ => Setoid.refl _) _ _ (g.eval_congr z w hz hw hzw)

def pullback_forward_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g) :
    LinearField.MatrixHolomorphic (LinearField.forwardField (pullbackFrame A hA g))
      g.domain_congr (pullback_forward_congr A hA g) :=
  fun i j => (pullbackVector_holomorphic A hA (Fiber.basis i) g hg).coordinates j

def pullback_inverse_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g) :
    LinearField.MatrixHolomorphic (LinearField.inverseField (pullbackFrame A hA g))
      g.domain_congr (pullback_inverse_congr A hA g) :=
  fun i j => (pullbackVector_holomorphic (negativeOperator A) (negativeOperator_linear A hA) (Fiber.basis i) g hg).coordinates j

def pullbackCoefficient (A : ValueMap (Fiber n) (Fiber n)) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) : LinearField.Field (n := n) (m := n) g.domain :=
  fun z hz => A.followedBy (Fiber.scaleMap (hg.derivative z hz))

theorem pullbackCoefficient_linear (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g) (z : Scalar) (hz : g.domain z) :
    IsLinear (pullbackCoefficient A g hg z hz) := IsLinear.followedBy hA (Fiber.scaleMap_linear _)

theorem pullback_matrix_derivative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g)
    (hM : LinearField.MatrixHolomorphic (LinearField.forwardField (pullbackFrame A hA g))
      g.domain_congr (pullback_forward_congr A hA g)) (z : Scalar) (hz : g.domain z) :
    (LinearField.derivativeField hM z hz).Equiv
      ((LinearField.forwardField (pullbackFrame A hA g) z hz).followedBy (pullbackCoefficient A g hg z hz)) := by
  apply (ValueMap.linear_equiv_iff_basis _ _ (LinearField.derivativeField_linear hM z hz)
    (IsLinear.followedBy (value_linear A hA _) (pullbackCoefficient_linear A hA g hg z hz))).2
  intro i
  exact Setoid.trans (LinearField.derivativeField_unique hM (pullback_forward_holomorphic A hA g hg) z hz (Fiber.basis i))
    (Setoid.trans (ValueMap.ofColumns_basis (LinearField.derivativeColumn (pullback_forward_holomorphic A hA g hg) z hz) i)
      (pullbackVector_derivative A hA (Fiber.basis i) g hg z hz))

theorem pullback_forward_compatible (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g)
    (hM : LinearField.MatrixHolomorphic (LinearField.forwardField (pullbackFrame A hA g))
      g.domain_congr (pullback_forward_congr A hA g)) :
    LinearField.Compatible (LinearField.forwardField (pullbackFrame A hA g)) (LinearField.derivativeField hM)
      (fun _ _ => ValueMap.zeroBetween n n) (pullbackCoefficient A g hg) := by
  intro z hz x
  exact Setoid.trans (Fiber.add_congr (pullback_matrix_derivative A hA g hg hM z hz x)
    ((value_linear A hA _).zero)) (Fiber.add_zero _)

theorem pullback_inverse_derivative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g)
    (hN : LinearField.MatrixHolomorphic (LinearField.inverseField (pullbackFrame A hA g))
      g.domain_congr (pullback_inverse_congr A hA g)) (z : Scalar) (hz : g.domain z) (x : Fiber n) :
    (LinearField.derivativeField hN z hz).eval x ≈
      Fiber.neg ((pullbackCoefficient A g hg z hz).eval
        ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x)) := by
  have hd := pullback_matrix_derivative (negativeOperator A) (negativeOperator_linear A hA) g hg hN z hz x
  have hn : Fiber.scale (hg.derivative z hz) (Fiber.neg (A.eval
      ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x))) ≈
      Fiber.neg ((pullbackCoefficient A g hg z hz).eval
        ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x)) := by
    intro i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (Fiber.scale (hg.derivative z hz) (Fiber.neg (A.eval
        ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x)))).property i)
      (hright := (Fiber.neg ((pullbackCoefficient A g hg z hz).eval
        ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x))).property i)
    let D := ComplexRawQuotient.ofRaw (hg.derivative z hz).val (hg.derivative z hz).property
    let Y := ComplexRawQuotient.ofRaw ((A.eval
      ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x)).val i)
      ((A.eval ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x)).property i)
    change D*(-Y)= -(D*Y)
    grind only
  exact Setoid.trans hd (Setoid.trans (Fiber.scale_congr (equiv_refl _ (hg.derivative z hz).property)
    (negativeOperator_value A _)) hn)

theorem pullback_inverse_coefficient_commutes (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g) (z : Scalar) (hz : g.domain z) (x : Fiber n) :
    (LinearField.inverseField (pullbackFrame A hA g) z hz).eval ((pullbackCoefficient A g hg z hz).eval x) ≈
      (pullbackCoefficient A g hg z hz).eval ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x) := by
  let G := value (negativeOperator A) (negativeOperator_linear A hA) (g.eval z hz)
  have hs : G.eval (Fiber.scale (hg.derivative z hz) (A.eval x)) ≈
      Fiber.scale (hg.derivative z hz) (G.eval (A.eval x)) :=
    (value_linear (negativeOperator A) (negativeOperator_linear A hA) (g.eval z hz)).2 (hg.derivative z hz) (A.eval x)
  have hc : Fiber.scale (hg.derivative z hz) (G.eval (A.eval x)) ≈
      Fiber.scale (hg.derivative z hz) (A.eval (G.eval x)) :=
    Fiber.scale_congr (equiv_refl _ (hg.derivative z hz).property) (Setoid.symm (negative_exponential_commutes A hA (g.eval z hz) x))
  exact Setoid.trans hs hc

theorem pullback_inverse_compatible (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (hg : DomainFunctions.Holomorphic g)
    (hN : LinearField.MatrixHolomorphic (LinearField.inverseField (pullbackFrame A hA g))
      g.domain_congr (pullback_inverse_congr A hA g)) :
    LinearField.Compatible (LinearField.inverseField (pullbackFrame A hA g)) (LinearField.derivativeField hN)
      (pullbackCoefficient A g hg) (fun _ _ => ValueMap.zeroBetween n n) := by
  intro z hz x
  exact Setoid.trans (Fiber.add_congr (pullback_inverse_derivative A hA g hg hN z hz x)
      (pullback_inverse_coefficient_commutes A hA g hg z hz x))
    (Setoid.trans (Fiber.add_comm _ _) (fun i => add_neg_equiv _
      (((pullbackCoefficient A g hg z hz).eval
        ((LinearField.inverseField (pullbackFrame A hA g) z hz).eval x)).property i)))

theorem pullback_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (g : DomainFunctions.Map) (p : Scalar) (hp : g.domain p) (hg0 : (g.eval p hp).val.Equiv zero) :
    (LinearField.forwardField (pullbackFrame A hA g) p hp).Equiv ValueMap.identity := by
  intro x
  exact Setoid.trans (value_congr A A hA hA (fun _ => Setoid.refl _) _ ⟨zero, ofQComplex_valid _⟩
    hg0 x x (Setoid.refl _)) (value_initial A hA x)

end ComputableAnalysis.RiemannHilbert.MatrixExponential
