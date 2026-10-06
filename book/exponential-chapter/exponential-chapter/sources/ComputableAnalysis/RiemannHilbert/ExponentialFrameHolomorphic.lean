import ComputableAnalysis.RiemannHilbert.ExponentialInverse
import ComputableAnalysis.RiemannHilbert.InverseFieldHolomorphic

/-! The proved exponential isomorphisms form an entire holomorphic frame.
Both actual matrix derivatives and the inverse derivative formula are exact
and independent of the supplied holomorphic witnesses. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def frameField (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    (z : Scalar) → True → LinearIso n n := fun z _ => frame A hA z

theorem frame_forward_congr (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z w : Scalar) (_hz _hw : True) (hzw : z.val.Equiv w.val) :
    (LinearField.forwardField (frameField A hA) z _hz).Equiv
      (LinearField.forwardField (frameField A hA) w _hw) := field_congr A hA z w _hz _hw hzw

theorem frame_inverse_congr (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z w : Scalar) (_hz _hw : True) (hzw : z.val.Equiv w.val) :
    (LinearField.inverseField (frameField A hA) z _hz).Equiv
      (LinearField.inverseField (frameField A hA) w _hw) :=
  field_congr (negativeOperator A) (negativeOperator_linear A hA) z w _hz _hw hzw

def frame_forward_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    LinearField.MatrixHolomorphic (LinearField.forwardField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_forward_congr A hA) := field_holomorphic A hA

def frame_inverse_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    LinearField.MatrixHolomorphic (LinearField.inverseField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_inverse_congr A hA) :=
  field_holomorphic (negativeOperator A) (negativeOperator_linear A hA)

theorem frame_forward_derivative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hM : LinearField.MatrixHolomorphic (LinearField.forwardField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_forward_congr A hA)) (z : Scalar) :
    (LinearField.derivativeField hM z True.intro).Equiv
      ((LinearField.forwardField (frameField A hA) z True.intro).followedBy A) :=
  field_derivative_ode A hA hM z

theorem frame_inverse_derivative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hN : LinearField.MatrixHolomorphic (LinearField.inverseField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_inverse_congr A hA)) (z : Scalar) (x : Fiber n) :
    (LinearField.derivativeField hN z True.intro).eval x ≈
      Fiber.neg (A.eval ((LinearField.inverseField (frameField A hA) z True.intro).eval x)) :=
  Setoid.trans (field_derivative_ode (negativeOperator A) (negativeOperator_linear A hA) hN z x)
    (negativeOperator_value A _)

/-- The usual inverse derivative formula, for the constructed entire frame
and arbitrary genuine entrywise holomorphic witnesses on both fields. -/
theorem frame_inverse_derivative_formula (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hM : LinearField.MatrixHolomorphic (LinearField.forwardField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_forward_congr A hA))
    (hN : LinearField.MatrixHolomorphic (LinearField.inverseField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_inverse_congr A hA)) (z : Scalar) :
    (LinearField.derivativeField hN z True.intro).Equiv
      (LinearField.inverseSlope (frameField A hA) (LinearField.derivativeField hM) z True.intro) := by
  intro x
  let G := LinearField.inverseField (frameField A hA) z True.intro
  have hs : G.eval ((LinearField.derivativeField hM z True.intro).eval (G.eval x)) ≈
      A.eval (G.eval x) :=
    Setoid.trans (G.congr (frame_forward_derivative A hA hM z (G.eval x)))
      (Setoid.trans (G.congr (A.congr (value_after_negative A hA z x)))
        (Setoid.symm (negative_exponential_commutes A hA z x)))
  have hn : (LinearField.inverseSlope (frameField A hA) (LinearField.derivativeField hM) z True.intro).eval x ≈
      Fiber.neg (A.eval (G.eval x)) :=
    Setoid.trans (Fiber.sub_congr (Setoid.refl _) hs)
      (fun i => zero_add_equiv _ (neg_valid ((A.eval (G.eval x)).property i)))
  exact Setoid.trans (frame_inverse_derivative A hA hN z x) (Setoid.symm hn)

theorem frame_forward_compatible (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hM : LinearField.MatrixHolomorphic (LinearField.forwardField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_forward_congr A hA)) :
    LinearField.Compatible (LinearField.forwardField (frameField A hA)) (LinearField.derivativeField hM)
      (fun _ _ => ValueMap.zeroBetween n n) (fun _ _ => A) := by
  intro z _ x
  exact Setoid.trans (Fiber.add_congr (frame_forward_derivative A hA hM z x)
    ((value_linear A hA z).zero)) (Fiber.add_zero _)

theorem frame_inverse_compatible (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hN : LinearField.MatrixHolomorphic (LinearField.inverseField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_inverse_congr A hA)) :
    LinearField.Compatible (LinearField.inverseField (frameField A hA)) (LinearField.derivativeField hN)
      (fun _ _ => A) (fun _ _ => ValueMap.zeroBetween n n) := by
  intro z _ x
  exact Setoid.trans (Fiber.add_congr (frame_inverse_derivative A hA hN z x)
      (Setoid.symm (negative_exponential_commutes A hA z x)))
    (Setoid.trans (Fiber.add_comm _ _) (fun i => add_neg_equiv _
      ((A.eval ((value (negativeOperator A) (negativeOperator_linear A hA) z).eval x)).property i)))

theorem frame_inverse_horizontal (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hN : LinearField.MatrixHolomorphic (LinearField.inverseField (frameField A hA))
      (fun _ _ _ => Iff.rfl) (frame_inverse_congr A hA))
    (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f)
    (hsource : CoordinateConnection.Horizontal f hf (fun _ _ => A)) :
    CoordinateConnection.Horizontal
      (LinearField.action (LinearField.inverseField (frameField A hA)) (frame_inverse_congr A hA) f
        (fun _ _ => True.intro))
      (LinearField.action_holomorphic _ (fun _ _ _ => Iff.rfl) (frame_inverse_congr A hA)
        (fun z _ => value_linear (negativeOperator A) (negativeOperator_linear A hA) z)
        hN f hf (fun _ _ => True.intro))
      (fun _ _ => ValueMap.zeroBetween n n) :=
  LinearField.horizontal_action
    (fun z _ => value_linear (negativeOperator A) (negativeOperator_linear A hA) z)
    hN (fun _ _ => A) (fun _ _ => ValueMap.zeroBetween n n) (frame_inverse_compatible A hA hN)
    f hf (fun _ _ => True.intro) hsource

theorem frame_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    (LinearField.forwardField (frameField A hA) ⟨zero, ofQComplex_valid _⟩ True.intro).Equiv ValueMap.identity :=
  value_initial A hA

theorem frame_inverse_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    (LinearField.inverseField (frameField A hA) ⟨zero, ofQComplex_valid _⟩ True.intro).Equiv ValueMap.identity :=
  value_initial (negativeOperator A) (negativeOperator_linear A hA)

end ComputableAnalysis.RiemannHilbert.MatrixExponential
