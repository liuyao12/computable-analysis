import ComputableAnalysis.RepresentedHolomorphicJet
import ComputableAnalysis.ComplexMultiplication

/-!
# Algebra of represented complex first jets

These operations lift the exact first-jet sum, product, scalar, and chain
rules to valid raw complex algorithms.  They are the algebraic layer of a
computable holomorphic chart certificate; convergence of finite analytic
approximants remains a separate field supplied by each chart construction.
-/

namespace ComputableAnalysis
namespace RepresentedHolomorphicJet
namespace FirstJet

def constant (value : QComplex) : FirstJet where
  value := ComplexRaw.ofQComplex value
  derivative := ComplexRaw.zero

def identity (value : ComplexRaw) : FirstJet where
  value := value
  derivative := ComplexRaw.one

def neg (jet : FirstJet) : FirstJet where
  value := ComplexRaw.neg jet.value
  derivative := ComplexRaw.neg jet.derivative

def add (left right : FirstJet) : FirstJet where
  value := ComplexRaw.add left.value right.value
  derivative := ComplexRaw.add left.derivative right.derivative

def scaleRat (scalar : Rat) (jet : FirstJet) : FirstJet where
  value := ComplexRaw.scaleRat scalar jet.value
  derivative := ComplexRaw.scaleRat scalar jet.derivative

/-- Represented product rule. -/
def mul (left right : FirstJet) : FirstJet where
  value := ComplexRaw.mul left.value right.value
  derivative := ComplexRaw.add
    (ComplexRaw.mul left.derivative right.value)
    (ComplexRaw.mul left.value right.derivative)

/-- Represented chain rule. `outer` is already evaluated at `inner.value`;
the agreement between those two inputs belongs to the surrounding chart
certificate. -/
def compose (outer inner : FirstJet) : FirstJet where
  value := outer.value
  derivative := ComplexRaw.mul outer.derivative inner.derivative

@[simp] theorem constant_value (value : QComplex) :
    (constant value).value = ComplexRaw.ofQComplex value := rfl

@[simp] theorem constant_derivative (value : QComplex) :
    (constant value).derivative = ComplexRaw.zero := rfl

@[simp] theorem identity_value (value : ComplexRaw) :
    (identity value).value = value := rfl

@[simp] theorem identity_derivative (value : ComplexRaw) :
    (identity value).derivative = ComplexRaw.one := rfl

@[simp] theorem add_value (left right : FirstJet) :
    (add left right).value = ComplexRaw.add left.value right.value := rfl

@[simp] theorem add_derivative (left right : FirstJet) :
    (add left right).derivative =
      ComplexRaw.add left.derivative right.derivative := rfl

@[simp] theorem mul_value (left right : FirstJet) :
    (mul left right).value = ComplexRaw.mul left.value right.value := rfl

@[simp] theorem mul_derivative (left right : FirstJet) :
    (mul left right).derivative = ComplexRaw.add
      (ComplexRaw.mul left.derivative right.value)
      (ComplexRaw.mul left.value right.derivative) := rfl

@[simp] theorem compose_value (outer inner : FirstJet) :
    (compose outer inner).value = outer.value := rfl

@[simp] theorem compose_derivative (outer inner : FirstJet) :
    (compose outer inner).derivative =
      ComplexRaw.mul outer.derivative inner.derivative := rfl

theorem constant_valid (value : QComplex) : (constant value).Valid :=
  ⟨ComplexRaw.ofQComplex_valid value,
    ComplexRaw.ofQComplex_valid QComplex.zero⟩

theorem identity_valid {value : ComplexRaw} (hvalue : value.Valid) :
    (identity value).Valid :=
  ⟨hvalue, ComplexRaw.ofQComplex_valid QComplex.one⟩

theorem neg_valid {jet : FirstJet} (hjet : jet.Valid) :
    (neg jet).Valid :=
  ⟨ComplexRaw.neg_valid hjet.1, ComplexRaw.neg_valid hjet.2⟩

theorem add_valid {left right : FirstJet}
    (hleft : left.Valid) (hright : right.Valid) :
    (add left right).Valid :=
  ⟨ComplexRaw.add_valid hleft.1 hright.1,
    ComplexRaw.add_valid hleft.2 hright.2⟩

theorem scaleRat_valid (scalar : Rat) {jet : FirstJet}
    (hjet : jet.Valid) : (scaleRat scalar jet).Valid :=
  ⟨ComplexRaw.scaleRat_valid hjet.1,
    ComplexRaw.scaleRat_valid hjet.2⟩

theorem mul_valid {left right : FirstJet}
    (hleft : left.Valid) (hright : right.Valid) :
    (mul left right).Valid := by
  constructor
  · exact ComplexRaw.mul_valid hleft.1 hright.1
  · exact ComplexRaw.add_valid
      (ComplexRaw.mul_valid hleft.2 hright.1)
      (ComplexRaw.mul_valid hleft.1 hright.2)

theorem compose_valid {outer inner : FirstJet}
    (houter : outer.Valid) (hinner : inner.Valid) :
    (compose outer inner).Valid :=
  ⟨houter.1, ComplexRaw.mul_valid houter.2 hinner.2⟩

theorem neg_equiv {left right : FirstJet} (h : left.Equiv right) :
    (neg left).Equiv (neg right) :=
  ⟨ComplexRaw.neg_equiv h.1, ComplexRaw.neg_equiv h.2⟩

theorem add_equiv {left left' right right' : FirstJet}
    (hleft : left.Equiv left') (hright : right.Equiv right') :
    (add left right).Equiv (add left' right') :=
  ⟨ComplexRaw.add_equiv hleft.1 hright.1,
    ComplexRaw.add_equiv hleft.2 hright.2⟩

theorem scaleRat_equiv (scalar : Rat) {left right : FirstJet}
    (h : left.Equiv right) :
    (scaleRat scalar left).Equiv (scaleRat scalar right) :=
  ⟨ComplexRaw.scaleRat_equiv h.1,
    ComplexRaw.scaleRat_equiv h.2⟩

theorem mul_equiv {left left' right right' : FirstJet}
    (hl : left.Valid) (hl' : left'.Valid)
    (hr : right.Valid) (hr' : right'.Valid)
    (hleft : left.Equiv left') (hright : right.Equiv right') :
    (mul left right).Equiv (mul left' right') := by
  constructor
  · exact ComplexRaw.mul_equiv hl.1 hl'.1 hr.1 hr'.1
      hleft.1 hright.1
  · apply ComplexRaw.add_equiv
    · exact ComplexRaw.mul_equiv hl.2 hl'.2 hr.1 hr'.1
        hleft.2 hright.1
    · exact ComplexRaw.mul_equiv hl.1 hl'.1 hr.2 hr'.2
        hleft.1 hright.2

theorem compose_equiv {outer outer' inner inner' : FirstJet}
    (ho : outer.Valid) (ho' : outer'.Valid)
    (hi : inner.Valid) (hi' : inner'.Valid)
    (houter : outer.Equiv outer') (hinner : inner.Equiv inner') :
    (compose outer inner).Equiv (compose outer' inner') :=
  ⟨houter.1,
    ComplexRaw.mul_equiv ho.2 ho'.2 hi.2 hi'.2
      houter.2 hinner.2⟩

end FirstJet
end RepresentedHolomorphicJet
end ComputableAnalysis
