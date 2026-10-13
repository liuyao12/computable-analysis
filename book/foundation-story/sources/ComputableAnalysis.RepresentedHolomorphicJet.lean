import ComputableAnalysis.HolomorphicJet

/-!
# Represented complex first jets

This is the completion-level counterpart of `HolomorphicJet.FirstJet`.  Its
two components are raw complex algorithms.  Analytic chart modules attach
finite approximation certificates showing that the second component is the
derivative of the first; this file supplies only the common representation,
validity, and equivalence vocabulary.
-/

namespace ComputableAnalysis
namespace RepresentedHolomorphicJet

structure FirstJet where
  value : ComplexRaw
  derivative : ComplexRaw

namespace FirstJet

def Valid (jet : FirstJet) : Prop :=
  jet.value.Valid /\ jet.derivative.Valid

def Equiv (left right : FirstJet) : Prop :=
  left.value.Equiv right.value /\
    left.derivative.Equiv right.derivative

theorem equiv_refl (jet : FirstJet) (hjet : jet.Valid) : jet.Equiv jet :=
  ⟨ComplexRaw.equiv_refl jet.value hjet.1,
    ComplexRaw.equiv_refl jet.derivative hjet.2⟩

theorem equiv_symm {left right : FirstJet} :
    left.Equiv right -> right.Equiv left := by
  intro h
  exact ⟨ComplexRaw.equiv_symm h.1, ComplexRaw.equiv_symm h.2⟩

theorem equiv_trans {left middle right : FirstJet}
    (hleft : left.Valid) (hmiddle : middle.Valid) (hright : right.Valid) :
    left.Equiv middle -> middle.Equiv right -> left.Equiv right := by
  intro hlm hmr
  exact ⟨
    ComplexRaw.equiv_trans hleft.1 hmiddle.1 hright.1 hlm.1 hmr.1,
    ComplexRaw.equiv_trans hleft.2 hmiddle.2 hright.2 hlm.2 hmr.2⟩

/-- A represented first jet is self-derivative when its derivative component
represents the same complex value as its value component. -/
def SelfDerivative (jet : FirstJet) : Prop :=
  jet.derivative.Equiv jet.value

end FirstJet
end RepresentedHolomorphicJet
end ComputableAnalysis
