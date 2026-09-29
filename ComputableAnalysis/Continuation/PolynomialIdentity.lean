import ComputableAnalysis.Holomorphic

/-! Lift finite rational polynomial identities to valid represented inputs
by a shared rational sample in each stage box. No ring quotient is needed. -/
namespace ComputableAnalysis.Continuation
open ComplexRaw

inductive PolynomialExpr where
  | var : Nat → PolynomialExpr
  | lit : QComplex → PolynomialExpr
  | add : PolynomialExpr → PolynomialExpr → PolynomialExpr
  | neg : PolynomialExpr → PolynomialExpr
  | mul : PolynomialExpr → PolynomialExpr → PolynomialExpr
  | scale : Rat → PolynomialExpr → PolynomialExpr

namespace PolynomialExpr

def raw (v : Nat → ComplexRaw) : PolynomialExpr → ComplexRaw
  | .var n => v n
  | .lit c => ofQComplex c
  | .add a b => ComplexRaw.add (a.raw v) (b.raw v)
  | .neg a => ComplexRaw.neg (a.raw v)
  | .mul a b => ComplexRaw.mul (a.raw v) (b.raw v)
  | .scale r a => scaleRat r (a.raw v)

def rational (v : Nat → QComplex) : PolynomialExpr → QComplex
  | .var n => v n
  | .lit c => c
  | .add a b => QComplex.add (a.rational v) (b.rational v)
  | .neg a => QComplex.neg (a.rational v)
  | .mul a b => QComplex.mul (a.rational v) (b.rational v)
  | .scale r a => QComplex.scaleRat r (a.rational v)

theorem contains (e : PolynomialExpr) (v : Nat → ComplexRaw)
    (p : Nat → QComplex) (n : Nat)
    (h : ∀ i, ((v i).compute n).lo ≤ p i ∧ p i ≤ ((v i).compute n).hi) :
    ((e.raw v).compute n).lo ≤ e.rational p ∧
    e.rational p ≤ ((e.raw v).compute n).hi := by
  induction e with
  | var i => exact h i
  | lit c => exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | add a b ha hb => exact QBox.add_contains ha.1 ha.2 hb.1 hb.2
  | neg a ha =>
      rcases ha with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
      exact ⟨⟨Rat.neg_le_neg h3,Rat.neg_le_neg h4⟩,
        ⟨Rat.neg_le_neg h1,Rat.neg_le_neg h2⟩⟩
  | mul a b ha hb => exact QBox.mul_contains ha.1 ha.2 hb.1 hb.2
  | scale r a ha => exact QBox.scaleRat_contains ha.1 ha.2

theorem identity (e g : PolynomialExpr) (v : Nat → ComplexRaw)
    (hv : ∀ i, (v i).Valid) (he : ∀ p, e.rational p = g.rational p) :
    (e.raw v).Equiv (g.raw v) := by
  intro n
  let p := fun i => ((v i).compute n).center
  have hp := fun i => QBox.center_mem (valid_ordered (hv i) n)
  have hleft := e.contains v p n hp
  have hright := g.contains v p n hp
  rw [he p] at hleft
  apply (compareAt_overlap_iff _ _ n n).mpr
  exact ⟨QComplex.le_trans hleft.1 hright.2,QComplex.le_trans hright.1 hleft.2⟩

end PolynomialExpr
end ComputableAnalysis.Continuation
