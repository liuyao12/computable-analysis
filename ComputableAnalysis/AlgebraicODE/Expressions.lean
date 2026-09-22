import ComputableAnalysis.ComplexInterval

/-! Finite polynomial expressions, evaluated by the project's rational complex
boxes and valid raw algorithms. Variables in an ODE are `x,y,y',y''`.
This syntax alone does not certify that supplied jets are derivatives. -/
namespace ComputableAnalysis.AlgebraicODE

inductive Expr (n : Nat) where
  | const : Rat → Expr n
  | var : Fin n → Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
deriving Repr

namespace Expr
def evalRat (v : Fin n → Rat) : Expr n → Rat
  | .const c => c
  | .var i => v i
  | .add p q => p.evalRat v + q.evalRat v
  | .neg p => -p.evalRat v
  | .mul p q => p.evalRat v * q.evalRat v

def evalComplex (v : Fin n → QComplex) : Expr n → QComplex
  | .const c => QComplex.ofRat c
  | .var i => v i
  | .add p q => QComplex.add (p.evalComplex v) (q.evalComplex v)
  | .neg p => QComplex.neg (p.evalComplex v)
  | .mul p q => QComplex.mul (p.evalComplex v) (q.evalComplex v)

def evalRaw (v : Fin n → ComplexRaw) : Expr n → ComplexRaw
  | .const c => ComplexRaw.ofQComplex (QComplex.ofRat c)
  | .var i => v i
  | .add p q => ComplexRaw.add (p.evalRaw v) (q.evalRaw v)
  | .neg p => ComplexRaw.neg (p.evalRaw v)
  | .mul p q => ComplexRaw.mul (p.evalRaw v) (q.evalRaw v)

theorem evalRaw_valid (p : Expr n) (v : Fin n → ComplexRaw)
    (hv : ∀ i, (v i).Valid) : (p.evalRaw v).Valid := by
  induction p with
  | const c => exact ComplexRaw.ofQComplex_valid _
  | var i => exact hv i
  | add p q hp hq => exact ComplexRaw.add_valid hp hq
  | neg p hp => exact ComplexRaw.neg_valid hp
  | mul p q hp hq => exact ComplexRaw.mul_valid hp hq

/-- Exact inputs produce exact boxes at every stage. This connects the
symbolic complex evaluator to the literal raw runtime. -/
theorem evalRaw_exact (p : Expr n) (v : Fin n → QComplex) :
    p.evalRaw (fun i => ComplexRaw.ofQComplex (v i)) =
      ComplexRaw.ofQComplex (p.evalComplex v) := by
  induction p with
  | const c => rfl
  | var i => rfl
  | add p q hp hq => simp only [evalRaw, evalComplex, hp, hq]; rfl
  | neg p hp => simp only [evalRaw, evalComplex, hp]; rfl
  | mul p q hp hq =>
      simp only [evalRaw, evalComplex, hp, hq]
      apply congrArg (fun f => ({ compute := f } : ComplexRaw))
      funext stage
      exact QBox.mul_point _ _

theorem evalComplex_ofRat (p : Expr n) (v : Fin n → Rat) :
    p.evalComplex (fun i => QComplex.ofRat (v i)) =
      QComplex.ofRat (p.evalRat v) := by
  induction p with
  | const c => rfl
  | var i => rfl
  | add p q hp hq =>
      simp only [evalComplex, evalRat, hp, hq]
      simp [QComplex.add, QComplex.ofRat]
      grind
  | neg p hp =>
      simp only [evalComplex, evalRat, hp]
      simp [QComplex.neg, QComplex.ofRat]
  | mul p q hp hq =>
      simp only [evalComplex, evalRat, hp, hq]
      simp [QComplex.mul, QComplex.ofRat]
      congr 1 <;> grind

theorem evalRaw_ofRat (p : Expr n) (v : Fin n → Rat) :
    p.evalRaw (fun i => ComplexRaw.ofQComplex (QComplex.ofRat (v i))) =
      ComplexRaw.ofQComplex (QComplex.ofRat (p.evalRat v)) := by
  rw [evalRaw_exact, evalComplex_ofRat]

/-- Polynomial residuals respect represented equality; no decision procedure
for equality of arbitrary computable numbers is assumed. -/
theorem evalRaw_equiv (p : Expr n) (v w : Fin n → ComplexRaw)
    (hv : ∀ i, (v i).Valid) (hw : ∀ i, (w i).Valid)
    (h : ∀ i, (v i).Equiv (w i)) :
    (p.evalRaw v).Equiv (p.evalRaw w) := by
  induction p with
  | const c => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | var i => exact h i
  | add p q hp hq => exact ComplexRaw.add_equiv hp hq
  | neg p hp => exact ComplexRaw.neg_equiv hp
  | mul p q hp hq =>
      exact ComplexRaw.mul_equiv (p.evalRaw_valid v hv) (p.evalRaw_valid w hw)
        (q.evalRaw_valid v hv) (q.evalRaw_valid w hw) hp hq
end Expr

abbrev Equation := Expr 4
def x : Equation := .var 0
def y : Equation := .var 1
def dy : Equation := .var 2
def ddy : Equation := .var 3

def Equation.Holds (p : Equation) (v : Fin 4 → ComplexRaw) : Prop :=
  (∀ i, (v i).Valid) ∧
    (p.evalRaw v).Equiv (ComplexRaw.ofQComplex QComplex.zero)

theorem Equation.holds_of_evalRat_zero (p : Equation) (v : Fin 4 → Rat)
    (h : p.evalRat v = 0) :
    p.Holds (fun i => ComplexRaw.ofQComplex (QComplex.ofRat (v i))) := by
  refine ⟨fun _ => ComplexRaw.ofQComplex_valid _, ?_⟩
  rw [Expr.evalRaw_ofRat, h]
  exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)

/-- A nonzero polynomial relation in independent and dependent variables.
An explicit nonzero evaluation rules out the vacuous zero polynomial. -/
structure AlgebraicRelation where
  polynomial : Expr 2
  witness : Fin 2 → Rat
  nonzero : polynomial.evalRat witness ≠ 0

def AlgebraicRelation.Holds (p : AlgebraicRelation)
    (z value : ComplexRaw) : Prop :=
  z.Valid ∧ value.Valid ∧
    (p.polynomial.evalRaw (fun i => if i.val = 0 then z else value)).Equiv
      (ComplexRaw.ofQComplex QComplex.zero)

end ComputableAnalysis.AlgebraicODE
