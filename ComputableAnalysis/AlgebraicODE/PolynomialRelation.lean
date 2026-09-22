import ComputableAnalysis.AlgebraicODE.Expressions
import ComputableAnalysis.Polynomial

namespace ComputableAnalysis.AlgebraicODE

/-- Embed a rational Horner polynomial in the residual-expression language. -/
def polynomialExpression : List Rat → Expr 2
  | [] => .const 0
  | a :: p => .add (.const a) (.mul (.var 0) (polynomialExpression p))

theorem polynomialExpression_eval (p : List Rat) (v : Fin 2 → Rat) :
    (polynomialExpression p).evalRat v = Polynomial.eval p (v 0) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [polynomialExpression, Expr.evalRat, Polynomial.eval, List.foldr_cons]
      rw [ih]
      rfl


/-- Every finite rational polynomial has the nonvacuous graph relation
`y-P(x)=0`, with the explicit witness `(0,P(0)+1)`. -/
def polynomialGraph (p : List Rat) : AlgebraicRelation where
  polynomial := .add (.var 1) (.neg (polynomialExpression p))
  witness := fun i => if i.val = 0 then 0 else Polynomial.eval p 0 + 1
  nonzero := by
    simp only [Expr.evalRat, polynomialExpression_eval]
    change Polynomial.eval p 0 + 1 + -Polynomial.eval p 0 ≠ 0
    grind

theorem polynomialGraph_holds (p : List Rat) (x : Rat) :
    (polynomialGraph p).polynomial.evalRat
      (fun i => if i.val = 0 then x else Polynomial.eval p x) = 0 := by
  simp only [polynomialGraph, Expr.evalRat, polynomialExpression_eval]
  change Polynomial.eval p x + -Polynomial.eval p x = 0
  grind

end ComputableAnalysis.AlgebraicODE
