import ComputableAnalysis.Basel.Proof
import ComputableAnalysis.Basel.PrimeCriterion

namespace ComputableAnalysis.Basel

/-- Irrationality of the square of geometric pi implies irrationality of
zeta at two, using the proved Basel theorem. -/
theorem zetaTwo_irrational_of_piSquare_irrational
    (hpi : (piCircleArea*piCircleArea).Irrational) :
    DirichletSeries.zetaTwoRaw.Irrational :=
  zetaTwo_irrational_of_basel_of_piSquare_irrational eulerBasel hpi

/-- **Infinitude of primes via Basel and Euler's product**, conditional only
on irrationality of the square of geometric pi. -/
theorem prime_unbounded_of_piSquare_irrational
    (hpi : (piCircleArea*piCircleArea).Irrational) (bound : Nat) :
    ∃p, BasicPrime p ∧ bound<p :=
  prime_unbounded_of_zetaTwo_irrational (zetaTwo_irrational_of_piSquare_irrational hpi) bound

end ComputableAnalysis.Basel
