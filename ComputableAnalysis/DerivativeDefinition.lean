import ComputableAnalysis.Holomorphic

/-!
# Derivatives as continuous divided differences

A derivative is the center value of a supplied represented divided difference,
continuous at that center. The factorization identifies the quotient away
from the center without deciding whether two represented values are equal.
Continuity of the derivative as a function of the center is a separate law.
-/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw

/-- Exact derivative specification by a continuous extension of the quotient.
The evaluator is valid and representation invariant on the original domain. -/
structure DerivativeAt (f : Map) (a d : ComplexRaw) where
  quotient : ComplexRaw → ComplexRaw
  quotient_valid : ∀ z, z.Valid → f.domain z → (quotient z).Valid
  quotient_congr : ∀ {z w}, z.Valid → w.Valid → f.domain z → f.domain w →
    z.Equiv w → (quotient z).Equiv (quotient w)
  quotient_continuous : ContinuousAt f.domain quotient a
  derivative_valid : d.Valid
  value_at : (quotient a).Equiv d
  factorization : ∀ z, z.Valid → f.domain z →
    (sub (f.eval z) (f.eval a)).Equiv (mul (sub z a) (quotient z))

def DerivativeAt.point_valid {f : Map} {a d : ComplexRaw} (h : DerivativeAt f a d) : a.Valid :=
  h.quotient_continuous.point_valid

def DerivativeAt.point_mem {f : Map} {a d : ComplexRaw} (h : DerivativeAt f a d) : f.domain a :=
  h.quotient_continuous.point_mem

/-- Differentiability throughout a domain, without assuming derivative continuity. -/
structure DifferentiableOn (f : Map) where
  derivative : ComplexRaw → ComplexRaw
  atPoint : ∀ a, a.Valid → f.domain a → DerivativeAt f a (derivative a)
  derivative_congr : ∀ {a b}, a.Valid → b.Valid → f.domain a → f.domain b →
    a.Equiv b → (derivative a).Equiv (derivative b)

end ComputableAnalysis.FunctionTheory

namespace ComputableAnalysis.RealFunctionTheory

/-- A real map with an explicit representation-invariant domain and evaluator. -/
structure Map where
  domain : RealRaw → Prop
  eval : RealRaw → RealRaw
  valid : ∀ x, x.Valid → domain x → (eval x).Valid
  domain_congr : ∀ {x y}, x.Valid → y.Valid → x.Equiv y → (domain x ↔ domain y)
  eval_congr : ∀ {x y}, x.Valid → y.Valid → domain x → domain y →
    x.Equiv y → (eval x).Equiv (eval y)

/-- Real derivative as the center value of a continuous divided difference. -/
structure DerivativeAt (f : Map) (a d : RealRaw) where
  quotient : RealRaw → RealRaw
  quotient_valid : ∀ y, y.Valid → f.domain y → (quotient y).Valid
  quotient_congr : ∀ {y z}, y.Valid → z.Valid → f.domain y → f.domain z →
    y.Equiv z → (quotient y).Equiv (quotient z)
  quotient_continuous : ContinuousAt f.domain quotient a
  derivative_valid : d.Valid
  value_at : (quotient a).Equiv d
  factorization : ∀ y, y.Valid → f.domain y →
    (f.eval y - f.eval a).Equiv ((y-a) * quotient y)

/-- Pointwise derivatives throughout the real domain; no derivative continuity field. -/
structure DifferentiableOn (f : Map) where
  derivative : RealRaw → RealRaw
  atPoint : ∀ a, a.Valid → f.domain a → DerivativeAt f a (derivative a)
  derivative_congr : ∀ {a b}, a.Valid → b.Valid → f.domain a → f.domain b →
    a.Equiv b → (derivative a).Equiv (derivative b)

end ComputableAnalysis.RealFunctionTheory
