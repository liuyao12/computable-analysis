import ComputableAnalysis.Basic

namespace ComputableAnalysis

namespace Polynomial

def eval (coeffs : List Rat) (x : Rat) : Rat := coeffs.foldr (fun c acc => c + x * acc) 0

def derivative : List Rat -> List Rat
  | [] => []
  | _ :: cs => cs.zipIdx.map (fun (c, i) => ((i + 1 : Nat) : Rat) * c)

def asFunRaw (coeffs : List Rat) : RealFunRaw := RealFunRaw.exact (eval coeffs)

end Polynomial

inductive RatExpr where
  | var
  | const (q : Rat)
  | neg (e : RatExpr)
  | add (a b : RatExpr)
  | mul (a b : RatExpr)
  | inv (e : RatExpr)
deriving Repr, DecidableEq

namespace RatExpr

def eval : RatExpr -> Rat -> Option Rat
  | var, x => some x
  | const q, _ => some q
  | neg e, x => (eval e x).map (fun y => -y)
  | add a b, x => match eval a x, eval b x with | some y, some z => some (y + z) | _, _ => none
  | mul a b, x => match eval a x, eval b x with | some y, some z => some (y * z) | _, _ => none
  | inv e, x => match eval e x with | some y => if y = 0 then none else some (1 / y) | none => none

def sub (a b : RatExpr) : RatExpr := add a (neg b)
def div (a b : RatExpr) : RatExpr := mul a (inv b)
def square : RatExpr := mul var var
def oneDivOnePlusSquare : RatExpr := inv (add (const 1) square)

end RatExpr

/-- A rational function as numerator and denominator polynomials.

The value is defined exactly on rational inputs where the denominator is
nonzero.  There is no placeholder value outside the domain.
-/
structure RatFun where
  num : List Rat
  den : List Rat

namespace RatFun

def denominator (f : RatFun) (x : Rat) : Rat := Polynomial.eval f.den x
def numerator (f : RatFun) (x : Rat) : Rat := Polynomial.eval f.num x
def DefinedAt (f : RatFun) (x : Rat) : Prop := f.denominator x != 0
def undefinedAt (f : RatFun) (x : Rat) : Bool := decide (f.denominator x = 0)

def eval? (f : RatFun) (x : Rat) : Option Rat :=
  let d := f.denominator x
  if d = 0 then none else some (f.numerator x / d)

def evalOnDomain (f : RatFun) (x : Rat) (_h : f.DefinedAt x) : Rat :=
  f.numerator x / f.denominator x

def polynomial (coeffs : List Rat) : RatFun where
  num := coeffs
  den := [1]

def oneOverX : RatFun where
  num := [1]
  den := [0, 1]

def oneOverOnePlusSquare : RatFun where
  num := [1]
  den := [1, 0, 1]

/-- `1 / (x^2 - 2)`.  It has no rational pole, but it should still fail the
interval-regularity certificate on `[1,2]`, because the denominator is not
apart from zero there. -/
def oneOverXSquareMinusTwo : RatFun where
  num := [1]
  den := [-2, 0, 1]

end RatFun

end ComputableAnalysis
