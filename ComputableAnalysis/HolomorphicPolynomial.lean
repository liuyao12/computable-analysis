import ComputableAnalysis.HolomorphicCalculus
import ComputableAnalysis.Continuation.DifferentialEquation

/-! Polynomial computations and all their formal derivatives have actual
holomorphic witnesses. Coefficients may be arbitrary valid represented values. -/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw Continuation

def Map.constant (c : ComplexRaw) (hc : c.Valid) : Map where
  domain := fun _ => True
  eval := fun _ => c
  valid := fun _ _ _ => hc
  domain_congr := fun _ _ _ => Iff.rfl
  eval_congr := fun _ _ _ _ _ => equiv_refl c hc

def Map.identity : Map where
  domain := fun _ => True
  eval := id
  valid := fun _ hz _ => hz
  domain_congr := fun _ _ _ => Iff.rfl
  eval_congr := fun _ _ _ _ h => h

def constant_holomorphic (c : ComplexRaw) (hc : c.Valid) : Holomorphic (Map.constant c hc) :=
  (affine_holomorphic zero c (ofQComplex_valid _) hc).congr (fun _ => Iff.rfl) (by
    intro z hz _
    let v : Nat → ComplexRaw := fun n => if n=0 then c else z
    have hv : ∀ n, (v n).Valid := by intro n; dsimp [v]; split <;> assumption
    exact PolynomialExpr.identity (.add (.mul (.lit QComplex.zero) (.var 1)) (.var 0)) (.var 0) v hv (by
      intro p; simp only [PolynomialExpr.rational,QComplex.zero,QComplex.add,QComplex.mul]
      change _ = (⟨(p 0).re,(p 0).im⟩ : QComplex)
      congr 1 <;> grind))

def identity_holomorphic : Holomorphic Map.identity :=
  (affine_holomorphic one zero (ofQComplex_valid _) (ofQComplex_valid _)).congr (fun _ => Iff.rfl) (by
    intro z hz _
    exact PolynomialExpr.identity (.add (.mul (.lit QComplex.one) (.var 0)) (.lit QComplex.zero)) (.var 0)
      (fun _ => z) (fun _ => hz) (by
        intro p; simp only [PolynomialExpr.rational,QComplex.one,QComplex.zero,QComplex.add,QComplex.mul]
        change _ = (⟨(p 0).re,(p 0).im⟩ : QComplex)
        congr 1 <;> grind))

/-- Finite polynomial expressions, retaining executable represented coefficients. -/
inductive PolynomialFunction where
  | constant : Point → PolynomialFunction
  | input : PolynomialFunction
  | add : PolynomialFunction → PolynomialFunction → PolynomialFunction
  | mul : PolynomialFunction → PolynomialFunction → PolynomialFunction

namespace PolynomialFunction

def map : PolynomialFunction → Map
  | .constant c => Map.constant c.val c.property
  | .input => Map.identity
  | .add p q => p.map.add q.map
  | .mul p q => p.map.mul q.map

theorem entire (p : PolynomialFunction) (z : ComplexRaw) : p.map.domain z := by
  induction p with
  | constant c => trivial
  | input => trivial
  | add p q hp hq => exact ⟨hp,hq⟩
  | mul p q hp hq => exact ⟨hp,hq⟩

def holomorphic : (p : PolynomialFunction) → Holomorphic p.map
  | .constant c => constant_holomorphic c.val c.property
  | .input => identity_holomorphic
  | .add p q => p.holomorphic.add q.holomorphic
  | .mul p q => p.holomorphic.mul q.holomorphic

/-- Formal differentiation is justified below by the actual remainder calculus. -/
def diff : PolynomialFunction → PolynomialFunction
  | .constant _ => .constant ⟨zero,ofQComplex_valid _⟩
  | .input => .constant ⟨one,ofQComplex_valid _⟩
  | .add p q => .add p.diff q.diff
  | .mul p q => .add (.mul p.diff q) (.mul p q.diff)

theorem derivative_equiv (p : PolynomialFunction) (z : ComplexRaw) (hz : z.Valid) :
    (p.holomorphic.derivative z).Equiv (p.diff.map.eval z) := by
  induction p with
  | constant c => exact equiv_refl zero (ofQComplex_valid _)
  | input => exact equiv_refl one (ofQComplex_valid _)
  | add p q hp hq => exact add_equiv hp hq
  | mul p q hp hq =>
    exact add_equiv
      (mul_equiv (p.holomorphic.atPoint z hz (p.entire z)).derivative_valid
        (p.diff.map.valid z hz (p.diff.entire z)) (q.map.valid z hz (q.entire z))
        (q.map.valid z hz (q.entire z)) hp (equiv_refl _ (q.map.valid z hz (q.entire z))))
      (mul_equiv (p.map.valid z hz (p.entire z)) (p.map.valid z hz (p.entire z))
        (q.holomorphic.atPoint z hz (q.entire z)).derivative_valid (q.diff.map.valid z hz (q.diff.entire z))
        (equiv_refl _ (p.map.valid z hz (p.entire z))) hq)

def hasDerivative (p : PolynomialFunction) (z : ComplexRaw) (hz : z.Valid) :
    HasDerivativeAt p.map z (p.diff.map.eval z) :=
  (p.holomorphic.atPoint z hz (p.entire z)).congrDerivative
    (p.diff.map.valid z hz (p.diff.entire z)) (p.derivative_equiv z hz)

/-- The derivative map consumed by differential-equation clients is holomorphic. -/
def derivative_holomorphic (p : PolynomialFunction) : Holomorphic p.holomorphic.derivativeMap :=
  p.diff.holomorphic.congr (fun z => ⟨fun _ => p.entire z, fun _ => p.diff.entire z⟩)
    (fun z hz _ => equiv_symm (p.derivative_equiv z hz))

def iteratedDiff (p : PolynomialFunction) : Nat → PolynomialFunction
  | 0 => p
  | n+1 => (p.iteratedDiff n).diff

def iterated_hasDerivative (p : PolynomialFunction) (n : Nat) (z : ComplexRaw) (hz : z.Valid) :
    HasDerivativeAt (p.iteratedDiff n).map z ((p.iteratedDiff (n+1)).map.eval z) :=
  (p.iteratedDiff n).hasDerivative z hz

/-- Horner evaluation, with coefficients in increasing degree order. -/
def ofCoefficients : List Point → PolynomialFunction
  | [] => .constant ⟨zero,ofQComplex_valid _⟩
  | c :: cs => .add (.constant c) (.mul .input (ofCoefficients cs))

def horner (cs : List Point) (z : ComplexRaw) : ComplexRaw :=
  match cs with
  | [] => zero
  | c :: rest => ComplexRaw.add c.val (ComplexRaw.mul z (horner rest z))

theorem ofCoefficients_eval (cs : List Point) (z : ComplexRaw) :
    (ofCoefficients cs).map.eval z = horner cs z := by
  induction cs with
  | nil => rfl
  | cons c cs ih => change ComplexRaw.add c.val (ComplexRaw.mul z ((ofCoefficients cs).map.eval z)) = _; rw [ih]; rfl

def CoefficientsEquiv : List Point → List Point → Prop
  | [], [] => True
  | c :: cs, d :: ds => c.val.Equiv d.val ∧ CoefficientsEquiv cs ds
  | _, _ => False

/-- Changing coefficient representations as well as the input preserves the value. -/
theorem ofCoefficients_congr (cs ds : List Point)
    (hcs : CoefficientsEquiv cs ds)
    (z w : ComplexRaw) (hz : z.Valid) (hw : w.Valid) (hzw : z.Equiv w) :
    ((ofCoefficients cs).map.eval z).Equiv ((ofCoefficients ds).map.eval w) := by
  induction cs generalizing ds with
  | nil =>
    cases ds with
    | nil => exact equiv_refl zero (ofQComplex_valid _)
    | cons _ _ => exact False.elim hcs
  | cons c cs ih =>
    cases ds with
    | nil => exact False.elim hcs
    | cons d ds =>
      exact add_equiv hcs.1 (mul_equiv hz hw
        ((ofCoefficients cs).map.valid z hz ((ofCoefficients cs).entire z))
        ((ofCoefficients ds).map.valid w hw ((ofCoefficients ds).entire w)) hzw (ih ds hcs.2))

/-- A polynomial differential expression, with polynomial coefficients. -/
def secondOrder (A B C p : PolynomialFunction) : PolynomialFunction :=
  .add (.add (.mul A p.diff.diff) (.mul B p.diff)) (.mul C p)

/-- The formal polynomial expression agrees with the existing analytic ODE residual. -/
theorem secondOrder_equiv (A B C p : PolynomialFunction) (z : ComplexRaw) (hz : z.Valid) :
    (secondOrderResidual p.holomorphic p.derivative_holomorphic z
      (A.map.eval z) (B.map.eval z) (C.map.eval z)).Equiv ((secondOrder A B C p).map.eval z) := by
  have hA := A.map.valid z hz (A.entire z)
  have hB := B.map.valid z hz (B.entire z)
  have hC := C.map.valid z hz (C.entire z)
  exact add_equiv (add_equiv
    (mul_equiv hA hA (p.diff.holomorphic.atPoint z hz (p.diff.entire z)).derivative_valid
      (p.diff.diff.map.valid z hz (p.diff.diff.entire z)) (equiv_refl _ hA) (p.diff.derivative_equiv z hz))
    (mul_equiv hB hB (p.holomorphic.atPoint z hz (p.entire z)).derivative_valid
      (p.diff.map.valid z hz (p.diff.entire z)) (equiv_refl _ hB) (p.derivative_equiv z hz)))
    (equiv_refl _ (mul_valid hC (p.map.valid z hz (p.entire z))))

def secondOrder_holomorphic (A B C p : PolynomialFunction) : Holomorphic (secondOrder A B C p).map :=
  (secondOrder A B C p).holomorphic

end PolynomialFunction
end ComputableAnalysis.FunctionTheory
