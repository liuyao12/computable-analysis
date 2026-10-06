import ComputableAnalysis.RiemannHilbert.TranslatedHolomorphic
import ComputableAnalysis.RiemannHilbert.LocalGermAgreement

/-! Actual finite-rank holomorphic solution charts centered at arbitrary
represented complex points. The chart stores coefficient data and proved
majorants; all solution, derivative and inverse maps are constructed. -/
namespace ComputableAnalysis.RiemannHilbert

structure SystemChart (n : Nat) where
  center : Scalar
  coefficients : Nat → ValueMap (Fiber n) (Fiber n)
  linear : ∀ k, IsLinear (coefficients k)
  M : Rat
  K : Rat
  nonnegM : 0 ≤ M
  nonnegK : 0 ≤ K
  compatible : 2*M ≤ K
  majorant : LocalSystem.OperatorMajorant coefficients M K

namespace SystemChart
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

def radius (c : SystemChart n) : QPos := solutionRadius c.K c.nonnegK
def domain (c : SystemChart n) (z : Scalar) : Prop := Centered.domain c.center c.radius.val z

theorem domain_congr (c : SystemChart n) (z w : Scalar) (hzw : z.val.Equiv w.val) :
    c.domain z ↔ c.domain w :=
  Centered.domain_congr c.center c.center z w c.radius.val (equiv_refl _ c.center.property) hzw

theorem center_mem (c : SystemChart n) : c.domain c.center := Centered.center_mem c.center c.radius

def value (c : SystemChart n) (initial : Fiber n) (z : Scalar) (hz : c.domain z) : Fiber n :=
  localValue c.coefficients initial c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant (Centered.offset c.center z) hz

def derivative (c : SystemChart n) (initial : Fiber n) (z : Scalar) (hz : c.domain z) : Fiber n :=
  localDerivative c.coefficients initial c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant (Centered.offset c.center z) hz

def operator (c : SystemChart n) (z : Scalar) (hz : c.domain z) : ValueMap (Fiber n) (Fiber n) :=
  coefficientValueMap c.coefficients c.M c.K c.nonnegM c.nonnegK c.majorant (Centered.offset c.center z) hz

def coordinate (c : SystemChart n) (initial : Fiber n) (i : Fin n) : CertifiedFunctions.Map :=
  CertifiedFunctions.translateInput c.center
    (coordinateMap c.coefficients initial c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant i)

def coordinate_holomorphic (c : SystemChart n) (initial : Fiber n) (i : Fin n) :
    CertifiedFunctions.Holomorphic (c.coordinate initial i) :=
  CertifiedFunctions.translateDerivative c.center
    (coordinateMap_holomorphic c.coefficients initial c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant i)

theorem coordinate_value (c : SystemChart n) (initial : Fiber n) (i : Fin n)
    (z : Scalar) (hz : c.domain z) : (c.coordinate initial i).eval z = (c.value initial z hz).val i := rfl

theorem value_congr (c d : SystemChart n) (initial seed : Fiber n)
    (hc : c.center.val.Equiv d.center.val) (ha : ∀ k, (c.coefficients k).Equiv (d.coefficients k))
    (hv : initial ≈ seed) (z w : Scalar) (hzw : z.val.Equiv w.val) (hz : c.domain z) (hw : d.domain w) :
    c.value initial z hz ≈ d.value seed w hw :=
  localValue_congr c.coefficients d.coefficients initial seed ha hv
    c.M c.K d.M d.K c.nonnegM c.nonnegK d.nonnegM d.nonnegK c.compatible d.compatible c.majorant d.majorant
    (Centered.offset c.center z) (Centered.offset d.center w) (Centered.offset_congr _ _ _ _ hc hzw) hz hw

theorem value_initial (c : SystemChart n) (initial : Fiber n) :
    c.value initial c.center c.center_mem ≈ initial := by
  let z : Scalar := ⟨zero, ofQComplex_valid _⟩
  have hz := interior_zero c.radius.val c.radius.property
  exact Setoid.trans
    (localValue_congr c.coefficients c.coefficients initial initial (fun _ => ValueMap.equiv_refl _) (Setoid.refl _)
      c.M c.K c.M c.K c.nonnegM c.nonnegK c.nonnegM c.nonnegK c.compatible c.compatible c.majorant c.majorant
      (Centered.offset c.center c.center) z (Centered.offset_self c.center) c.center_mem hz)
    (localValue_initial c.coefficients initial c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant)

theorem value_bound (c : SystemChart n) (initial : Fiber n) (z : Scalar) (hz : c.domain z) :
    CoordinateBound (c.value initial z hz) (4*initialBound initial) :=
  localValue_bound c.coefficients initial c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant (Centered.offset c.center z) hz

theorem value_ode (c : SystemChart n) (initial : Fiber n) (z : Scalar) (hz : c.domain z) :
    c.derivative initial z hz ≈ (c.operator z hz).eval (c.value initial z hz) :=
  localValue_ode c.coefficients c.linear initial c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant (Centered.offset c.center z) hz

theorem operator_linear (c : SystemChart n) (z : Scalar) (hz : c.domain z) : IsLinear (c.operator z hz) :=
  coefficientValueMap_linear c.coefficients c.linear c.M c.K c.nonnegM c.nonnegK c.majorant (Centered.offset c.center z) hz

theorem operator_bound (c : SystemChart n) (z : Scalar) (hz : c.domain z)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((c.operator z hz).eval x) ((8*c.M)*B) :=
  operatorValue_bound c.coefficients (Centered.offset c.center z) c.M c.K c.radius.val B
    c.nonnegM c.nonnegK (Rat.le_of_lt c.radius.property) hB c.majorant
    (interior_bound _ (Centered.offset c.center z) hz) (by
      have hs : 8*c.K*c.radius.val ≤ (1 : Rat)/2 := solutionRadius_small c.K c.nonnegK
      have := Rat.mul_nonneg c.nonnegK (Rat.le_of_lt c.radius.property)
      grind) x hx

def valueIso (c : SystemChart n) (z : Scalar) (hz : c.domain z) : LinearIso n n :=
  localValueIso c.coefficients c.linear c.M c.K c.nonnegM c.nonnegK c.compatible c.majorant (Centered.offset c.center z) hz

def remainder (c : SystemChart n) (f : (z : Scalar) → c.domain z → Fiber n)
    (w z : Scalar) (hw : c.domain w) (hz : c.domain z) : Fiber n :=
  Fiber.sub (Fiber.sub (f z hz) (f w hw))
    (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ ((c.operator w hw).eval (f w hw)))

def delta (c : SystemChart n) (initial : Fiber n) : QPos → QPos :=
  derivativeDelta (initialBound initial) c.K (initialBound_nonneg initial) c.nonnegK

theorem value_uniform_remainder (c : SystemChart n) (initial : Fiber n)
    (eps H : QPos) (w z : Scalar) (hw : c.domain w) (hz : c.domain z)
    (hH : H.val ≤ (c.delta initial eps).val) (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (c.remainder (c.value initial) w z hw hz) (eps.val*H.val) := by
  have hs := localValue_uniform_remainder c.coefficients c.linear initial c.M c.K
    c.nonnegM c.nonnegK c.compatible c.majorant eps H (Centered.offset c.center w) (Centered.offset c.center z) hw hz hH
    (Small.congr (sub_valid z.property w.property)
      (sub_valid (Centered.offset c.center z).property (Centered.offset c.center w).property)
      (equiv_symm (Centered.offset_difference c.center w z)) hzw)
  let x : Scalar := ⟨sub (Centered.offset c.center z).val (Centered.offset c.center w).val,
    sub_valid (Centered.offset c.center z).property (Centered.offset c.center w).property⟩
  let y : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
  exact bound_congr (Fiber.sub_congr (Setoid.refl _)
    (Fiber.scale_congr (a := x) (b := y) (Centered.offset_difference c.center w z) (Setoid.refl _))) hs

end SystemChart
end ComputableAnalysis.RiemannHilbert
