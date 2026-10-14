import ComputableAnalysis.RiemannHilbert.NeumannOperatorAgreement
import ComputableAnalysis.RiemannHilbert.OperatorSeries
import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

/-! An executable scalar inverse near one, obtained from the proved
finite-dimensional Neumann construction. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarNeumannInverse
open ComplexRaw FunctionTheory LocalSystem

def unit : Fiber 1 := ⟨fun _ => ofQComplex QComplex.one, fun _ => ofQComplex_valid _⟩

theorem unit_bound : CoordinateBound unit 1 :=
  fun _ => ⟨fun _ _ => by change (-1 : Rat) ≤ 1; decide +kernel,
    fun _ _ => by change (1 : Rat) ≤ 1; decide +kernel,
    fun _ _ => by change (-1 : Rat) ≤ 0; decide +kernel,
    fun _ _ => by change (0 : Rat) ≤ 1; decide +kernel⟩

theorem deviation (s : Scalar) (x : Fiber n) :
    (ValueMap.difference ValueMap.identity (Fiber.scaleMap s)).eval x ≈
      Fiber.scale ⟨sub (ofQComplex QComplex.one) s.val,
        sub_valid (ofQComplex_valid _) s.property⟩ x := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((ValueMap.difference ValueMap.identity (Fiber.scaleMap s)).eval x).property i)
    (hright := (Fiber.scale ⟨sub (ofQComplex QComplex.one) s.val,
      sub_valid (ofQComplex_valid _) s.property⟩ x).property i)
  let S := ComplexRawQuotient.ofRaw s.val s.property
  let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
  change X + -(S*X) = ((1 : ScalarAlgebra.Value) + -S)*X
  grind

theorem deviation_bound (s : Scalar)
    (hs : Small (sub (ofQComplex QComplex.one) s.val) ((1 : Rat)/8))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((ValueMap.difference ValueMap.identity (Fiber.scaleMap s)).eval x) ((1 : Rat)/4*B) := by
  have hb := bound_scale (c := ⟨sub (ofQComplex QComplex.one) s.val,
      sub_valid (ofQComplex_valid _) s.property⟩) (x := x) (B := (1 : Rat)/8) (C := B)
    (by decide +kernel) hB hs hx
  have he : (2 : Rat)*(1/8) = 1/4 := by decide +kernel
  rw [he] at hb
  exact bound_congr (Setoid.symm (deviation s x)) hb

def errorScalar (s : Scalar) : Scalar :=
  ⟨sub (ofQComplex QComplex.one) s.val, sub_valid (ofQComplex_valid _) s.property⟩

theorem error_bound (s : Scalar)
    (hs : Small (sub (ofQComplex QComplex.one) s.val) ((1 : Rat)/8))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((Fiber.scaleMap (errorScalar s)).eval x) ((1 : Rat)/4*B) := by
  have hb := bound_scale (c := errorScalar s) (x := x) (B := (1 : Rat)/8) (C := B)
    (by decide +kernel) hB hs hx
  have he : (2 : Rat)*(1/8) = 1/4 := by decide +kernel
  rw [he] at hb
  exact hb

def vector (s : Scalar)
    (hs : Small (sub (ofQComplex QComplex.one) s.val) ((1 : Rat)/8)) : Fiber 1 :=
  (Neumann.valueMap (Fiber.scaleMap (errorScalar s)) (1/4) (by decide +kernel) (by decide +kernel)
    (error_bound s hs)).eval unit

theorem vector_agreement (s : Scalar)
    (hs : Small (sub (ofQComplex QComplex.one) s.val) ((1 : Rat)/8)) :
    vector s hs ≈ (Neumann.inverse (Fiber.scaleMap s) (1/4)
      (by decide +kernel) (by decide +kernel) (deviation_bound s hs)).eval unit :=
  Neumann.valueMap_congr (Fiber.scaleMap (errorScalar s))
    (ValueMap.difference ValueMap.identity (Fiber.scaleMap s)) (fun x => Setoid.symm (deviation s x))
    (1/4) (1/4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (error_bound s hs) (deviation_bound s hs) unit

def value (s : Scalar)
    (hs : Small (sub (ofQComplex QComplex.one) s.val) ((1 : Rat)/8)) : Scalar :=
  ⟨(vector s hs).val 0, (vector s hs).property 0⟩

theorem mul_value (s : Scalar)
    (hs : Small (sub (ofQComplex QComplex.one) s.val) ((1 : Rat)/8)) :
    (mul s.val (value s hs).val).Equiv (ofQComplex QComplex.one) := by
  have h1 := (Fiber.scaleMap s).congr (vector_agreement s hs)
  have h2 := Neumann.forward_inverse (Fiber.scaleMap s) (Fiber.scaleMap_linear s) (1/4)
    (by decide +kernel) (by decide +kernel) (deviation_bound s hs) unit
  exact Setoid.trans h1 h2 0

theorem value_bound (s : Scalar)
    (hs : Small (sub (ofQComplex QComplex.one) s.val) ((1 : Rat)/8)) :
    Small (value s hs).val 4 := by
  have h := Neumann.valueMap_bound
    (Fiber.scaleMap (errorScalar s)) (1/4)
    (by decide +kernel) (by decide +kernel) (error_bound s hs)
    1 (by decide +kernel) unit unit_bound 0
  simpa only [Rat.mul_one, value, vector] using h

end ComputableAnalysis.RiemannHilbert.ScalarNeumannInverse
