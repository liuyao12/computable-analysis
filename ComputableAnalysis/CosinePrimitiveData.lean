import ComputableAnalysis.ClosedArctanInverse
import ComputableAnalysis.CosineIntegralData

/-!
# One basepoint statement, independently of its proofs

A is the geometric arctangent, with a separate checked rectangle-integral
presentation. Pi is literally four times A(1). The closed inverse provider
normalizes by the arctangent endpoint, then applies rational circle formulas.
All functions below are used on the rational chart [0,1/2].
-/
namespace ComputableAnalysis.CosinePrimitive
open SinPiIntegral GeometricSineDerivative ClosedArctanInverse IntervalSelections

abbrev Domain (t : Rat) : Prop := OnHalf t

def A (u : Rat) : RealRaw := ArctanGeometry.arctanGeom u

def pi : RealRaw := (4 : Nat) * A 1

theorem pi_compute (n : Nat) : pi.compute n = piCircleArea.compute n :=
  ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n

theorem pi_valid : pi.Valid := ArctanGeometry.four_arctanGeom_one_valid

/-- Literal reciprocal of the arctangent presentation of pi. -/
def inversePi : RealRaw where
  compute := fun n => QInterval.inv (pi.compute n)

theorem inversePi_compute (n : Nat) : inversePi.compute n = reciprocalPiRaw.compute n := by
  change QInterval.inv (pi.compute n) = QInterval.inv (piCircleArea.compute n)
  rw [pi_compute]

theorem inversePi_eq : inversePi = reciprocalPiRaw := by
  have hc : inversePi.compute = reciprocalPiRaw.compute := funext inversePi_compute
  exact congrArg (fun f => RealRaw.mk f .unknown) hc

/-- The same closed geometric sine and cosine used by the finite sums. -/
def S (x : Rat) : RealRaw := CosineFTC.sine provider x
def C (x : Rat) : RealRaw := CosineFTC.cosine provider x

theorem S_valid (x : Rat) : (S x).Valid := CosineFTC.sine_valid provider x
theorem C_valid (x : Rat) : (C x).Valid := CosineFTC.cosine_valid provider x

/-- Independently executable left-Riemann computation. -/
def integral (t : Rat) (ht : Domain t) : RealRaw :=
  CosineFTC.integral provider 0 t (by constructor <;> decide +kernel) ht ht.1

def endpoint (t : Rat) : RealRaw := RealRaw.mul inversePi (S t)

def Statement (t : Rat) (ht : Domain t) : Prop :=
  (integral t ht).Equiv (endpoint t)

end ComputableAnalysis.CosinePrimitive
