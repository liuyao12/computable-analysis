import ComputableAnalysis.CosinePrimitiveData

/-!
# Literal definitions behind the trigonometry blueprint

These are readback equations for the existing programs, not new sine/cosine
implementations or integral proofs. `CosinePrimitive` is a namespace; its
`pi` is defined from arctangent before any endpoint theorem is imported.
-/
namespace ComputableAnalysis.TrigonometricReadback
open CosinePrimitive SinPiIntegral

/-- The pi appearing in the common theorem is independently defined by A(1). -/
theorem pi_definition : CosinePrimitive.pi = (4 : Nat) * ArctanGeometry.arctanGeom 1 := rfl

/-- On the certified chart, the sine box is the increasing circle coordinate
of the literal CLOSED inverse box at normalized parameter 2*x. -/
theorem sine_stage (x : Rat) (hx : Domain x) (n : Nat) :
    (S x).compute n =
      { lo := rationalCircleSin ((ClosedArctanInverse.raw (2*x)).compute n).lo
        hi := rationalCircleSin ((ClosedArctanInverse.raw (2*x)).compute n).hi } := by
  simp only [S, CosineFTC.sine, dif_pos hx]
  rfl

/-- Cosine is decreasing in the same slope, so its box endpoints are reversed. -/
theorem cosine_stage (x : Rat) (hx : Domain x) (n : Nat) :
    (C x).compute n =
      { lo := rationalCircleCos ((ClosedArctanInverse.raw (2*x)).compute n).hi
        hi := rationalCircleCos ((ClosedArctanInverse.raw (2*x)).compute n).lo } := by
  simp only [C, CosineFTC.cosine, dif_pos hx]
  rfl

/-- Totalization outside this chart is zero, NOT a global trigonometric extension. -/
theorem sine_outside_chart (x : Rat) (hx : ¬ Domain x) : S x = RealRaw.zero := by
  simp only [S, CosineFTC.sine, dif_neg hx]

theorem cosine_outside_chart (x : Rat) (hx : ¬ Domain x) : C x = RealRaw.zero := by
  simp only [C, CosineFTC.cosine, dif_neg hx]

/-- The integral reads fixed-mesh sums, never the proposed endpoint value. -/
theorem integral_stage (t : Rat) (ht : Domain t) (n : Nat) :
    (integral t ht).compute n = Integral.Dovetail.intersectMeshes
      (fun k q => QInterval.expand
        ((CosineFTC.fixedMesh ClosedArctanInverse.provider 0 t k).compute q)
        (CosineFTC.error 0 t k)) n n := rfl

/-- The other side of the proposition is a separately defined product. -/
theorem endpoint_definition (t : Rat) :
    endpoint t = RealRaw.mul inversePi (S t) := rfl

/-- Concrete outputs demonstrate that the two programs are not definitionally
identical. The asserted theorem is representation equivalence, not box equality. -/
theorem pi_initial : CosinePrimitive.pi.compute 0 = ({lo := 2, hi := 4} : QInterval) := by
  decide +kernel

theorem integral_initial_half :
    (integral (1/2) ⟨by decide +kernel, by decide +kernel⟩).compute 0 =
      ({lo := -1000, hi := 2001/2} : QInterval) := by
  decide +kernel

theorem endpoint_initial_half : (endpoint (1/2)).compute 0 =
    ({lo := 0, hi := 1/2} : QInterval) := by
  decide +kernel

end ComputableAnalysis.TrigonometricReadback
