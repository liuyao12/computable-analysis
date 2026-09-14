import ComputableAnalysis.CosineFTC

open ComputableAnalysis
open ComputableAnalysis.IntegralIdentities
open ComputableAnalysis.SinPiIntegral
open ComputableAnalysis.GeometricSineDerivative

-- The requested theorem uses the original geometric sine and cosine data.
example (B : ArctanInverseBisection) :
    (CosineFTC.integral B 0 (1/2)
      ⟨by decide +kernel, by decide +kernel⟩
      ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)).Equiv
      (RealRaw.mul reciprocalPiRaw
        (sinPiRawOfArctan B (1/2) ⟨by decide +kernel, by decide +kernel⟩ -
          sinPiRawOfArctan B 0 ⟨by decide +kernel, by decide +kernel⟩)) :=
  CosineFTC.integral_cosPi_equiv_sinPi_endpoints B _ _ _ _ _

-- Equal endpoints are covered without a nonzero-length hypothesis.
example (B : ArctanInverseBisection) (a : Rat) (ha : OnHalf a) :
    (CosineFTC.integral B a a ha ha (Rat.le_refl)).Valid :=
  CosineFTC.integral_valid B a a ha ha (Rat.le_refl)

-- A delayed-evaluation regression. The fresh diagonal alone stays coarse,
-- while retaining old meshes makes genuine progress with a fixed schedule.
private def slowMesh (k : Nat) : RealRaw where
  compute := fun n =>
    if (k+1)*(k+1) <= n then {lo := 1/2, hi := 1/2}
    else {lo := 0, hi := 1}

private def slowRadius (k : Nat) : Rat := 1 / ((k+1 : Nat) : Rat)

example : (slowMesh 16).compute 16 = ({lo := 0, hi := 1} : QInterval) := by
  decide +kernel

example : (Integral.Dovetail.raw slowMesh slowRadius).compute 16 =
    ({lo := 1/4, hi := 3/4} : QInterval) := by
  decide +kernel

#print axioms ComputableAnalysis.Integral.Dovetail.raw_valid
#print axioms ComputableAnalysis.CosineFTC.fixedMesh_compute_eq_riemannLeftInterval
#print axioms ComputableAnalysis.CosineFTC.fixedMesh_overlaps_endpoint
#print axioms ComputableAnalysis.CosineFTC.integral_valid
#print axioms ComputableAnalysis.CosineFTC.integral_cosPi_equiv_sinPi_endpoints
#print axioms ComputableAnalysis.CosineFTC.integral_compute
