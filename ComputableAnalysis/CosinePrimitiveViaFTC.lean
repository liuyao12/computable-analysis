import ComputableAnalysis.CosinePrimitiveEndpoints
import ComputableAnalysis.CosineIntegralViaFTC

namespace ComputableAnalysis.CosinePrimitive
open ClosedArctanInverse GeometricSineConcavity

private theorem budget (t : Rat) (ht : Domain t) (k : Nat) :
    ((k+1 : Nat) : Rat)*((primitiveDerivativeData provider).K : Rat)*
      mesh 0 t (k+1)*mesh 0 t (k+1) <= CosineFTC.error 0 t k := by
  rw [CosineFTC.error_eq_mesh]
  change ((k+1 : Nat) : Rat)*32*mesh 0 t (k+1)*mesh 0 t (k+1) <=
    ((k+1 : Nat) : Rat)*(4000*mesh 0 t (k+1)*mesh 0 t (k+1))
  have hh := mesh_nonneg_of_le (Nat.succ_pos k) ht.1
  have hm : 0 <= ((k+1 : Nat) : Rat) := Rat.le_of_lt ((Rat.natCast_pos).2 (Nat.succ_pos k))
  have h := Rat.mul_le_mul_of_nonneg_right (by decide : (32 : Rat) <= 4000)
    (Rat.mul_nonneg (Rat.mul_nonneg hm hh) hh)
  grind

theorem integral_valid_viaFTC (t : Rat) (ht : Domain t) :
    (integral t ht).Valid :=
  ConcaveFTC.integral_valid (primitiveDerivativeData provider)
    (by constructor <;> decide +kernel) ht ht.1 (CosineFTC.error 0 t)
    (CosineFTC.error_shrinks (by constructor <;> decide +kernel) ht ht.1) (budget t ht)

/-- The concavity-based FTC proves the identical basepoint statement. -/
theorem viaFTC (t : Rat) (ht : Domain t) : Statement t ht := by
  have h : (integral t ht).Equiv
      (ConcaveFTC.endpointDifference (CosineFTC.primitiveFun provider) 0 t) :=
    ConcaveFTC.integral_equiv_endpoint (primitiveDerivativeData provider)
      (by constructor <;> decide +kernel) ht ht.1 (CosineFTC.error 0 t) (budget t ht)
  have h2 := RealRaw.equiv_trans
    (ConcaveFTC.endpointDifference_valid (primitiveDerivativeData provider)
      (by constructor <;> decide +kernel) ht)
    (CosineFTC.endpoint_valid provider 0 t) (endpoint_valid t)
    (CosineFTC.primitive_difference_equiv_endpoint provider 0 t) (endpoints_from_zero t)
  exact RealRaw.equiv_trans (integral_valid_viaFTC t ht)
    (ConcaveFTC.endpointDifference_valid (primitiveDerivativeData provider)
      (by constructor <;> decide +kernel) ht) (endpoint_valid t) h h2

end ComputableAnalysis.CosinePrimitive
