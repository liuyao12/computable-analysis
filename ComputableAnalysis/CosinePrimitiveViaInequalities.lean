import ComputableAnalysis.CosinePrimitiveEndpoints
import ComputableAnalysis.CosineFTC

namespace ComputableAnalysis.CosinePrimitive
open ClosedArctanInverse

theorem integral_valid_viaInequalities (t : Rat) (ht : Domain t) :
    (integral t ht).Valid :=
  Integral.Dovetail.raw_valid (CosineFTC.fixedMesh_valid provider 0 t)
    (CosineFTC.endpoint_valid provider 0 t)
    (CosineFTC.error_shrinks (by constructor <;> decide +kernel) ht ht.1)
    (CosineFTC.fixedMesh_overlaps_endpoint provider (by constructor <;> decide +kernel) ht ht.1)

/-- Direct finite inequalities prove the basepoint identity itself. -/
theorem viaInequalities (t : Rat) (ht : Domain t) : Statement t ht := by
  have h : (integral t ht).Equiv (CosineFTC.endpoint provider 0 t) :=
    Integral.Dovetail.raw_equiv_endpoint
      (CosineFTC.fixedMesh_overlaps_endpoint provider
        (by constructor <;> decide +kernel) ht ht.1)
  exact RealRaw.equiv_trans (integral_valid_viaInequalities t ht)
    (CosineFTC.endpoint_valid provider 0 t) (endpoint_valid t) h (endpoints_from_zero t)

end ComputableAnalysis.CosinePrimitive
