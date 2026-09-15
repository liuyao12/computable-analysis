import MathlibComparison.CosineIntegralBridge
import MathlibComparison.MathlibRoute
import ComputableAnalysis.CosinePrimitiveEndpoints

/-!
# Third proof of the identical native basepoint proposition

The closed native algorithms are unchanged. The quadrature correspondence
uses no native endpoint theorem; the Mathlib primitive is transported through
the independently proved value bridges.
-/
namespace MathlibComparison
open ComputableAnalysis CosinePrimitive GeometricSineDerivative

lemma primitive_endpoint_represents (t : Rat) (ht : Domain t) :
    Represents (endpoint t) (∫ x in (0:ℝ)..(t:ℝ), normalizedCosine x) := by
  have hs : Represents (S t) (Real.sin (Real.pi*(t:ℝ))) := by
    simpa only [S,CosineFTC.sine,dif_pos ht] using
      sine_represents ClosedArctanInverse.provider t ht
  have hp : Represents inversePi Real.pi⁻¹ := by
    rw [inversePi_eq]
    exact reciprocalPi_represents
  have h := represents_mul inversePi_valid (S_valid t) hp hs
  change Represents (endpoint t) (Real.pi⁻¹*Real.sin (Real.pi*(t:ℝ))) at h
  simpa only [normalizedCosine,mathlib_cosine_primitive,div_eq_inv_mul] using h

lemma primitive_integral_represents (t : Rat) (ht : Domain t) :
    Represents (integral t ht) (∫ x in (0:ℝ)..(t:ℝ), normalizedCosine x) := by
  simpa only [integral,Rat.cast_zero] using cosine_integral_represents
    ClosedArctanInverse.provider 0 t (by constructor <;> decide +kernel) ht ht.1

end MathlibComparison

namespace ComputableAnalysis.CosinePrimitive
open MathlibComparison ClosedArctanInverse

/-- Validity justified by the Mathlib route, not a native integral identity. -/
theorem integral_valid_viaMathlib (t : Rat) (ht : Domain t) :
    (integral t ht).Valid := by
  have he := primitive_endpoint_represents t ht
  apply Integral.Dovetail.raw_valid
    (CosineFTC.fixedMesh_valid provider 0 t) (endpoint_valid t)
    (CosineFTC.error_shrinks (by constructor <;> decide +kernel) ht ht.1)
  intro k q j
  have hi := fixedMesh_contains_integral provider
    (a := 0) (b := t) (by constructor <;> decide +kernel) ht ht.1 k q
  norm_num only [Rat.cast_zero] at hi
  constructor
  · exact_mod_cast le_trans hi.1 (he j).2
  · exact_mod_cast le_trans (he j).1 hi.2

/-- The third inhabitant of the same native theorem type. -/
theorem viaMathlib (t : Rat) (ht : Domain t) : Statement t ht :=
  equiv_of_represents (primitive_integral_represents t ht) (primitive_endpoint_represents t ht)

end ComputableAnalysis.CosinePrimitive
