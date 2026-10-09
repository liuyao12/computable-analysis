import ComputableAnalysis.ModularForms.CMJModularOrbits

open ComputableAnalysis ComputableAnalysis.ModularForms
open ComputableAnalysis.RiemannHilbert

#check latticeJMap_zero_of_modular_fixed
#check latticeJMap_1728_of_modular_fixed
#check cmJValue4_exact_value
#check latticeJMap_squareCM_equivalent_value
#check latticeJMap_squareCM_orbit_equivalent_value

#print axioms modular_weight_fixed_value_zero
#print axioms upperWeightFour_zero_of_modular_fixed
#print axioms upperWeightSix_zero_of_modular_fixed
#print axioms latticeJMap_value_of_weightFour_zero
#print axioms latticeJMap_value_of_weightSix_zero
#print axioms latticeJMap_zero_of_modular_fixed
#print axioms latticeJMap_1728_of_modular_fixed
#print axioms squareCMPoint_fixed
#print axioms squareCMPoint_weightSix_nonidentity
#print axioms cmJValue4_exact_value
#print axioms latticeJMap_squareCM_equivalent_value
#print axioms latticeJMap_squareCM_orbit_value
#print axioms latticeJMap_squareCM_orbit_equivalent_value

-- The public endpoint supplies domain evidence for any valid represented
-- name of any modular transform of i, without numerical or chart choices.
example (g : SL2Z) (z : Scalar)
    (hz : z.val.Equiv (fractionalLinear g squareCMPoint squareCMPoint_upper).val) :
    (latticeJMap.eval z (latticeJMap_squareCM_orbit_equivalent_domain g z hz)).val.Equiv
      (ComplexRaw.ofQComplex ⟨1728,0⟩) :=
  latticeJMap_squareCM_orbit_equivalent_value g z hz

#print axioms latticeJMap_modular_orbit_equivalent_value
#print axioms latticeJMap_cm163_orbit_equivalent_value
#print axioms latticeJMap_cm4_orbit_equivalent_value

#eval squareCMPoint.val.compute 0
