import ComputableAnalysis.ModularForms.NearIntegerExponentials

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

-- A non-elliptic CM point: repeated Hecke value, polynomial root, analytic
-- isolation and exact value, all with constructed evidence.
#check cmJValue43_exact_value
#print axioms cmPoint43Value_quadratic
#print axioms cmHeckePointFive43_action_agreement
#print axioms hecke41Point_cm43_five_j
#print axioms hecke41_repeated_j_diagonal_root
#print axioms cmJValue43_candidate_diagonal_root
#print axioms cmJValue43_real_isolation_bounds
#print axioms cmJValue43_quotient_nonzero
#print axioms cmJValue43_exact_value
#print axioms latticeJMap_cm43_equivalent_value
#print axioms latticeJMap_cm43_orbit_equivalent_value
#print axioms EC43.complex_exp_agreement
#print axioms EC43.real_exp_agreement
#print axioms EC43.implementation_agreement

example (z : Scalar) (hz : z.val.Equiv cmPoint43) :
    (latticeJMap.eval z (latticeJMap_cm43_equivalent_domain z hz)).val.Equiv
      (ComplexRaw.ofQComplex ⟨-((960:Rat)^3),0⟩) :=
  latticeJMap_cm43_equivalent_value z hz

example (g : SL2Z) (z : Scalar)
    (hz : z.val.Equiv (fractionalLinear g cmScalar43 cmPoint43_upper).val) :
    (latticeJMap.eval z (latticeJMap_modular_orbit_equivalent_domain
      g cmScalar43 cmPoint43_upper z hz)).val.Equiv
      (ComplexRaw.ofQComplex ⟨-((960:Rat)^3),0⟩) :=
  latticeJMap_cm43_orbit_equivalent_value g z hz

#print axioms cmJValue43_linear_laurent_bound
#print axioms cmJGrowthError43_small_sharp
#print axioms cmJGrowthError43_real_upper_negative
#print axioms cmJGrowthDeficit43_lower
#print axioms cmJGrowthDeficit43_upper
#print axioms EC43.deficit_agreement
#print axioms EC43.deficit_bounds
#print axioms EC43.exp_bounds
#print axioms EC43.compoundInterest_bounds
#print axioms EC43.linearODE_bounds
#print axioms exp_pi_sqrt43_near_integer
#print axioms exp_pi_sqrt163_near_integer
#print axioms exp_pi_sqrt43_near_integer_for
#print axioms exp_pi_sqrt163_near_integer_for
