import ComputableAnalysis.ModularForms.CMJExactValue4
import ComputableAnalysis.ModularForms.CMJExactValue163

/-! A general represented modular-orbit law, with exact integer CM
specializations of discriminants minus four and minus 163. This is not the
general class-polynomial theorem or its algebraic-degree assertion. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

/-- Domain evidence at every equivalent represented name of a modular orbit point. -/
theorem latticeJMap_modular_orbit_equivalent_domain (g : SL2Z) (a : Scalar)
    (ha : InUpperHalfPlane a.val) (z : Scalar)
    (hz : z.val.Equiv (fractionalLinear g a ha).val) : latticeJMap.domain z :=
  (latticeJMap.domain_congr z _ hz).mpr
    (latticeJMap_global_domain _ (fractionalLinear_mem g a ha))

/-- The actual j value is constant on a modular orbit, for arbitrary
represented base points and arbitrary equivalent valid orbit names. -/
theorem latticeJMap_modular_orbit_equivalent_value (g : SL2Z) (a : Scalar)
    (ha : InUpperHalfPlane a.val) (z : Scalar)
    (hz : z.val.Equiv (fractionalLinear g a ha).val) :
    (latticeJMap.eval z (latticeJMap_modular_orbit_equivalent_domain g a ha z hz)).val.Equiv
      (latticeJMap.eval a (latticeJMap_global_domain a ha)).val := by
  let w := fractionalLinear g a ha
  let hw := latticeJMap_global_domain w (fractionalLinear_mem g a ha)
  exact equiv_trans (latticeJMap.eval z
      (latticeJMap_modular_orbit_equivalent_domain g a ha z hz)).property
    (latticeJMap.eval w hw).property
    (latticeJMap.eval a (latticeJMap_global_domain a ha)).property
    (latticeJMap.eval_congr z w _ hw hz)
    (latticeJMap_action g a (latticeJMap_global_domain a ha) hw)

/-- The existing integer identity extends to the entire modular orbit of
the CM point of discriminant minus 163, without caller-supplied domain data. -/
theorem latticeJMap_cm163_orbit_equivalent_value (g : SL2Z) (z : Scalar)
    (hz : z.val.Equiv (fractionalLinear g cmScalar163 cmPoint163_upper).val) :
    (latticeJMap.eval z
      (latticeJMap_modular_orbit_equivalent_domain g cmScalar163 cmPoint163_upper z hz)).val.Equiv
      (ofQComplex ⟨-((640320:Rat)^3),0⟩) := by
  have ho := latticeJMap_modular_orbit_equivalent_value g cmScalar163 cmPoint163_upper z hz
  exact equiv_trans (latticeJMap.eval z _).property cmJValue163.property
    (ofQComplex_valid _) ho cmJValue163_exact_value

/-- The second exact CM value is a specialization of the same general orbit law. -/
theorem latticeJMap_cm4_orbit_equivalent_value (g : SL2Z) (z : Scalar)
    (hz : z.val.Equiv (fractionalLinear g squareCMPoint squareCMPoint_upper).val) :
    (latticeJMap.eval z
      (latticeJMap_modular_orbit_equivalent_domain g squareCMPoint squareCMPoint_upper z hz)).val.Equiv
      (ofQComplex ⟨1728,0⟩) :=
  equiv_trans (latticeJMap.eval z _).property cmJValue4.property (ofQComplex_valid _)
    (latticeJMap_modular_orbit_equivalent_value g squareCMPoint squareCMPoint_upper z hz)
    cmJValue4_exact_value

end ComputableAnalysis.ModularForms
