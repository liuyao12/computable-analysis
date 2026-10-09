import ComputableAnalysis.ModularForms.EllipticFixedValues
import ComputableAnalysis.ModularForms.ActionLaws

/-! The exact singular modulus of discriminant minus four, and its full
modular orbit. The point is the literal computable rational complex number i. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def squareCMPoint : Scalar := ⟨ofQComplex ⟨0,1⟩,ofQComplex_valid _⟩

theorem squareCMPoint_upper : InUpperHalfPlane squareCMPoint.val :=
  ⟨0,by decide +kernel⟩

theorem squareCMPoint_fixed :
    (fractionalLinear SL2Z.S squareCMPoint squareCMPoint_upper).val.Equiv
      squareCMPoint.val := by
  apply fractionalLinear_unique SL2Z.S squareCMPoint squareCMPoint_upper squareCMPoint
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  dsimp [SL2Z.S,squareCMPoint,integerAffine,translate,scaleRat,add,mul,ofQComplex]
  decide +kernel

theorem squareCMPoint_weightSix_nonidentity :
    ¬(LocalODE.power (integerAffine SL2Z.S.c SL2Z.S.d squareCMPoint.val) 6).Equiv
      (ofQComplex QComplex.one) := by
  intro h
  have he := (compareAt_overlap_iff _ _ 0 0).mp (h 0)
  have hn : ¬((LocalODE.power (integerAffine SL2Z.S.c SL2Z.S.d squareCMPoint.val) 6).compute 0).Overlaps
      ((ofQComplex QComplex.one).compute 0) := by decide +kernel
  exact hn he

/-- The actual lattice j value at i, with its domain constructed internally. -/
def cmJValue4 : Scalar :=
  latticeJMap.eval squareCMPoint (latticeJMap_global_domain squareCMPoint squareCMPoint_upper)

theorem cmJValue4_exact_value : cmJValue4.val.Equiv (ofQComplex ⟨1728,0⟩) :=
  latticeJMap_1728_of_modular_fixed SL2Z.S squareCMPoint squareCMPoint_upper
    squareCMPoint_fixed squareCMPoint_weightSix_nonidentity

/-- Every equivalent valid name of i has its justified j domain. -/
theorem latticeJMap_squareCM_equivalent_domain (z : Scalar)
    (hz : z.val.Equiv squareCMPoint.val) : latticeJMap.domain z :=
  (latticeJMap.domain_congr z squareCMPoint hz).mpr
    (latticeJMap_global_domain squareCMPoint squareCMPoint_upper)

theorem latticeJMap_squareCM_equivalent_value (z : Scalar)
    (hz : z.val.Equiv squareCMPoint.val) :
    (latticeJMap.eval z (latticeJMap_squareCM_equivalent_domain z hz)).val.Equiv
      (ofQComplex ⟨1728,0⟩) :=
  equiv_trans (latticeJMap.eval z (latticeJMap_squareCM_equivalent_domain z hz)).property
    cmJValue4.property (ofQComplex_valid _)
    (latticeJMap.eval_congr z squareCMPoint _ _ hz) cmJValue4_exact_value

/-- The whole modular orbit of i has the same exact integer j value. -/
theorem latticeJMap_squareCM_orbit_value (g : SL2Z) :
    (latticeJMap.eval (fractionalLinear g squareCMPoint squareCMPoint_upper)
      (latticeJMap_global_domain _ (fractionalLinear_mem g squareCMPoint squareCMPoint_upper))).val.Equiv
      (ofQComplex ⟨1728,0⟩) :=
  equiv_trans (latticeJMap.eval _ _).property cmJValue4.property (ofQComplex_valid _)
    (latticeJMap_action g squareCMPoint
      (latticeJMap_global_domain squareCMPoint squareCMPoint_upper) _) cmJValue4_exact_value

theorem latticeJMap_squareCM_orbit_equivalent_domain (g : SL2Z) (z : Scalar)
    (hz : z.val.Equiv (fractionalLinear g squareCMPoint squareCMPoint_upper).val) :
    latticeJMap.domain z :=
  (latticeJMap.domain_congr z _ hz).mpr
    (latticeJMap_global_domain _ (fractionalLinear_mem g squareCMPoint squareCMPoint_upper))

/-- The orbit theorem is invariant under every valid representation of its point. -/
theorem latticeJMap_squareCM_orbit_equivalent_value (g : SL2Z) (z : Scalar)
    (hz : z.val.Equiv (fractionalLinear g squareCMPoint squareCMPoint_upper).val) :
    (latticeJMap.eval z (latticeJMap_squareCM_orbit_equivalent_domain g z hz)).val.Equiv
      (ofQComplex ⟨1728,0⟩) :=
  equiv_trans (latticeJMap.eval z _).property (latticeJMap.eval _ _).property (ofQComplex_valid _)
    (latticeJMap.eval_congr z _ _ _ hz) (latticeJMap_squareCM_orbit_value g)

end ComputableAnalysis.ModularForms
