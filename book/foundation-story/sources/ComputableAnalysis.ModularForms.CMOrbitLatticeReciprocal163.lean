import ComputableAnalysis.ModularForms.LatticeActionIdentity
import ComputableAnalysis.ModularForms.CMLatticeInverseFormula163

/-! Certified lattice reciprocals at every modular transform of the CM point. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163
set_option maxRecDepth 8192

def cmOrbitPoint163 (g : SL2Z) : Scalar :=
  fractionalLinear g ⟨cmPoint163,cmPoint163_valid⟩ cmPoint163_upper

def cmOrbitLattice163 (g : SL2Z) (u : QuadraticOrder163) : Scalar :=
  ⟨integerAffine u.y u.x (cmOrbitPoint163 g).val,
    integerAffine_valid _ _ (cmOrbitPoint163 g).property⟩

def cmOrbitDenominator163 (g : SL2Z) : Scalar :=
  ⟨integerAffine g.c g.d cmPoint163,integerAffine_valid _ _ cmPoint163_valid⟩

private theorem orbit_lattice_product (g : SL2Z) (u : QuadraticOrder163) :
    (ComplexRaw.mul (cmOrbitDenominator163 g).val (cmOrbitLattice163 g u).val).Equiv
      (basisIndex (latticeIndexMatrix g) u).complexRaw :=
  latticeVector_action g ⟨cmPoint163,cmPoint163_valid⟩ cmPoint163_upper u

theorem cmOrbitLattice163_nonzero (g : SL2Z) (u : QuadraticOrder163) (hu : u≠zero) :
    NonzeroBoxSearch.Nonzero (cmOrbitLattice163 g u) := by
  intro hz
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (cmOrbitLattice163 g u).property)
    (hright := ComplexRaw.ofQComplex_valid QComplex.zero) hz
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid (cmOrbitDenominator163 g).property
      (cmOrbitLattice163 g u).property)
    (hright := (basisIndex (latticeIndexMatrix g) u).complexRaw_valid)
    (orbit_lattice_product g u)
  rw [ComplexRawQuotient.ofRaw_mul _ _ (cmOrbitDenominator163 g).property
    (cmOrbitLattice163 g u).property,he] at hp
  have hzero : (basisIndex (latticeIndexMatrix g) u).complexValue=0 := by
    change _*0=(basisIndex (latticeIndexMatrix g) u).complexValue at hp
    grind
  exact basisIndex_nonzero _ u hu ((complexValue_eq_zero_iff _).mp hzero)

def cmOrbitLatticeInverse163 (g : SL2Z) (u : QuadraticOrder163) (hu : u≠zero) : Scalar :=
  RepresentedReciprocal.inverse (cmOrbitLattice163 g u) (cmOrbitLattice163_nonzero g u hu)

/-- The reciprocal at the transformed point gains one denominator factor. -/
theorem cmOrbitLatticeInverse163_transform (g : SL2Z) (u : QuadraticOrder163) (hu : u≠zero) :
    (cmOrbitLatticeInverse163 g u hu).val.Equiv
      (ComplexRaw.mul (cmOrbitDenominator163 g).val
        (complexInverse (basisIndex (latticeIndexMatrix g) u) (basisIndex_nonzero _ u hu)).val) := by
  let v := basisIndex (latticeIndexMatrix g) u
  let inv := complexInverse v (basisIndex_nonzero _ u hu)
  let r : Scalar := ⟨ComplexRaw.mul (cmOrbitDenominator163 g).val inv.val,
    ComplexRaw.mul_valid (cmOrbitDenominator163 g).property inv.property⟩
  apply RepresentedReciprocal.inverse_unique (cmOrbitLattice163 g u)
    (cmOrbitLattice163_nonzero g u hu) r
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid (cmOrbitDenominator163 g).property (cmOrbitLattice163 g u).property)
    (hright := v.complexRaw_valid) (orbit_lattice_product g u)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid v.complexRaw_valid inv.property)
    (hright := ComplexRaw.ofQComplex_valid QComplex.one) (complexInverse_product v _)
  rw [ComplexRawQuotient.ofRaw_mul _ _ (cmOrbitDenominator163 g).property
    (cmOrbitLattice163 g u).property] at hp
  rw [ComplexRawQuotient.ofRaw_mul _ _ v.complexRaw_valid inv.property] at hi
  change ComplexRawQuotient.ofRaw v.complexRaw v.complexRaw_valid *
    ComplexRawQuotient.ofRaw inv.val inv.property=(1:ScalarAlgebra.Value) at hi
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.mul_valid (cmOrbitLattice163 g u).property r.property)
    (hright := ComplexRaw.ofQComplex_valid QComplex.one)
  change ComplexRawQuotient.ofRaw (cmOrbitLattice163 g u).val (cmOrbitLattice163 g u).property *
    (ComplexRawQuotient.ofRaw (cmOrbitDenominator163 g).val (cmOrbitDenominator163 g).property *
      ComplexRawQuotient.ofRaw inv.val inv.property)=1
  grind

end ComputableAnalysis.ModularForms
