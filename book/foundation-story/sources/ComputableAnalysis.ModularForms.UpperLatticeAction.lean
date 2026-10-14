import ComputableAnalysis.ModularForms.UpperLatticeCongruence
import ComputableAnalysis.ModularForms.CMOrbitLatticePowers163

/-! Reciprocal lattice transformation at arbitrary represented upper-half-plane points. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

/-- The actual general reciprocal gains the automorphy denominator under
fractional-linear transformation, with a proved integral reindexing. -/
theorem latticeInverse_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (u : QuadraticOrder163) (hu : u≠zero) :
    (latticeInverse (fractionalLinear g z hz) (fractionalLinear_mem g z hz) u hu).val.Equiv
      (ComplexRaw.mul (integerAffine g.c g.d z.val)
        (latticeInverse z hz (basisIndex (latticeIndexMatrix g) u) (basisIndex_nonzero _ u hu)).val) := by
  let w := fractionalLinear g z hz
  let v := basisIndex (latticeIndexMatrix g) u
  let d : Scalar := ⟨integerAffine g.c g.d z.val,integerAffine_valid _ _ z.property⟩
  let inv := latticeInverse z hz v (basisIndex_nonzero _ u hu)
  let r : Scalar := ⟨ComplexRaw.mul d.val inv.val,ComplexRaw.mul_valid d.property inv.property⟩
  apply RepresentedReciprocal.inverse_unique (latticeVector w u)
    (latticeVector_nonzero w (fractionalLinear_mem g z hz) u hu) r
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid d.property (latticeVector w u).property)
    (hright := (latticeVector z v).property) (latticeVector_action g z hz u)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid (latticeVector z v).property inv.property)
    (hright := ComplexRaw.ofQComplex_valid QComplex.one) (latticeInverse_product z hz v _)
  rw [ComplexRawQuotient.ofRaw_mul _ _ d.property (latticeVector w u).property] at hp
  rw [ComplexRawQuotient.ofRaw_mul _ _ (latticeVector z v).property inv.property] at hi
  change ComplexRawQuotient.ofRaw (latticeVector z v).val (latticeVector z v).property *
    ComplexRawQuotient.ofRaw inv.val inv.property=(1:ScalarAlgebra.Value) at hi
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.mul_valid (latticeVector w u).property r.property)
    (hright := ComplexRaw.ofQComplex_valid QComplex.one)
  change ComplexRawQuotient.ofRaw (latticeVector w u).val (latticeVector w u).property *
    (ComplexRawQuotient.ofRaw d.val d.property * ComplexRawQuotient.ofRaw inv.val inv.property)=1
  grind

/-- The term weight law holds for every natural exponent over the full domain. -/
theorem latticeInverse_power_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (u : QuadraticOrder163) (hu : u≠zero) (k : Nat) :
    (LocalODE.power
      (latticeInverse (fractionalLinear g z hz) (fractionalLinear_mem g z hz) u hu).val k).Equiv
      (ComplexRaw.mul (LocalODE.power (integerAffine g.c g.d z.val) k)
        (LocalODE.power
          (latticeInverse z hz (basisIndex (latticeIndexMatrix g) u) (basisIndex_nonzero _ u hu)).val k)) := by
  let inv := latticeInverse z hz (basisIndex (latticeIndexMatrix g) u) (basisIndex_nonzero _ u hu)
  have hd := integerAffine_valid g.c g.d z.property
  have ht := (latticeInverse (fractionalLinear g z hz) (fractionalLinear_mem g z hz) u hu).property
  exact ComplexRaw.equiv_trans (LocalODE.power_valid _ ht k)
    (LocalODE.power_valid _ (ComplexRaw.mul_valid hd inv.property) k)
    (ComplexRaw.mul_valid (LocalODE.power_valid _ hd k) (LocalODE.power_valid _ inv.property k))
    (LocalODE.power_congr _ _ ht (ComplexRaw.mul_valid hd inv.property)
      (latticeInverse_action g z hz u hu) k)
    (representedPower_mul _ _ hd inv.property k)

end ComputableAnalysis.ModularForms
