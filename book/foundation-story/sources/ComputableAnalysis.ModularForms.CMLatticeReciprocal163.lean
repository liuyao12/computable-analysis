import ComputableAnalysis.ModularForms.CMOrderConjugation163

/-! Certified executable reciprocals of all nonzero integral CM lattice points. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163
open RiemannHilbert

def complexScalar (u : QuadraticOrder163) : Scalar := ⟨u.complexRaw,u.complexRaw_valid⟩

theorem complexScalar_nonzero (u : QuadraticOrder163) (hu : u≠zero) :
    NonzeroBoxSearch.Nonzero u.complexScalar := by
  intro hz
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := u.complexRaw_valid) (hright := ComplexRaw.ofQComplex_valid QComplex.zero) hz
  change u.complexValue=0 at he
  exact hu ((complexValue_eq_zero_iff u).mp he)

def complexInverse (u : QuadraticOrder163) (hu : u≠zero) : Scalar :=
  RepresentedReciprocal.inverse u.complexScalar (complexScalar_nonzero u hu)

theorem complexInverse_product (u : QuadraticOrder163) (hu : u≠zero) :
    (ComplexRaw.mul u.complexRaw (complexInverse u hu).val).Equiv ComplexRaw.one :=
  RepresentedReciprocal.mul_inverse u.complexScalar (complexScalar_nonzero u hu)

theorem complexInverse_unique (u : QuadraticOrder163) (hu : u≠zero) (r : Scalar)
    (hr : (ComplexRaw.mul u.complexRaw r.val).Equiv ComplexRaw.one) :
    (complexInverse u hu).val.Equiv r.val :=
  RepresentedReciprocal.inverse_unique u.complexScalar (complexScalar_nonzero u hu) r hr

end ComputableAnalysis.ModularForms.QuadraticOrder163
