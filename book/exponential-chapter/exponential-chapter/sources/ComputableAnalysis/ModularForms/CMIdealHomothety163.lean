import ComputableAnalysis.ModularForms.IdealGeneratorUniqueness163

/-! Complex ideal lattices are homothetic to the base CM lattice. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

def InCMIdealLattice163 (I : OrderIdeal163) (z : ScalarAlgebra.Value) : Prop :=
  ∃ v : QuadraticOrder163, I.contains v ∧ v.complexValue=z

def InCMBaseLattice163 (z : ScalarAlgebra.Value) : Prop :=
  ∃ v : QuadraticOrder163, v.complexValue=z

theorem cmIdealLattice163_homothety (I : OrderIdeal163)
    (hn : ∃ v, I.contains v ∧ v≠zero) :
    ∃ u : QuadraticOrder163, u.complexValue≠0 ∧
      ∀ z, InCMIdealLattice163 I z ↔
        ∃ w : ScalarAlgebra.Value, InCMBaseLattice163 w ∧ z=u.complexValue*w := by
  obtain ⟨u,hu,hprincipal⟩ := I.exists_principal_generator hn
  refine ⟨u,?_,?_⟩
  · intro hz
    exact hu ((complexValue_eq_zero_iff u).mp hz)
  · intro z
    constructor
    · rintro ⟨v,hv,hvz⟩
      obtain ⟨w,hw⟩ := (hprincipal v).mp hv
      refine ⟨w.complexValue,⟨w,rfl⟩,?_⟩
      rw [← hvz,hw,complexValue_mul]
    · rintro ⟨w,⟨v,hv⟩,hz⟩
      refine ⟨mul u v,(hprincipal _).mpr ⟨v,rfl⟩,?_⟩
      rw [complexValue_mul,hv,hz]

theorem cmIdealLattice163_raw_factorization (I : OrderIdeal163)
    (hn : ∃ v, I.contains v ∧ v≠zero) :
    ∃ u : QuadraticOrder163, u≠zero ∧
      ∀ z : QuadraticOrder163, I.contains z ↔
        ∃ v : QuadraticOrder163,
          z.complexRaw.Equiv (ComplexRaw.mul u.complexRaw v.complexRaw) := by
  obtain ⟨u,hu,hprincipal⟩ := I.exists_principal_generator hn
  refine ⟨u,hu,?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨v,hv⟩ := (hprincipal z).mp hz
    refine ⟨v,?_⟩
    rw [hv]
    exact complexRaw_mul u v
  · rintro ⟨v,hv⟩
    have he := ComplexRaw.equiv_trans z.complexRaw_valid
      (ComplexRaw.mul_valid u.complexRaw_valid v.complexRaw_valid)
      (mul u v).complexRaw_valid hv (ComplexRaw.equiv_symm (complexRaw_mul u v))
    have hz := (complexRaw_equiv_iff z (mul u v)).mp he
    exact (hprincipal z).mpr ⟨v,hz⟩

end ComputableAnalysis.ModularForms
