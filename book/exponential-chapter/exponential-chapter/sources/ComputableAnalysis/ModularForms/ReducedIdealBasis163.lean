import ComputableAnalysis.ModularForms.FormIdeal163

/-! Principal norm coordinates on the ideal lattice after certified form reduction. -/
namespace ComputableAnalysis.ModularForms

def IntegralForm163.reducedIdealLattice (f : IntegralForm163) (m n : Int) : QuadraticOrder163 :=
  f.idealLattice (f.reductionMatrix.a*m+f.reductionMatrix.b*n)
    (f.reductionMatrix.c*m+f.reductionMatrix.d*n)

def IntegralForm163.idealGenerator (f : IntegralForm163) : QuadraticOrder163 :=
  f.reducedIdealLattice 1 0

def IntegralForm163.idealSecondBasis (f : IntegralForm163) : QuadraticOrder163 :=
  f.reducedIdealLattice 0 1

theorem IntegralForm163.reducedIdealLattice_norm (f : IntegralForm163) (m n : Int) :
    QuadraticOrder163.norm (f.reducedIdealLattice m n)=f.a*(m*m+m*n+41*n*n) := by
  unfold reducedIdealLattice
  rw [idealLattice_norm,principal_change_of_variables]

theorem IntegralForm163.idealGenerator_norm (f : IntegralForm163) :
    QuadraticOrder163.norm f.idealGenerator=f.a := by
  have h := f.reducedIdealLattice_norm 1 0
  change QuadraticOrder163.norm f.idealGenerator=_ at h
  grind

theorem IntegralForm163.idealGenerator_mem (f : IntegralForm163) :
    f.InIdeal f.idealGenerator :=
  ⟨f.reductionMatrix.a*1+f.reductionMatrix.b*0,
    f.reductionMatrix.c*1+f.reductionMatrix.d*0,rfl⟩

theorem IntegralForm163.reducedIdealLattice_spans (f : IntegralForm163) (m n : Int) :
    f.reducedIdealLattice (f.reductionMatrix.d*m-f.reductionMatrix.b*n)
      (-f.reductionMatrix.c*m+f.reductionMatrix.a*n)=f.idealLattice m n := by
  have hd := f.reductionMatrix.determinant
  unfold reducedIdealLattice
  congr 1 <;> grind

theorem IntegralForm163.inIdeal_iff_reducedLattice (f : IntegralForm163) (z : QuadraticOrder163) :
    f.InIdeal z ↔ ∃ m n : Int, z=f.reducedIdealLattice m n := by
  constructor
  · rintro ⟨m,n,h⟩
    refine ⟨f.reductionMatrix.d*m-f.reductionMatrix.b*n,
      -f.reductionMatrix.c*m+f.reductionMatrix.a*n,?_⟩
    rw [reducedIdealLattice_spans]
    exact h
  · rintro ⟨m,n,h⟩
    exact ⟨f.reductionMatrix.a*m+f.reductionMatrix.b*n,
      f.reductionMatrix.c*m+f.reductionMatrix.d*n,h⟩

theorem IntegralForm163.reducedIdealBasis_determinant (f : IntegralForm163) :
    f.idealGenerator.x*f.idealSecondBasis.y-f.idealSecondBasis.x*f.idealGenerator.y=f.a := by
  have hd := f.reductionMatrix.determinant
  unfold idealGenerator idealSecondBasis reducedIdealLattice idealLattice
  grind

end ComputableAnalysis.ModularForms
