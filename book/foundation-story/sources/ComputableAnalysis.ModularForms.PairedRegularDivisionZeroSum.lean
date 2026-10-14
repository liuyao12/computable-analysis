import ComputableAnalysis.ModularForms.PairedRegularDivisionZeroInverse

/-! Exact inverse-square series evaluation of regular division at zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedZeroSquareTerm (n : Nat) : ComplexRaw :=
  scaleRat 2 (ofQComplex ⟨-reciprocalSquare (n+1),0⟩)

theorem pairedRegularDivisionTerm_at_zero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (he : z.val.Equiv zero) (n : Nat) :
    (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).val.Equiv (pairedZeroSquareTerm n) :=
  scaleRat_equiv (pairedSmallDiskLiteralInverse_at_zero z hz he n)

def pairedZeroScalar : Scalar := ⟨zero,ofQComplex_valid _⟩

theorem pairedZeroScalar_interior : LocalODE.interior (1/4) pairedZeroScalar :=
  ⟨0,by decide,by decide +kernel,Small.zero (by decide)⟩

theorem pairedZeroSquareTerm_bound (n : Nat) :
    Small (pairedZeroSquareTerm n) (8*reciprocalSquare (n+1)) :=
  Small.congr (pairedRegularDivisionTerm pairedZeroScalar
      (LocalODE.interior_bound _ _ pairedZeroScalar_interior) n).property
    (scaleRat_valid (ofQComplex_valid _))
    (pairedRegularDivisionTerm_at_zero pairedZeroScalar pairedZeroScalar_interior
      (equiv_refl _ pairedZeroScalar.property) n)
    (pairedRegularDivisionTerm_bound pairedZeroScalar
      (LocalODE.interior_bound _ _ pairedZeroScalar_interior) n)

def pairedZeroSquareSum : ComplexRaw :=
  inverseSquareSeriesValue pairedZeroSquareTerm (fun _ => scaleRat_valid (ofQComplex_valid _)) 8

theorem pairedZeroSquareSum_valid : pairedZeroSquareSum.Valid :=
  inverseSquareSeriesValue_valid _ _ 8 pairedZeroSquareTerm_bound

theorem pairedZeroSquareSum_close (N : Nat) :
    Small (sub pairedZeroSquareSum (ScalarSeries.block pairedZeroSquareTerm 0 (N+1)))
      (8*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 8 pairedZeroSquareTerm_bound N

theorem pairedRegularDivisionValue_at_zero (z : Scalar) (hz : LocalODE.interior (1/4) z)
    (he : z.val.Equiv zero) :
    (pairedRegularDivisionMap.eval z hz).val.Equiv pairedZeroSquareSum :=
  inverseSquareSeriesValue_congr _ _
    (fun n => (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).property)
    (fun _ => scaleRat_valid (ofQComplex_valid _)) 8
    (pairedRegularDivisionTerm_bound z (LocalODE.interior_bound _ z hz)) pairedZeroSquareTerm_bound
    (pairedRegularDivisionTerm_at_zero z hz he)

end ComputableAnalysis.ModularForms
