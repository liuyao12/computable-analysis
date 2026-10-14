import ComputableAnalysis.ModularForms.PairedDivisionDerivativeTermHolomorphic

/-! Explicit second derivatives of the actual division-series terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def doubleScalar (x : Scalar) : Scalar := scalarSum x x

def pairedDivisionSecondDerivativeTerm (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) : Scalar :=
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let a := scalarNeg (DomainFunctions.scalarProduct i i)
  let b := DomainFunctions.scalarProduct (DomainFunctions.scalarProduct z z)
    (DomainFunctions.scalarProduct i (DomainFunctions.scalarProduct i i))
  scalarSum (doubleScalar (doubleScalar a))
    (doubleScalar (doubleScalar (doubleScalar (doubleScalar b))))

theorem pairedDivisionDerivativeTermMap_derivative (n : Nat) (z : Scalar)
    (hz : LocalODE.interior (1/4) z) :
    ((pairedDivisionDerivativeTermMap_holomorphic n).derivative z hz).val.Equiv
      (pairedDivisionSecondDerivativeTerm z hz n).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedDivisionDerivativeTermMap_holomorphic n).derivative z hz).property)
    (hright := (pairedDivisionSecondDerivativeTerm z hz n).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval z hz).val
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).property
  change (((-((-(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1)))*I+I*(-(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1)))))*((0+1*Z)+(0+1*Z))+(-(I*I))*(1+1))+((-((-(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1)))*I+I*(-(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1)))))*((0+1*Z)+(0+1*Z))+(-(I*I))*(1+1))) = ((-(I*I)+-(I*I))+(-(I*I)+-(I*I)))+(((((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))+((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I))))+(((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))+((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))))+((((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))+((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I))))+(((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))+((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I))))))
  grind only

theorem pairedDivisionSecondDerivativeTerm_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) :
    Small (pairedDivisionSecondDerivativeTerm z hz n).val
      (1152*reciprocalSquare (n+1)) := by
  let c := reciprocalSquare (n+1)
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hc : 0≤c := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hcle : c≤1 := by
    have h := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
    simpa only [show reciprocalSquare 1=1 by decide +kernel] using h
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  have hi : Small i.val (4*c) := pairedSmallDiskLiteralInverse_bound z
    (LocalODE.interior_bound _ z hz) n
  have hi4 : Small i.val 4 := hi.mono (by grind only)
  have hsq := Small.mul i.property i.property
    (Rat.mul_nonneg (by decide +kernel) hc) (show (0:Rat)≤4 by decide +kernel) hi hi4
  have hcu := Small.mul i.property (mul_valid i.property i.property)
    (show (0:Rat)≤4 by decide +kernel) (by grind only) hi4 hsq
  have hzz := Small.mul z.property z.property
    (show (0:Rat)≤1/4 by decide +kernel) (show (0:Rat)≤1/4 by decide +kernel)
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ z hz)
  have hb := Small.mul (mul_valid z.property z.property)
    (mul_valid i.property (mul_valid i.property i.property))
    (by decide +kernel) (by grind only) hzz hcu
  have ha := SeriesLimitLaws.small_neg hsq
  have haa := LocalODE.small_add ha ha
  have ha4 := LocalODE.small_add haa haa
  have hb2 := LocalODE.small_add hb hb
  have hb4 := LocalODE.small_add hb2 hb2
  have hb8 := LocalODE.small_add hb4 hb4
  have hb16 := LocalODE.small_add hb8 hb8
  exact (LocalODE.small_add ha4 hb16).mono (by grind only)

def pairedDivisionSecondDerivativeValue (z : Scalar)
    (hz : LocalODE.interior (1/4) z) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedDivisionSecondDerivativeTerm z hz n).val)
    (fun n => (pairedDivisionSecondDerivativeTerm z hz n).property) 1152

theorem pairedDivisionSecondDerivativeValue_valid (z : Scalar)
    (hz : LocalODE.interior (1/4) z) : (pairedDivisionSecondDerivativeValue z hz).Valid :=
  inverseSquareSeriesValue_valid _ _ 1152 (pairedDivisionSecondDerivativeTerm_bound z hz)

theorem pairedDivisionSecondDerivativeValue_close (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (N : Nat) :
    Small (sub (pairedDivisionSecondDerivativeValue z hz)
      (ScalarSeries.block (fun n => (pairedDivisionSecondDerivativeTerm z hz n).val) 0 (N+1)))
      (1152*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 1152 (pairedDivisionSecondDerivativeTerm_bound z hz) N

theorem pairedDivisionSecondDerivativeTerm_congr (a b : Scalar)
    (ha : LocalODE.interior (1/4) a) (hb : LocalODE.interior (1/4) b)
    (he : a.val.Equiv b.val) (n : Nat) :
    (pairedDivisionSecondDerivativeTerm a ha n).val.Equiv
      (pairedDivisionSecondDerivativeTerm b hb n).val := by
  let hf := pairedDivisionDerivativeTermMap_holomorphic n
  exact equiv_trans (pairedDivisionSecondDerivativeTerm a ha n).property
    (hf.derivative a ha).property (pairedDivisionSecondDerivativeTerm b hb n).property
    (equiv_symm (pairedDivisionDerivativeTermMap_derivative n a ha))
    (equiv_trans (hf.derivative a ha).property (hf.derivative b hb).property
      (pairedDivisionSecondDerivativeTerm b hb n).property
      (hf.derivative_congr a b ha hb he)
      (pairedDivisionDerivativeTermMap_derivative n b hb))

theorem pairedDivisionSecondDerivativeValue_congr (a b : Scalar)
    (ha : LocalODE.interior (1/4) a) (hb : LocalODE.interior (1/4) b)
    (he : a.val.Equiv b.val) :
    (pairedDivisionSecondDerivativeValue a ha).Equiv
      (pairedDivisionSecondDerivativeValue b hb) :=
  inverseSquareSeriesValue_congr _ _
    (fun n => (pairedDivisionSecondDerivativeTerm a ha n).property)
    (fun n => (pairedDivisionSecondDerivativeTerm b hb n).property) 1152
    (pairedDivisionSecondDerivativeTerm_bound a ha)
    (pairedDivisionSecondDerivativeTerm_bound b hb)
    (pairedDivisionSecondDerivativeTerm_congr a b ha hb he)

def pairedDivisionSecondDerivativeMap : DomainFunctions.Map where
  domain := LocalODE.interior (1/4)
  eval z hz := ⟨pairedDivisionSecondDerivativeValue z hz,
    pairedDivisionSecondDerivativeValue_valid z hz⟩
  domain_congr := pairedRegularDivisionMap.domain_congr
  eval_congr := pairedDivisionSecondDerivativeValue_congr

end ComputableAnalysis.ModularForms
