import ComputableAnalysis.ModularForms.PairedRegularDivisionTermHolomorphic

/-! Actual derivative terms and summable bounds for regular division. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRegularDivisionDerivativeTerm (z : Scalar) (hz : LocalODE.interior (1/4) z) (n : Nat) : Scalar :=
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let d : Scalar := ⟨neg (mul i.val i.val),neg_valid (mul_valid i.property i.property)⟩
  let v := DomainFunctions.scalarProduct d (DomainFunctions.scalarSum z z)
  DomainFunctions.scalarSum v v

theorem pairedRegularDivisionTermMap_derivative (n : Nat) (z : Scalar) (hz : LocalODE.interior (1/4) z) :
    ((pairedRegularDivisionTermMap_holomorphic n).derivative z hz).val.Equiv
      (pairedRegularDivisionDerivativeTerm z hz n).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedRegularDivisionTermMap_holomorphic n).derivative z hz).property)
    (hright := (pairedRegularDivisionDerivativeTerm z hz n).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw ((pairedSmallDiskLiteralInverseMap n).eval z hz).val
    ((pairedSmallDiskLiteralInverseMap n).eval z hz).property
  change (-(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1)))+
    (-(I*I)*(1*(1*(0+1*Z)+(0+1*Z)*1))) = (-(I*I)*(Z+Z))+(-(I*I)*(Z+Z))
  grind only

theorem pairedRegularDivisionDerivativeTerm_bound (z : Scalar) (hz : LocalODE.interior (1/4) z) (n : Nat) :
    Small (pairedRegularDivisionDerivativeTerm z hz n).val
      (64*reciprocalSquare (n+1)*reciprocalSquare (n+1)) := by
  let hq := LocalODE.interior_bound _ z hz
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  have hi : Small i.val (4*reciprocalSquare (n+1)) := pairedSmallDiskLiteralInverse_bound z hq n
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hc : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hm := Rat.mul_nonneg (show (0:Rat)≤4 by decide) hc
  have hsq := SeriesLimitLaws.small_neg (Small.mul i.property i.property hm hm hi hi)
  have hs := LocalODE.small_add hq hq
  have hb := Small.mul (neg_valid (mul_valid i.property i.property)) (add_valid z.property z.property)
    (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hm) hm)
    (show (0:Rat)≤1/4+1/4 by decide +kernel) hsq hs
  have h := LocalODE.small_add hb hb
  exact h.mono (by grind only)

theorem pairedRegularDivisionDerivativeTerm_square_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) :
    Small (pairedRegularDivisionDerivativeTerm z hz n).val (64*reciprocalSquare (n+1)) := by
  apply (pairedRegularDivisionDerivativeTerm_bound z hz n).mono
  have hr := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
  rw [show reciprocalSquare 1=1 by decide +kernel] at hr
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hc : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have h := Rat.mul_le_mul_of_nonneg_left hr (Rat.mul_nonneg (show (0:Rat)≤64 by decide) hc)
  grind only

def pairedRegularDivisionDerivativeValue (z : Scalar) (hz : LocalODE.interior (1/4) z) : ComplexRaw :=
  inverseSquareSeriesValue (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val)
    (fun n => (pairedRegularDivisionDerivativeTerm z hz n).property) 64

theorem pairedRegularDivisionDerivativeValue_valid (z : Scalar) (hz : LocalODE.interior (1/4) z) :
    (pairedRegularDivisionDerivativeValue z hz).Valid :=
  inverseSquareSeriesValue_valid _ _ 64 (pairedRegularDivisionDerivativeTerm_square_bound z hz)

theorem pairedRegularDivisionDerivativeValue_close (z : Scalar) (hz : LocalODE.interior (1/4) z) (N : Nat) :
    Small (sub (pairedRegularDivisionDerivativeValue z hz)
      (ScalarSeries.block (fun n => (pairedRegularDivisionDerivativeTerm z hz n).val) 0 (N+1)))
      (64*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 64 (pairedRegularDivisionDerivativeTerm_square_bound z hz) N

end ComputableAnalysis.ModularForms
