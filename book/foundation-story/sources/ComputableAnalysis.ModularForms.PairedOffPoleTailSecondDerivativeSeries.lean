import ComputableAnalysis.ModularForms.PairedOffPoleTailSecondDerivativeTerms

/-! A constructed, uniformly controlled second-derivative tail on the full disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailSecondDerivativeConstant (B : Nat) : Nat := 768*B+32768*B*B*B

theorem pairedOffPoleTailSecondDerivativeTerm_bound (B n : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    Small (pairedOffPoleTailSecondDerivativeTerm B n z hz).val
      ((pairedOffPoleTailSecondDerivativeConstant B:Rat)*reciprocalSquare (n+1)) := by
  have hB : (0:Rat)≤(B:Rat) := Rat.natCast_nonneg
  let c := reciprocalSquare (n+1)
  have hp : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hc : 0≤c := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hp hp))
  have hcle : c≤1 := by
    have h := pairedDerivative_reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
    simpa only [show reciprocalSquare 1=1 by decide +kernel] using h
  let i := pairedOffPoleTailInverse B n z hz
  have hi : Small i.val (4*c) := (pairedOffPoleTailInverse_bound B n z hz).mono
    (Rat.mul_le_mul_of_nonneg_left
      (pairedDerivative_reciprocalSquare_antitone (n+1) (pairedTailShift B n)
        (by omega) (by unfold pairedTailShift; omega)) (by decide +kernel))
  have hi4 : Small i.val 4 := hi.mono (by grind only)
  have hsq := Small.mul i.property i.property
    (Rat.mul_nonneg (by decide +kernel) hc) (show (0:Rat)≤4 by decide +kernel) hi hi4
  have hcu := Small.mul i.property (mul_valid i.property i.property)
    (show (0:Rat)≤4 by decide +kernel) (by grind only) hi4 hsq
  have hzz := Small.mul z.property z.property Rat.natCast_nonneg Rat.natCast_nonneg
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ z hz)
  have hzznonneg : 0≤2*(B:Rat)*(B:Rat) :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hB
  have hzzznonneg : 0≤2*(2*(B:Rat)*(B:Rat))*(B:Rat) :=
    Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hzznonneg) hB
  have hzzz := Small.mul (mul_valid z.property z.property) z.property
    hzznonneg Rat.natCast_nonneg hzz (LocalODE.interior_bound _ z hz)
  have ha := SeriesLimitLaws.small_neg (Small.mul z.property (mul_valid i.property i.property)
    Rat.natCast_nonneg (by grind only) (LocalODE.interior_bound _ z hz) hsq)
  have hb := Small.mul (mul_valid (mul_valid z.property z.property) z.property)
    (mul_valid i.property (mul_valid i.property i.property)) hzzznonneg (by grind only) hzzz hcu
  have ha2 := LocalODE.small_add ha ha
  have ha4 := LocalODE.small_add ha2 ha2
  have ha8 := LocalODE.small_add ha4 ha4
  have hb2 := LocalODE.small_add hb hb
  have hb4 := LocalODE.small_add hb2 hb2
  have hb8 := LocalODE.small_add hb4 hb4
  have hb16 := LocalODE.small_add hb8 hb8
  apply (LocalODE.small_add (LocalODE.small_add ha4 ha8) hb16).mono
  simp only [pairedOffPoleTailSecondDerivativeConstant,Rat.natCast_add,Rat.natCast_mul,
    show ((768:Nat):Rat)=768 by decide +kernel,show ((32768:Nat):Rat)=32768 by decide +kernel]
  grind only

def pairedOffPoleTailSecondDerivativeValue (B : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) : Scalar :=
  ⟨inverseSquareSeriesValue (fun n => (pairedOffPoleTailSecondDerivativeTerm B n z hz).val)
    (fun n => (pairedOffPoleTailSecondDerivativeTerm B n z hz).property)
    (pairedOffPoleTailSecondDerivativeConstant B),
    inverseSquareSeriesValue_valid _ _ _ (fun n => pairedOffPoleTailSecondDerivativeTerm_bound B n z hz)⟩

theorem pairedOffPoleTailSecondDerivativeValue_close (B : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) (N : Nat) :
    Small (sub (pairedOffPoleTailSecondDerivativeValue B z hz).val
      (ScalarSeries.block (fun n => (pairedOffPoleTailSecondDerivativeTerm B n z hz).val) 0 (N+1)))
      ((pairedOffPoleTailSecondDerivativeConstant B:Rat)*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ (fun n => (pairedOffPoleTailSecondDerivativeTerm B n z hz).property)
    _ (fun n => pairedOffPoleTailSecondDerivativeTerm_bound B n z hz) N

theorem pairedOffPoleTailSecondDerivativeValue_bound (B : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    Small (pairedOffPoleTailSecondDerivativeValue B z hz).val
      (2*(pairedOffPoleTailSecondDerivativeConstant B:Rat)) :=
  inverseSquareSeriesValue_bound _ (fun n => (pairedOffPoleTailSecondDerivativeTerm B n z hz).property)
    _ (fun n => pairedOffPoleTailSecondDerivativeTerm_bound B n z hz)

end ComputableAnalysis.ModularForms
