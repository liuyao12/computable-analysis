import ComputableAnalysis.ModularForms.PairedDivisionQuadraticPrefixes

/-! Constructed constant and quadratic coefficients for the actual regular-division series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem reciprocalSquare_nonneg (n : Nat) : 0≤reciprocalSquare (n+1) := by
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  unfold reciprocalSquare
  exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hn hn))

private theorem centerReciprocal_precise_small (n : Nat) :
    Small (pairedCenterReciprocal n).val (reciprocalSquare (n+1)) := by
  have h := reciprocalSquare_nonneg n
  refine ⟨?_,?_,?_,?_⟩
  · intro a b
    change -reciprocalSquare (n+1)≤reciprocalSquare (n+1)
    grind only
  · intro a b
    exact Rat.le_refl
  · intro a b
    change -reciprocalSquare (n+1)≤0
    grind only
  · intro a b
    exact h

private theorem scale_neg_two_small (x : Scalar) (B : Rat) (h : Small x.val B) :
    Small (scaleRat (-2) x.val) (2*B) := by
  have he : (neg (scaleRat 2 x.val)).Equiv (scaleRat (-2) x.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid x.property)) (hright := scaleRat_valid x.property)
    change -(ComplexRawQuotient.scaleRat 2 (ComplexRawQuotient.ofRaw x.val x.property))=
      ComplexRawQuotient.scaleRat (-2) (ComplexRawQuotient.ofRaw x.val x.property)
    exact ComplexRawQuotient.neg_scaleRat 2 _
  exact Small.congr (neg_valid (scaleRat_valid x.property)) (scaleRat_valid x.property) he
    (SeriesLimitLaws.small_neg (LocalODE.small_scale (show (0:Rat)≤2 by decide +kernel) h))

theorem pairedCenterConstantTerm_bound (n : Nat) :
    Small (pairedCenterConstantTerm n) (2*reciprocalSquare (n+1)) :=
  scale_neg_two_small (pairedCenterReciprocal n) _ (centerReciprocal_precise_small n)

theorem pairedCenterQuadraticTerm_bound (n : Nat) :
    Small (pairedCenterQuadraticTerm n) (4*reciprocalSquare (n+1)) := by
  let c := pairedCenterReciprocal n
  have h := Small.mul c.property c.property (reciprocalSquare_nonneg n)
    (show (0:Rat)≤1 by decide +kernel) (centerReciprocal_precise_small n) (pairedCenterReciprocal_small n)
  have hs := scale_neg_two_small ⟨mul c.val c.val,mul_valid c.property c.property⟩ _ h
  have he : 2*(2*reciprocalSquare (n+1)*1)=4*reciprocalSquare (n+1) := by grind only
  rw [he] at hs
  exact hs

def pairedCenterConstantSum : ComplexRaw :=
  inverseSquareSeriesValue pairedCenterConstantTerm pairedCenterConstantTerm_valid 2

def pairedCenterQuadraticSum : ComplexRaw :=
  inverseSquareSeriesValue pairedCenterQuadraticTerm pairedCenterQuadraticTerm_valid 4

theorem pairedCenterConstantSum_valid : pairedCenterConstantSum.Valid :=
  inverseSquareSeriesValue_valid _ _ 2 pairedCenterConstantTerm_bound

theorem pairedCenterQuadraticSum_valid : pairedCenterQuadraticSum.Valid :=
  inverseSquareSeriesValue_valid _ _ 4 pairedCenterQuadraticTerm_bound

theorem pairedCenterConstantSum_close (N : Nat) :
    Small (sub pairedCenterConstantSum (ScalarSeries.block pairedCenterConstantTerm 0 (N+1)))
      (2*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 2 pairedCenterConstantTerm_bound N

theorem pairedCenterQuadraticSum_close (N : Nat) :
    Small (sub pairedCenterQuadraticSum (ScalarSeries.block pairedCenterQuadraticTerm 0 (N+1)))
      (4*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 4 pairedCenterQuadraticTerm_bound N

end ComputableAnalysis.ModularForms
