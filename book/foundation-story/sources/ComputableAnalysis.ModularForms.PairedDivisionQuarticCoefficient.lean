import ComputableAnalysis.ModularForms.PairedInverseQuarticCenterExpansion

/-! Constructed quartic coefficient with an executable inverse-square tail schedule. -/
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

def pairedCenterQuarticTerm (n : Nat) : ComplexRaw :=
  let c := pairedCenterReciprocal n
  scaleRat (-2) (mul c.val (mul c.val c.val))

theorem pairedCenterQuarticTerm_valid (n : Nat) : (pairedCenterQuarticTerm n).Valid :=
  scaleRat_valid (mul_valid (pairedCenterReciprocal n).property
    (mul_valid (pairedCenterReciprocal n).property (pairedCenterReciprocal n).property))

theorem pairedCenterQuarticTerm_bound (n : Nat) :
    Small (pairedCenterQuarticTerm n) (8*reciprocalSquare (n+1)) := by
  let c := pairedCenterReciprocal n
  let c2 := scalarProduct c c
  have hc2 : Small c2.val (2*1*1) := Small.mul c.property c.property
    (show (0:Rat)≤1 by decide +kernel) (show (0:Rat)≤1 by decide +kernel)
    (pairedCenterReciprocal_small n) (pairedCenterReciprocal_small n)
  have hc3 := Small.mul c.property c2.property (reciprocalSquare_nonneg n)
    (show (0:Rat)≤2*1*1 by decide +kernel) (centerReciprocal_precise_small n) hc2
  have hs := scale_neg_two_small (scalarProduct c c2) _ hc3
  have he : 2*(2*reciprocalSquare (n+1)*(2*1*1))=8*reciprocalSquare (n+1) := by grind only
  rw [he] at hs
  exact hs

def pairedCenterQuarticSum : ComplexRaw :=
  inverseSquareSeriesValue pairedCenterQuarticTerm pairedCenterQuarticTerm_valid 8

theorem pairedCenterQuarticSum_valid : pairedCenterQuarticSum.Valid :=
  inverseSquareSeriesValue_valid _ _ 8 pairedCenterQuarticTerm_bound

theorem pairedCenterQuarticSum_close (N : Nat) :
    Small (sub pairedCenterQuarticSum (ScalarSeries.block pairedCenterQuarticTerm 0 (N+1)))
      (8*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 8 pairedCenterQuarticTerm_bound N

end ComputableAnalysis.ModularForms
