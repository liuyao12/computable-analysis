import ComputableAnalysis.ModularForms.PairedDivisionQuadraticExpansion

/-! Agreement of the constructed quadratic coefficient with the actual holomorphic second derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- The center second-derivative terms are twice the quadratic coefficient terms. -/
theorem pairedZeroFourthTerm_quadratic_coefficient (n : Nat) :
    (pairedZeroFourthTerm n).Equiv (scaleRat 2 (pairedCenterQuadraticTerm n)) := by
  let c := pairedCenterReciprocal n
  have hp := rationalRealProduct_equiv (reciprocalSquare (n+1)) (reciprocalSquare (n+1))
  have h1 := scaleRat_equiv (r := (-4:Rat)) hp
  have h2 : (scaleRat 2 (pairedCenterQuadraticTerm n)).Equiv (scaleRat (-4) (mul c.val c.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (pairedCenterQuadraticTerm_valid n))
      (hright := scaleRat_valid (mul_valid c.property c.property))
    change ComplexRawQuotient.scaleRat 2 (ComplexRawQuotient.scaleRat (-2)
      (ComplexRawQuotient.ofRaw c.val c.property * ComplexRawQuotient.ofRaw c.val c.property))=
      ComplexRawQuotient.scaleRat (-4)
        (ComplexRawQuotient.ofRaw c.val c.property * ComplexRawQuotient.ofRaw c.val c.property)
    rw [ComplexRawQuotient.scaleRat_scaleRat]
    rw [show (2:Rat)*(-2)= -4 by decide +kernel]
  exact equiv_trans (pairedZeroFourthTerm_valid n) (scaleRat_valid (mul_valid c.property c.property))
    (scaleRat_valid (pairedCenterQuadraticTerm_valid n)) (equiv_symm h1) (equiv_symm h2)

/-- The actual inverse-fourth center sum equals twice its constructed quadratic coefficient. -/
theorem pairedZeroFourthSum_quadratic_coefficient :
    pairedZeroFourthSum.Equiv (scaleRat 2 pairedCenterQuadraticSum) := by
  let p := fun N => ScalarSeries.block pairedZeroFourthTerm 0 (N+1)
  have vp N : (p N).Valid := ScalarSeries.block_valid _ pairedZeroFourthTerm_valid 0 (N+1)
  have hp N : (p N).Equiv (scaleRat 2 (ScalarSeries.block pairedCenterQuadraticTerm 0 (N+1))) := by
    have h1 := ScalarSeries.block_congr _ _ pairedZeroFourthTerm_quadratic_coefficient 0 (N+1)
    have h2 := representedBlock_scale pairedCenterQuadraticTerm pairedCenterQuadraticTerm_valid 2 0 (N+1)
    exact equiv_trans (vp N)
      (ScalarSeries.block_valid _ (fun n => scaleRat_valid (pairedCenterQuadraticTerm_valid n)) 0 (N+1))
      (scaleRat_valid (ScalarSeries.block_valid _ pairedCenterQuadraticTerm_valid 0 (N+1))) h1 h2
  have hn N : (0:Rat)≤((N+1:Nat):Rat)⁻¹ := by
    have h : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
    exact Rat.le_of_lt (Rat.inv_pos.mpr h)
  apply RepresentedCauchySum.unique p vp (fun N => 1160*((N+1:Nat):Rat)⁻¹)
    (pairedReciprocalTail_shrinks 1160) pairedZeroFourthSum (scaleRat 2 pairedCenterQuadraticSum)
    pairedZeroFourthSum_valid (scaleRat_valid pairedCenterQuadraticSum_valid)
  · intro N
    apply (pairedZeroFourthSum_close N).mono
    have h := hn N
    grind only
  · intro N
    have h := represented_prefix_scale_close
      ⟨pairedCenterQuadraticSum,pairedCenterQuadraticSum_valid⟩
      ⟨ScalarSeries.block pairedCenterQuadraticTerm 0 (N+1),
        ScalarSeries.block_valid _ pairedCenterQuadraticTerm_valid 0 (N+1)⟩
      2 (4*((N+1:Nat):Rat)⁻¹) (by decide +kernel) (pairedCenterQuadraticSum_close N)
    have hc := Small.congr
      (sub_valid (scaleRat_valid pairedCenterQuadraticSum_valid)
        (scaleRat_valid (ScalarSeries.block_valid _ pairedCenterQuadraticTerm_valid 0 (N+1))))
      (sub_valid (scaleRat_valid pairedCenterQuadraticSum_valid) (vp N))
      (FunctionTheory.sub_congr (equiv_refl _ (scaleRat_valid pairedCenterQuadraticSum_valid)) (equiv_symm (hp N))) h
    apply hc.mono
    have h := hn N
    grind only

/-- The actual holomorphic second derivative at every valid representation of
zero equals twice the constructed quadratic coefficient. -/
theorem pairedDivisionFirstDerivativeMap_derivative_quadratic_coefficient (z : Scalar)
    (hz : pairedDivisionFirstDerivativeMap.domain z) (he : z.val.Equiv zero) :
    (pairedDivisionFirstDerivativeMap_holomorphic.derivative z hz).val.Equiv
      (scaleRat 2 pairedCenterQuadraticSum) :=
  equiv_trans (pairedDivisionFirstDerivativeMap_holomorphic.derivative z hz).property
    pairedZeroFourthSum_valid (scaleRat_valid pairedCenterQuadraticSum_valid)
    (pairedDivisionFirstDerivativeMap_derivative_at_zero z hz he) pairedZeroFourthSum_quadratic_coefficient

end ComputableAnalysis.ModularForms
