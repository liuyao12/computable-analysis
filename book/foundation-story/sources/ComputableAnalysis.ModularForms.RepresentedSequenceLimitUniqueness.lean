import ComputableAnalysis.ModularForms.PairedSquareContourConvergence

/-! Uniqueness follows from convergence to common samples and shrinking
rational errors, rather than being a field assumed in a certificate. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem representedSequenceLimit_unique (p : Nat → Scalar) (x y : Scalar)
    (hx : ∀ eps : QPos, ∃ N, ∀ n, N≤n → Small (sub x.val (p n).val) eps.val)
    (hy : ∀ eps : QPos, ∃ N, ∀ n, N≤n → Small (sub y.val (p n).val) eps.val) :
    x.val.Equiv y.val := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed (sub x.val y.val) 0
    (fun k => 2*(RepresentedCauchySum.error k).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks 2 (by decide +kernel))
  intro k
  obtain ⟨X,hX⟩ := hx (RepresentedCauchySum.error k)
  obtain ⟨Y,hY⟩ := hy (RepresentedCauchySum.error k)
  let M := p (max X Y)
  have hb := LocalODE.small_add (hX (max X Y) (Nat.le_max_left _ _))
    (SeriesLimitLaws.small_neg (hY (max X Y) (Nat.le_max_right _ _)))
  have he : (add (sub x.val M.val) (neg (sub y.val M.val))).Equiv (sub x.val y.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid x.property M.property) (neg_valid (sub_valid y.property M.property)))
      (hright := sub_valid x.property y.property)
    let A := ComplexRawQuotient.ofRaw x.val x.property
    let B := ComplexRawQuotient.ofRaw y.val y.property
    let C := ComplexRawQuotient.ofRaw M.val M.property
    change (A-C)+ -(B-C)=A-B
    grind only
  have hd := Small.congr
    (add_valid (sub_valid x.property M.property) (neg_valid (sub_valid y.property M.property)))
    (sub_valid x.property y.property) he hb
  have hsum : (RepresentedCauchySum.error k).val+(RepresentedCauchySum.error k).val=
      0+2*(RepresentedCauchySum.error k).val := by grind only
  rw [hsum] at hd
  exact hd

theorem pairedSquareContourLimit_unique (a : Scalar) (R : Rat) (hR : 0<R)
    (z : Scalar)
    (hz : ∀ eps : QPos, ∃ N, ∀ n, N≤n →
      Small (sub z.val (pairedSquareDyadicContour a R n).val) eps.val) :
    z.val.Equiv (pairedSquareContourLimit a R hR) :=
  representedSequenceLimit_unique (pairedSquareDyadicContour a R) z
    ⟨pairedSquareContourLimit a R hR, pairedSquareContourLimit_valid a R hR⟩ hz
    (pairedSquareContourLimit_convergence a R hR)

end ComputableAnalysis.ModularForms
