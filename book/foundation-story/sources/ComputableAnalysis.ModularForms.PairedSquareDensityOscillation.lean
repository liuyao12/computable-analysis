import ComputableAnalysis.ModularForms.PairedSquareKernelOscillation
import ComputableAnalysis.ModularForms.PairedRiccatiSquareSums

/-! Arbitrary-error dyadic oscillation of the actual oriented square density. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

theorem constantProduct_difference (a b c : Scalar) :
    (mul (sub a.val b.val) c.val).Equiv
      (sub (mul a.val c.val) (mul b.val c.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (sub_valid a.property b.property) c.property)
    (hright := sub_valid (mul_valid a.property c.property) (mul_valid b.property c.property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  change (A-B)*C=A*C-B*C
  grind only

theorem pairedSquareDensity_dyadic_oscillation (a : Scalar) (edge : HalfEdge)
    (R : Rat) (hR : 0<R) (eps : QPos) :
    ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n → ∀ u v : Rat,
      (bisectionInterval ⟨0,1⟩ choice n).lo≤u →
      u≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      (bisectionInterval ⟨0,1⟩ choice n).lo≤v →
      v≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      Small (sub (pairedSquareDensity a edge u R) (pairedSquareDensity a edge v R)) eps.val := by
  have hden : 0<2*R := Rat.mul_pos (by decide +kernel) hR
  let e : QPos := ⟨eps.val/(2*R), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr hden)⟩
  have he : 2*e.val*R=eps.val := by
    have hc := Rat.mul_inv_cancel (2*R) (Rat.ne_of_gt hden)
    dsimp [e]
    rw [Rat.div_def]
    grind only
  obtain ⟨N,hN⟩ := actualSquareKernel_dyadic_oscillation a edge R hR e
  refine ⟨N, ?_⟩
  intro choice n hn u v hulo huhi hvlo hvhi
  let U := actualSquareKernelSample a edge R u
  let V := actualSquareKernelSample a edge R v
  let C : Scalar := ⟨ofQComplex (QComplex.scaleRat R (velocity edge)),ofQComplex_valid _⟩
  have hc := (BoxApproximation.rational_small _).mono
    (scaledSquareVelocity_coordinate_bound edge R (Rat.le_of_lt hR))
  have hb := Small.mul (sub_valid U.property V.property) C.property
    (Rat.le_of_lt e.property) (Rat.le_of_lt hR)
    (hN choice n hn u v hulo huhi hvlo hvhi) hc
  rw [he] at hb
  have hd := Small.congr (mul_valid (sub_valid U.property V.property) C.property)
    (sub_valid (mul_valid U.property C.property) (mul_valid V.property C.property))
    (constantProduct_difference U V C) hb
  cases hed : edge.upper
  · have hneg := SeriesLimitLaws.small_neg hd
    have hev : (neg (sub (mul U.val C.val) (mul V.val C.val))).Equiv
        (sub (neg (mul U.val C.val)) (neg (mul V.val C.val))) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := neg_valid (sub_valid (mul_valid U.property C.property) (mul_valid V.property C.property)))
        (hright := sub_valid (neg_valid (mul_valid U.property C.property))
          (neg_valid (mul_valid V.property C.property)))
      let X := ComplexRawQuotient.ofRaw U.val U.property
      let Y := ComplexRawQuotient.ofRaw V.val V.property
      let Z := ComplexRawQuotient.ofRaw C.val C.property
      change -(X*Z-Y*Z)= -(X*Z)- -(Y*Z)
      grind only
    have hn' := Small.congr
      (neg_valid (sub_valid (mul_valid U.property C.property) (mul_valid V.property C.property)))
      (sub_valid (neg_valid (mul_valid U.property C.property)) (neg_valid (mul_valid V.property C.property))) hev hneg
    simpa only [pairedSquareDensity,hed,Bool.false_eq_true,if_false,U,V,C,actualSquareKernelSample,rationalSquaredKernel] using hn'
  · simpa only [pairedSquareDensity,hed,if_true,U,V,C,actualSquareKernelSample,rationalSquaredKernel] using hd

end ComputableAnalysis.ModularForms
