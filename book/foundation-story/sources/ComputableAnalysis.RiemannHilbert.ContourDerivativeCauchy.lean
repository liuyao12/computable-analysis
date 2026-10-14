import ComputableAnalysis.RiemannHilbert.ContourDerivativeFinite

/-! The actual first rectangular Cauchy moment converges to the supplied
complex derivative times the independently constructed geometric period.
No Taylor expansion, coefficient-limit witness, or derivative holomorphy
is assumed. The finite-cover stages remain existential inside Prop. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

theorem fixedRectangleDerivativeContour_converges_to (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (d : Scalar)
    (hd : HasDerivativeAt f b (hdom _ (rectanglePoleInterior_mem J b hb)) d) :
    Converges (fixedRectangleDerivativeContour f J hdom b hb) (scalarProduct d geometricPeriod) := by
  intro eps
  have ho := rectanglePoleInterior_ordered J b hb
  obtain ⟨D,hmargin⟩ := hb
  obtain ⟨F0,hF0,bF⟩ := continuousRectangleBoundary_rational_bound f hf.continuous J ho.1 ho.2
    (rectangleBoundaryDomains_of_rectangle f J ho.1 ho.2 hdom)
  obtain ⟨U0,hU0,bU⟩ := continuousRectangleBoundary_rational_bound (ribbonPoleReciprocal b)
    (ribbonPoleReciprocal_holomorphic b).continuous J ho.1 ho.2 (rectanglePoleReciprocalBoundaryDomains J b ⟨D,hmargin⟩)
  let F := F0+1
  let U := U0+1
  have hF : 0<F := by dsimp [F]; grind only
  have hU : 0<U := by dsimp [U]; grind only
  let eta := divideRadius eps (⟨3,by decide +kernel⟩ : QPos)
  let T : QPos := ⟨2*scalarBound geometricPeriod,Rat.mul_pos (by decide +kernel) (scalarBound_pos geometricPeriod)⟩
  let theta := divideRadius eta T
  have hW : 0≤4*(J.1.width+J.2.width) := by
    have hx : 0≤J.1.width := by unfold QInterval.width; grind only
    have hy : 0≤J.2.width := by unfold QInterval.width; grind only
    exact Rat.mul_nonneg (by decide +kernel) (Rat.add_nonneg hx hy)
  let C0 := 4*(J.1.width+J.2.width)*(128*F*U*U*U)
  have hC0 : 0≤C0 := Rat.mul_nonneg hW
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
      (Rat.le_of_lt hF)) (Rat.le_of_lt hU)) (Rat.le_of_lt hU)) (Rat.le_of_lt hU))
  let C : QPos := ⟨C0+1,by grind only⟩
  let V : QPos := ⟨16*U,Rat.mul_pos (by decide +kernel) hU⟩
  let h := minRadius (divideRadius D (⟨2,by decide +kernel⟩ : QPos))
    (minRadius (hd.delta theta) (minRadius (divideRadius unitError V) (divideRadius eta C)))
  have hD : h.val≤D.val/2 := by
    have ht := minRadius_left (divideRadius D (⟨2,by decide +kernel⟩ : QPos))
      (minRadius (hd.delta theta) (minRadius (divideRadius unitError V) (divideRadius eta C)))
    have he := divideRadius_identity D (⟨2,by decide +kernel⟩ : QPos)
    change 2*(divideRadius D (⟨2,by decide +kernel⟩ : QPos)).val=D.val at he
    dsimp [h]
    grind only
  have hdelta : h.val≤(hd.delta theta).val := Rat.le_trans (minRadius_right _ _) (minRadius_left _ _)
  have hV : h.val≤(divideRadius unitError V).val :=
    Rat.le_trans (minRadius_right _ _) (Rat.le_trans (minRadius_right _ _) (minRadius_left _ _))
  have hC : h.val≤(divideRadius eta C).val :=
    Rat.le_trans (minRadius_right _ _) (Rat.le_trans (minRadius_right _ _) (minRadius_right _ _))
  have hbudget : 16*U*h.val≤1 := by
    have hm := Rat.mul_le_mul_of_nonneg_left hV (Rat.le_of_lt V.property)
    have he := divideRadius_identity unitError V
    change 16*U*(divideRadius unitError V).val=1 at he
    rw [he] at hm
    exact hm
  have herror : 4*(J.1.width+J.2.width)*(128*F*U*U*U*h.val)≤eta.val := by
    have hm := Rat.mul_le_mul_of_nonneg_left hC (Rat.le_of_lt C.property)
    have he := divideRadius_identity eta C
    have hp := h.property
    change (C0+1)*h.val≤(C0+1)*(divideRadius eta C).val at hm
    change (C0+1)*(divideRadius eta C).val=eta.val at he
    dsimp [C0] at hm he
    grind only
  let hc := rectanglePoleInterior_rationalShift J b D h hmargin hD
  let ha := hdom b (rectanglePoleInterior_mem J b ⟨D,hmargin⟩)
  let hz := hdom (rationalShift b h) (rectanglePoleInterior_mem J _ hc)
  let Q := fixedRectanglePoleQuotient f J hdom b ⟨D,hmargin⟩ h hc
  let L := scalarProduct (rationalFunctionQuotient f b ha h hz) geometricPeriod
  let A := scalarProduct d geometricPeriod
  obtain ⟨N,hN⟩ := fixedRectanglePoleQuotient_converges f hf J hdom b ⟨D,hmargin⟩ h hc eta
  have hderiv := rationalFunctionQuotient_error f b ha d hd theta h hz hdelta
  have hmul := Small.mul (sub_valid (rationalFunctionQuotient f b ha h hz).property d.property)
    geometricPeriod.property (Rat.le_of_lt theta.property) (Rat.le_of_lt (scalarBound_pos geometricPeriod))
    hderiv (scalar_small geometricPeriod)
  have heT : 2*theta.val*scalarBound geometricPeriod=eta.val := by
    have ht := divideRadius_identity eta T
    change (2*scalarBound geometricPeriod)*theta.val=eta.val at ht
    grind only
  rw [heT] at hmul
  have hLA : Small (sub L.val A.val) eta.val := by
    have he : gridScalarSub L A≈scalarProduct (gridScalarSub (rationalFunctionQuotient f b ha h hz) d) geometricPeriod := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (gridScalarSub L A).property)
        (hright := (scalarProduct (gridScalarSub (rationalFunctionQuotient f b ha h hz) d) geometricPeriod).property)
      let X := gridScalarValue (rationalFunctionQuotient f b ha h hz)
      let Y := gridScalarValue d
      let P := gridScalarValue geometricPeriod
      change X*P-Y*P=(X-Y)*P
      grind only
    exact Small.congr (mul_valid (sub_valid (rationalFunctionQuotient f b ha h hz).property d.property)
      geometricPeriod.property) (sub_valid L.property A.property) (equiv_symm he) hmul
  refine ⟨N,?_⟩
  intro n hn
  let X := fixedRectangleDerivativeContour f J hdom b ⟨D,hmargin⟩ n
  have hQX := (fixedRectanglePoleQuotient_error f J hdom b ⟨D,hmargin⟩ h hc F U
    (Rat.le_of_lt hF) (Rat.le_of_lt hU)
    (fun q hq hz => (bF q hq hz).mono (by dsimp [F]; grind only))
    (fun q hq hz => (bU q hq hz).mono (by dsimp [U]; grind only)) hbudget n).mono herror
  have hXQ : Small (sub X.val (Q n).val) eta.val := by
    have he : gridScalarSub X (Q n)≈scalarNeg (gridScalarSub (Q n) X) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (gridScalarSub X (Q n)).property)
        (hright := (scalarNeg (gridScalarSub (Q n) X)).property)
      change gridScalarValue X-gridScalarValue (Q n)= -(gridScalarValue (Q n)-gridScalarValue X)
      grind only
    exact Small.congr (neg_valid (sub_valid (Q n).property X.property))
      (sub_valid X.property (Q n).property) (equiv_symm he) (SeriesLimitLaws.small_neg hQX)
  have hs := LocalODE.small_add (LocalODE.small_add hXQ (hN n hn)) hLA
  have he : (eta.val+eta.val)+eta.val=eps.val := by
    have ht := divideRadius_identity eps (⟨3,by decide +kernel⟩ : QPos)
    change 3*eta.val=eps.val at ht
    grind only
  rw [he] at hs
  exact Small.congr (add_valid (add_valid (sub_valid X.property (Q n).property)
    (sub_valid (Q n).property L.property)) (sub_valid L.property A.property)) (sub_valid X.property A.property)
    (equiv_symm (SeriesLimitLaws.difference_via X.val A.val (Q n).val L.val X.property A.property (Q n).property L.property)) hs

theorem fixedRectangleDerivativeContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) :
    Converges (fixedRectangleDerivativeContour f J hdom b hb)
      (scalarProduct (hf.derivative b (hdom _ (rectanglePoleInterior_mem J b hb))) geometricPeriod) :=
  fixedRectangleDerivativeContour_converges_to f hf J hdom b hb _ (hf.atPoint _ _)

theorem fixedRectangleDerivativeContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (v : Scalar)
    (hv : Converges (fixedRectangleDerivativeContour f J hdom b hb) v) :
    v≈scalarProduct (hf.derivative b (hdom _ (rectanglePoleInterior_mem J b hb))) geometricPeriod :=
  converge_unique _ _ _ hv (fixedRectangleDerivativeContour_converges f hf J hdom b hb)

end ComputableAnalysis.RiemannHilbert.RectangularContour
