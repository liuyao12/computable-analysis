import ComputableAnalysis.RiemannHilbert.ContourDerivativeKernelBounds
import ComputableAnalysis.RiemannHilbert.ContourBoundaryScaling

/-! Supplied derivatives control actual rational difference quotients;
proved sequence laws then control the corresponding Cauchy quadratures. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

theorem converge_difference (p q : Nat → Scalar) (a b : Scalar) (hp : Converges p a) (hq : Converges q b) :
    Converges (fun n => gridScalarSub (p n) (q n)) (gridScalarSub a b) := by
  intro eps
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  obtain ⟨A,hA⟩ := hp eta
  obtain ⟨B,hB⟩ := hq eta
  refine ⟨max A B,?_⟩
  intro n hn
  have h := SeriesLimitLaws.difference_close (p n).val (q n).val a.val b.val
    (p n).property (q n).property a.property b.property eta.val eta.val (hA n (by omega)) (hB n (by omega))
  have he : eta.val+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at h
    grind only
  rw [he] at h
  exact h

theorem converge_rational_scale (r : Rat) (p : Nat → Scalar) (a : Scalar) (hp : Converges p a) :
    Converges (fun n => scale r (p n)) (scale r a) := by
  have h := converge_product_left (RationalDilation.unit r) p a hp
  exact converge_limit_congr _ _ _
    (converge_congr _ _ _ h (fun n => RationalDilation.product r (p n))) (RationalDilation.product r a)

def rationalFunctionQuotient (f : DomainFunctions.Map) (b : Scalar) (hb : f.domain b) (h : QPos)
    (hz : f.domain (rationalShift b h)) : Scalar :=
  scale (1/h.val) (gridScalarSub (f.eval (rationalShift b h) hz) (f.eval b hb))

theorem rationalQuotient_remainder (x y b d : Scalar) (h : QPos) :
    gridScalarSub (scale (1/h.val) (gridScalarSub x y)) d≈
      scale (1/h.val) (gridScalarSub (gridScalarSub x y) (scalarProduct d (gridScalarSub (rationalShift b h) b))) := by
  have hu : scale (1/h.val) (scalarProduct d (gridScalarSub (rationalShift b h) b))≈d :=
    Setoid.trans (b := scale (1/h.val) (scalarProduct d (realStep h))) (scaleRat_equiv (mul_equiv d.property d.property
      (sub_valid (rationalShift b h).property b.property) (realStep h).property
      (equiv_refl _ d.property) (rationalShift_difference b h))) (inverse_realStep_scaling d h)
  exact Setoid.trans (b := gridScalarSub (scale (1/h.val) (gridScalarSub x y))
    (scale (1/h.val) (scalarProduct d (gridScalarSub (rationalShift b h) b)))) (FunctionTheory.sub_congr (equiv_refl _ (scale (1/h.val) (gridScalarSub x y)).property)
    (equiv_symm hu)) (RationalDilation.difference (1/h.val) (gridScalarSub x y)
      (scalarProduct d (gridScalarSub (rationalShift b h) b)))

theorem rationalFunctionQuotient_error (f : DomainFunctions.Map) (b : Scalar) (hb : f.domain b)
    (d : Scalar) (hd : HasDerivativeAt f b hb d) (eps h : QPos)
    (hz : f.domain (rationalShift b h)) (hh : h.val≤(hd.delta eps).val) :
    Small (sub (rationalFunctionQuotient f b hb h hz).val d.val) eps.val := by
  have hr := hd.estimate eps h (rationalShift b h) hz hh (rationalShift_small b h)
  have hi : 0≤1/h.val := by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr h.property)
  have hs := LocalODE.small_scale hi hr
  rw [show (1/h.val)*(eps.val*h.val)=eps.val by
    have ht := Rat.div_mul_cancel (a := (1:Rat)) (Rat.ne_of_gt h.property); grind only] at hs
  exact Small.congr (scaleRat_valid (DomainFunctions.remainder_valid f b hb d (rationalShift b h) hz))
    (sub_valid (rationalFunctionQuotient f b hb h hz).property d.property)
    (equiv_symm (rationalQuotient_remainder (f.eval (rationalShift b h) hz) (f.eval b hb) b d h)) hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
