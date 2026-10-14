import ComputableAnalysis.RiemannHilbert.ContourMomentMajorants
import ComputableAnalysis.RiemannHilbert.GeneralSeries

/-! The finite Taylor identity for the actual represented Cauchy kernels.
The shifted inverse bound and the remainder are proved from inverse laws,
not supplied by a reconstruction certificate. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

/-- Pole variation for arbitrary represented displacements. -/
theorem ribbonPoleOffset_pole_difference (b z w : Scalar) :
    gridScalarSub ((ribbonPoleOffset z).eval w trivial) ((ribbonPoleOffset b).eval w trivial)≈
      scalarNeg (Centered.offset b z) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSub ((ribbonPoleOffset z).eval w trivial) ((ribbonPoleOffset b).eval w trivial)).property)
    (hright := (scalarNeg (Centered.offset b z)).property)
  change (-gridScalarValue z+1*gridScalarValue w)-(-gridScalarValue b+1*gridScalarValue w)=
    -(gridScalarValue z-gridScalarValue b)
  grind only

theorem ribbonPoleReciprocal_near_bound (b z w : Scalar)
    (hb : (ribbonPoleReciprocal b).domain w) (hz : (ribbonPoleReciprocal z).domain w)
    (U H : Rat) (hU : 0≤U) (hH : 0≤H)
    (hr : Small ((ribbonPoleReciprocal b).eval w hb).val U)
    (hh : Small (Centered.offset b z).val H) (hbudget : 16*U*H≤1) :
    Small ((ribbonPoleReciprocal z).eval w hz).val (8*U) := by
  have hdiff : Small (sub ((ribbonPoleOffset z).eval w trivial).val
      ((ribbonPoleOffset b).eval w trivial).val) H :=
    Small.congr (scalarNeg (Centered.offset b z)).property
      (sub_valid ((ribbonPoleOffset z).eval w trivial).property ((ribbonPoleOffset b).eval w trivial).property)
      (equiv_symm (ribbonPoleOffset_pole_difference b z w)) (SeriesLimitLaws.small_neg hh)
  obtain ⟨hn,hs⟩ := inverse_near_exists_bound ((ribbonPoleOffset b).eval w trivial)
    ((ribbonPoleOffset z).eval w trivial) (compose_outer_mem hb) U H hU hH hr hdiff hbudget
  exact hs

theorem ribbonPoleReciprocal_resolvent (b z w : Scalar)
    (hb : (ribbonPoleReciprocal b).domain w) (hz : (ribbonPoleReciprocal z).domain w) :
    gridScalarSub ((ribbonPoleReciprocal z).eval w hz) ((ribbonPoleReciprocal b).eval w hb)≈
      scalarProduct (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb))
        ((ribbonPoleReciprocal z).eval w hz) := by
  let a := (ribbonPoleOffset b).eval w trivial
  let c := (ribbonPoleOffset z).eval w trivial
  let R := gridScalarValue ((ribbonPoleReciprocal b).eval w hb)
  let S := gridScalarValue ((ribbonPoleReciprocal z).eval w hz)
  let A := gridScalarValue a
  let C := gridScalarValue c
  let H := gridScalarValue (Centered.offset b z)
  have hA := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid a.property ((ribbonPoleReciprocal b).eval w hb).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse a (compose_outer_mem hb))
  have hC := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid c.property ((ribbonPoleReciprocal z).eval w hz).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse c (compose_outer_mem hz))
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (gridScalarSub c a).property) (hright := (scalarNeg (Centered.offset b z)).property)
    (ribbonPoleOffset_pole_difference b z w)
  change A*R=1 at hA
  change C*S=1 at hC
  change C-A= -H at hd
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSub ((ribbonPoleReciprocal z).eval w hz) ((ribbonPoleReciprocal b).eval w hb)).property)
    (hright := (scalarProduct (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb))
      ((ribbonPoleReciprocal z).eval w hz)).property)
  change S-R=(H*R)*S
  grind only

theorem ribbonCauchyPowerValue_formula (f : DomainFunctions.Map) (b w : Scalar)
    (hw : (ribbonCauchyKernel f b).domain w) (m : Nat) :
    gridScalarValue (ribbonCauchyPowerValue f b w hw m)=
      gridScalarValue (f.eval w hw.1)*gridScalarValue ((ribbonPoleReciprocal b).eval w hw.2)^m := by
  induction m with
  | zero => change _=_*1; exact (ComplexRawQuotient.mul_one _).symm
  | succ m ih =>
    change gridScalarValue (ribbonCauchyPowerValue f b w hw m)*gridScalarValue ((ribbonPoleReciprocal b).eval w hw.2)=_
    rw [ih]; change (gridScalarValue (f.eval w hw.1)*gridScalarValue ((ribbonPoleReciprocal b).eval w hw.2)^m)*gridScalarValue ((ribbonPoleReciprocal b).eval w hw.2)=gridScalarValue (f.eval w hw.1)*(gridScalarValue ((ribbonPoleReciprocal b).eval w hw.2)^m*gridScalarValue ((ribbonPoleReciprocal b).eval w hw.2)); grind only

private theorem product_power (x y : ScalarAlgebra.Value) (n : Nat) : (x*y)^n=x^n*y^n := by
  induction n with
  | zero => change 1=1*1; grind only
  | succ n ih => change (x*y)^n*(x*y)=(x^n*x)*(y^n*y); rw [ih]; grind only

def cauchyTaylorKernelPrefix (f : DomainFunctions.Map) (b z w : Scalar)
    (hw : (ribbonCauchyKernel f b).domain w) (N : Nat) : Scalar :=
  gridScalarSum N (fun k => scalarProduct (ribbonCauchyPowerValue f b w hw (k+1))
    ⟨LocalODE.power (Centered.offset b z).val k,LocalODE.power_valid _ (Centered.offset b z).property k⟩)

/-- Exact finite kernel identity for any represented center and evaluation point. -/
theorem cauchyTaylorKernel_remainder (f : DomainFunctions.Map) (b z w : Scalar)
    (hb : (ribbonCauchyKernel f b).domain w) (hz : (ribbonCauchyKernel f z).domain w) (N : Nat) :
    gridScalarSub ((ribbonCauchyKernel f z).eval w hz) (cauchyTaylorKernelPrefix f b z w hb N)≈
      scalarProduct
        ⟨LocalODE.power (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb.2)).val N,
          LocalODE.power_valid _ (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb.2)).property N⟩
        ((ribbonCauchyKernel f z).eval w hz) := by
  let V := gridScalarValue (f.eval w hb.1)
  let H := gridScalarValue (Centered.offset b z)
  let R := gridScalarValue ((ribbonPoleReciprocal b).eval w hb.2)
  let S := gridScalarValue ((ribbonPoleReciprocal z).eval w hz.2)
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (gridScalarSub ((ribbonPoleReciprocal z).eval w hz.2) ((ribbonPoleReciprocal b).eval w hb.2)).property)
    (hright := (scalarProduct (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb.2))
      ((ribbonPoleReciprocal z).eval w hz.2)).property)
    (ribbonPoleReciprocal_resolvent b z w hb.2 hz.2)
  change S-R=H*R*S at hr
  have hprefix (n : Nat) : gridScalarValue (cauchyTaylorKernelPrefix f b z w hb n)=
      gridValueSum n (fun k => V*R^(k+1)*H^k) := by
    unfold cauchyTaylorKernelPrefix
    rw [gridScalarSum_value]
    congr 1
    funext k
    change gridScalarValue (ribbonCauchyPowerValue f b w hb (k+1))*
      ComplexRawQuotient.ofRaw (LocalODE.power (Centered.offset b z).val k) (LocalODE.power_valid _ (Centered.offset b z).property k)=V*R^(k+1)*H^k
    rw [ribbonCauchyPowerValue_formula,ScalarAlgebra.ofRaw_power (Centered.offset b z).val (Centered.offset b z).property k]
    rfl
  have hfinite (n : Nat) : V*S-gridValueSum n (fun k => V*R^(k+1)*H^k)=(H*R)^n*(V*S) := by
    induction n with
    | zero => change V*S-0=1*(V*S); grind only
    | succ n ih =>
      change V*S-(gridValueSum n (fun k => V*R^(k+1)*H^k)+V*(R^n*R)*H^n)=
        ((H*R)^n*(H*R))*(V*S)
      have hp := product_power H R n
      grind only
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSub ((ribbonCauchyKernel f z).eval w hz) (cauchyTaylorKernelPrefix f b z w hb N)).property)
    (hright := (scalarProduct
      ⟨LocalODE.power (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb.2)).val N,
        LocalODE.power_valid _ (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb.2)).property N⟩
      ((ribbonCauchyKernel f z).eval w hz)).property)
  change V*S-gridScalarValue (cauchyTaylorKernelPrefix f b z w hb N)=
    ComplexRawQuotient.ofRaw (LocalODE.power (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb.2)).val N)
      (LocalODE.power_valid _ (scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb.2)).property N)*(V*S)
  rw [hprefix,ScalarAlgebra.ofRaw_power]
  exact hfinite N

theorem cauchyTaylorKernel_remainder_bound (f : DomainFunctions.Map) (b z w : Scalar)
    (hb : (ribbonCauchyKernel f b).domain w) (hz : (ribbonCauchyKernel f z).domain w)
    (F U H : QPos) (hv : Small (f.eval w hb.1).val F.val)
    (hr : Small ((ribbonPoleReciprocal b).eval w hb.2).val U.val)
    (hh : Small (Centered.offset b z).val H.val) (hbudget : 16*U.val*H.val≤1) (N : Nat) :
    Small (sub ((ribbonCauchyKernel f z).eval w hz).val (cauchyTaylorKernelPrefix f b z w hb N).val)
      (32*F.val*U.val*(4*H.val*U.val)^N) := by
  have hs := ribbonPoleReciprocal_near_bound b z w hb.2 hz.2 U.val H.val
    (Rat.le_of_lt U.property) (Rat.le_of_lt H.property) hr hh hbudget
  have hprod := Small.mul (f.eval w hz.1).property ((ribbonPoleReciprocal z).eval w hz.2).property
    (Rat.le_of_lt F.property) (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) U.property)) hv hs
  let u := scalarProduct (Centered.offset b z) ((ribbonPoleReciprocal b).eval w hb.2)
  have hu := Small.mul (Centered.offset b z).property ((ribbonPoleReciprocal b).eval w hb.2).property
    (Rat.le_of_lt H.property) (Rat.le_of_lt U.property) hh hr
  have hpow := LocalODE.power_small u.val u.property (2*H.val*U.val)
    (Rat.le_of_lt (Rat.mul_pos (Rat.mul_pos (by decide +kernel) H.property) U.property)) hu N
  have hm := Small.mul (LocalODE.power_valid u.val u.property N) ((ribbonCauchyKernel f z).eval w hz).property
    (Rat.pow_nonneg (Rat.le_of_lt (Rat.mul_pos (by decide +kernel)
      (Rat.mul_pos (Rat.mul_pos (by decide +kernel) H.property) U.property))))
    (Rat.le_of_lt (Rat.mul_pos (Rat.mul_pos (by decide +kernel) F.property)
      (Rat.mul_pos (by decide +kernel) U.property))) hpow hprod
  have he : 2*(2*(2*H.val*U.val))^N*(2*F.val*(8*U.val))=32*F.val*U.val*(4*H.val*U.val)^N := by
    rw [show 2*(2*H.val*U.val)=4*H.val*U.val by grind only]; grind only
  rw [he] at hm
  exact Small.congr
    (mul_valid (LocalODE.power_valid u.val u.property N) ((ribbonCauchyKernel f z).eval w hz).property)
    (sub_valid ((ribbonCauchyKernel f z).eval w hz).property (cauchyTaylorKernelPrefix f b z w hb N).property)
    (equiv_symm (cauchyTaylorKernel_remainder f b z w hb hz N)) hm

end ComputableAnalysis.RiemannHilbert.RectangularContour
