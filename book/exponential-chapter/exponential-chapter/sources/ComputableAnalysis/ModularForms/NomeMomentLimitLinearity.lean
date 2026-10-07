import ComputableAnalysis.ModularForms.NomeMomentHigherPrefixes

/-! Exact approximation-error transport for signed moment prefix combinations. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem represented_prefix_add_close (x y p q : Scalar) (e f : Rat)
    (hx : Small (sub x.val p.val) e) (hy : Small (sub y.val q.val) f) :
    Small (sub (add x.val y.val) (add p.val q.val)) (e+f) := by
  have h := LocalODE.small_add hx hy
  have he : (add (sub x.val p.val) (sub y.val q.val)).Equiv
      (sub (add x.val y.val) (add p.val q.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid x.property p.property) (sub_valid y.property q.property))
      (hright := sub_valid (add_valid x.property y.property) (add_valid p.property q.property))
    let X := ComplexRawQuotient.ofRaw x.val x.property
    let Y := ComplexRawQuotient.ofRaw y.val y.property
    let P := ComplexRawQuotient.ofRaw p.val p.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change (X-P)+(Y-Q)=(X+Y)-(P+Q)
    generalize X=x,Y=y,P=p,Q=q
    grind only
  exact Small.congr (add_valid (sub_valid x.property p.property) (sub_valid y.property q.property))
    (sub_valid (add_valid x.property y.property) (add_valid p.property q.property)) he h

theorem represented_prefix_sub_close (x y p q : Scalar) (e f : Rat)
    (hx : Small (sub x.val p.val) e) (hy : Small (sub y.val q.val) f) :
    Small (sub (sub x.val y.val) (sub p.val q.val)) (e+f) := by
  have h := SeriesLimitLaws.small_sub hx hy
  have he : (sub (sub x.val p.val) (sub y.val q.val)).Equiv
      (sub (sub x.val y.val) (sub p.val q.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid x.property p.property) (sub_valid y.property q.property))
      (hright := sub_valid (sub_valid x.property y.property) (sub_valid p.property q.property))
    let X := ComplexRawQuotient.ofRaw x.val x.property
    let Y := ComplexRawQuotient.ofRaw y.val y.property
    let P := ComplexRawQuotient.ofRaw p.val p.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change (X-P)-(Y-Q)=(X-Y)-(P-Q)
    generalize X=x,Y=y,P=p,Q=q
    grind only
  exact Small.congr (sub_valid (sub_valid x.property p.property) (sub_valid y.property q.property))
    (sub_valid (sub_valid x.property y.property) (sub_valid p.property q.property)) he h

theorem represented_prefix_scale_close (x p : Scalar) (c e : Rat) (hc : 0≤c)
    (hx : Small (sub x.val p.val) e) :
    Small (sub (scaleRat c x.val) (scaleRat c p.val)) (c*e) := by
  have h := LocalODE.small_scale hc hx
  have he : (scaleRat c (sub x.val p.val)).Equiv (sub (scaleRat c x.val) (scaleRat c p.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (sub_valid x.property p.property))
      (hright := sub_valid (scaleRat_valid x.property) (scaleRat_valid p.property))
    let X := ComplexRawQuotient.ofRaw x.val x.property
    let P := ComplexRawQuotient.ofRaw p.val p.property
    change ComplexRawQuotient.scaleRat c (X+ -P)=ComplexRawQuotient.scaleRat c X+ -ComplexRawQuotient.scaleRat c P
    rw [ComplexRawQuotient.scaleRat_add]
    have hn : ComplexRawQuotient.scaleRat c (-P)= -ComplexRawQuotient.scaleRat c P := by
      rw [ComplexRawQuotient.neg_eq_scaleRat_neg_one,ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.neg_scaleRat]
      congr 1
      grind only
    rw [hn]
  exact Small.congr (scaleRat_valid (sub_valid x.property p.property))
    (sub_valid (scaleRat_valid x.property) (scaleRat_valid p.property)) he h

end ComputableAnalysis.ModularForms
