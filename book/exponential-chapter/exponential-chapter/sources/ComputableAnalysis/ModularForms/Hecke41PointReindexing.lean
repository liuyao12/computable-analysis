import ComputableAnalysis.ModularForms.Hecke41PointEquations

/-! Transport of degree-41 matrix reindexing to actual represented points. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

private theorem reindex_algebra
    (ai bi di aj bj dj ag bg cg dg ah bh ch dh Z Y V W R Ri Rj : ScalarAlgebra.Value)
    (hg : (cg*Z+dg)*Y=ag*Z+bg) (hi : di*V=ai*Y+bi) (hj : dj*W=aj*Z+bj)
    (hu : (cg*Z+dg)*R=1) (hui : di*Ri=1) (huj : dj*Rj=1)
    (ha : ai*ag+bi*cg=ah*aj) (hb : ai*bg+bi*dg=ah*bj+bh*dj)
    (hc : di*cg=ch*aj) (hd : di*dg=ch*bj+dh*dj) :
    (ch*W+dh)*V=ah*W+bh := by
  have hden : dj*(ch*W+dh)=di*(cg*Z+dg) := by
    clear hg hi hu hui huj ha hb
    grind only
  have hnum : di*(cg*Z+dg)*V=ai*(ag*Z+bg)+bi*(cg*Z+dg) := by
    clear hj hu hui huj ha hb hc hd hden
    grind only
  have hpoly : ai*(ag*Z+bg)+bi*(cg*Z+dg)=dj*(ah*W+bh) := by
    clear hg hi hu hui huj hc hd hden hnum
    grind only
  have he : dj*((ch*W+dh)*V-(ah*W+bh))=0 := by
    clear hg hi hj hu hui huj ha hb hc hd
    grind only
  have hm := congrArg (fun X : ScalarAlgebra.Value => Rj*X) he
  clear hg hi hj hu hui ha hb hc hd hden hnum hpoly he
  grind only

private def denominatorReciprocal (i : Fin 42) : ScalarAlgebra.Value :=
  if i.val=41 then 1 else ComplexRawQuotient.scaleRat (1/41) 1

private theorem denominator_unit (i : Fin 42) :
    ((hecke41Representative i).d:ScalarAlgebra.Value)*denominatorReciprocal i=1 := by
  by_cases hi : i.val=41
  · simp only [hecke41Representative,denominatorReciprocal,if_pos hi]
    grind
  · simp only [hecke41Representative,denominatorReciprocal,if_neg hi]
    have h : (41:ScalarAlgebra.Value)*ComplexRawQuotient.scaleRat (1/41) 1=1 := by
      have hs := ScalarAlgebra.scale_natural 41 (ComplexRawQuotient.scaleRat (1/41) 1)
      rw [show ((41:Nat):Rat)=(41:Rat) by decide +kernel,ComplexRawQuotient.scaleRat_scaleRat,
        show (41:Rat)*(1/41)=1 by decide +kernel,ComplexRawQuotient.scaleRat_one] at hs
      grind
    grind

/-- Any checked triangular representative factorization transports to an exact actual-point identity. -/
theorem hecke41Point_reindex (i j : Fin 42) (g h : SL2Z)
    (hm : CorrespondenceMatrix.multiply (hecke41Representative i) (CorrespondenceMatrix.ofSL2Z g)=
      CorrespondenceMatrix.multiply (CorrespondenceMatrix.ofSL2Z h) (hecke41Representative j))
    (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (fractionalLinear h (hecke41Point j z) (hecke41Point_upper j z hz)).val.Equiv
      (hecke41Point i (fractionalLinear g z hz)).val := by
  let y := fractionalLinear g z hz
  let v := hecke41Point i y
  let w := hecke41Point j z
  let d : Scalar := ⟨integerAffine g.c g.d z.val,integerAffine_valid _ _ z.property⟩
  let r := RepresentedReciprocal.inverse d (denominator_nonzero g z hz)
  have hg := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid d.property y.property) (hright := integerAffine_valid _ _ z.property)
    (fractionalLinear_cancel g z hz)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (integerAffine_valid _ _ y.property) v.property)
    (hright := integerAffine_valid _ _ y.property) (hecke41Point_matrix_equation i y)
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (integerAffine_valid _ _ z.property) w.property)
    (hright := integerAffine_valid _ _ z.property) (hecke41Point_matrix_equation j z)
  have hu := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid d.property r.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse d (denominator_nonzero g z hz))
  apply fractionalLinear_unique h w (hecke41Point_upper j z hz) v
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (integerAffine_valid _ _ w.property) v.property)
    (hright := integerAffine_valid _ _ w.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  let V := ComplexRawQuotient.ofRaw v.val v.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let R := ComplexRawQuotient.ofRaw r.val r.property
  have hci := (hecke41Representative_denominator i).1
  have hcj := (hecke41Representative_denominator j).1
  change ComplexRawQuotient.ofRaw (integerAffine g.c g.d z.val) (integerAffine_valid _ _ z.property)*Y=
    ComplexRawQuotient.ofRaw (integerAffine g.a g.b z.val) (integerAffine_valid _ _ z.property) at hg
  change ComplexRawQuotient.ofRaw (integerAffine (hecke41Representative i).c (hecke41Representative i).d y.val)
    (integerAffine_valid _ _ y.property)*V=
    ComplexRawQuotient.ofRaw (integerAffine (hecke41Representative i).a (hecke41Representative i).b y.val)
      (integerAffine_valid _ _ y.property) at hi
  change ComplexRawQuotient.ofRaw (integerAffine (hecke41Representative j).c (hecke41Representative j).d z.val)
    (integerAffine_valid _ _ z.property)*W=
    ComplexRawQuotient.ofRaw (integerAffine (hecke41Representative j).a (hecke41Representative j).b z.val)
      (integerAffine_valid _ _ z.property) at hj
  change ComplexRawQuotient.ofRaw (integerAffine g.c g.d z.val) (integerAffine_valid _ _ z.property)*R=1 at hu
  simp only [integerAffine_class,hci,hcj] at hg hi hj hu
  change ComplexRawQuotient.ofRaw (integerAffine h.c h.d w.val) (integerAffine_valid _ _ w.property)*V=
    ComplexRawQuotient.ofRaw (integerAffine h.a h.b w.val) (integerAffine_valid _ _ w.property)
  simp only [integerAffine_class]
  have ha := congrArg CorrespondenceMatrix.a hm
  have hb := congrArg CorrespondenceMatrix.b hm
  have hc := congrArg CorrespondenceMatrix.c hm
  have hd := congrArg CorrespondenceMatrix.d hm
  simp only [CorrespondenceMatrix.multiply,CorrespondenceMatrix.ofSL2Z,hci,hcj] at ha hb hc hd
  have hva := congrArg (fun n : Int => (n:ScalarAlgebra.Value)) ha
  have hvb := congrArg (fun n : Int => (n:ScalarAlgebra.Value)) hb
  have hvc := congrArg (fun n : Int => (n:ScalarAlgebra.Value)) hc
  have hvd := congrArg (fun n : Int => (n:ScalarAlgebra.Value)) hd
  have hunit_i := denominator_unit i
  have hunit_j := denominator_unit j
  have hzero : ((0:Int):ScalarAlgebra.Value)=0 := by grind
  rw [hzero] at hi hj
  have hi' : ((hecke41Representative i).d:ScalarAlgebra.Value)*V=
      ((hecke41Representative i).a:ScalarAlgebra.Value)*Y+((hecke41Representative i).b:ScalarAlgebra.Value) := by
    clear hm hg hj hu ha hb hc hd hva hvb hvc hvd hunit_i hunit_j
    grind only
  have hj' : ((hecke41Representative j).d:ScalarAlgebra.Value)*W=
      ((hecke41Representative j).a:ScalarAlgebra.Value)*Z+((hecke41Representative j).b:ScalarAlgebra.Value) := by
    clear hm hg hi hi' hu ha hb hc hd hva hvb hvc hvd hunit_i hunit_j
    grind only
  apply reindex_algebra
    ((hecke41Representative i).a:ScalarAlgebra.Value) ((hecke41Representative i).b:ScalarAlgebra.Value)
    ((hecke41Representative i).d:ScalarAlgebra.Value)
    ((hecke41Representative j).a:ScalarAlgebra.Value) ((hecke41Representative j).b:ScalarAlgebra.Value)
    ((hecke41Representative j).d:ScalarAlgebra.Value)
    (g.a:ScalarAlgebra.Value) (g.b:ScalarAlgebra.Value) (g.c:ScalarAlgebra.Value) (g.d:ScalarAlgebra.Value)
    (h.a:ScalarAlgebra.Value) (h.b:ScalarAlgebra.Value) (h.c:ScalarAlgebra.Value) (h.d:ScalarAlgebra.Value)
    Z Y V W R (denominatorReciprocal i) (denominatorReciprocal j)
  · exact hg
  · exact hi'
  · exact hj'
  · exact hu
  · exact hunit_i
  · exact hunit_j
  all_goals grind

/-- The checked S permutation reindexes the actual degree-41 represented points. -/
theorem hecke41Point_S_reindex (i : Fin 42) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (fractionalLinear (hecke41SWitness i) (hecke41Point (hecke41SIndex i) z)
      (hecke41Point_upper (hecke41SIndex i) z hz)).val.Equiv
      (hecke41Point i (fractionalLinear SL2Z.S z hz)).val :=
  hecke41Point_reindex i (hecke41SIndex i) SL2Z.S (hecke41SWitness i) (hecke41S_reindex i) z hz

/-- The checked T permutation reindexes the actual degree-41 represented points. -/
theorem hecke41Point_T_reindex (i : Fin 42) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (fractionalLinear (hecke41TWitness i) (hecke41Point (hecke41TIndex i) z)
      (hecke41Point_upper (hecke41TIndex i) z hz)).val.Equiv
      (hecke41Point i (fractionalLinear SL2Z.T z hz)).val :=
  hecke41Point_reindex i (hecke41TIndex i) SL2Z.T (hecke41TWitness i) (hecke41T_reindex i) z hz

/-- A justified j domain transports along an actual correspondence reindexing identity. -/
theorem hecke41Point_reindex_j_domain (i j : Fin 42) (g h : SL2Z)
    (hm : CorrespondenceMatrix.multiply (hecke41Representative i) (CorrespondenceMatrix.ofSL2Z g)=
      CorrespondenceMatrix.multiply (CorrespondenceMatrix.ofSL2Z h) (hecke41Representative j))
    (z : Scalar) (hz : InUpperHalfPlane z.val) (hj : latticeJMap.domain (hecke41Point j z)) :
    latticeJMap.domain (hecke41Point i (fractionalLinear g z hz)) := by
  have he := hecke41Point_reindex i j g h hm z hz
  exact (latticeJMap.domain_congr
    (fractionalLinear h (hecke41Point j z) (hecke41Point_upper j z hz))
    (hecke41Point i (fractionalLinear g z hz)) he).mp (latticeJMap_action_mem h (hecke41Point j z) hj)

/-- Actual j values agree at reindexed correspondence points on their justified domains. -/
theorem hecke41Point_reindex_j (i j : Fin 42) (g h : SL2Z)
    (hm : CorrespondenceMatrix.multiply (hecke41Representative i) (CorrespondenceMatrix.ofSL2Z g)=
      CorrespondenceMatrix.multiply (CorrespondenceMatrix.ofSL2Z h) (hecke41Representative j))
    (z : Scalar) (hz : InUpperHalfPlane z.val) (hj : latticeJMap.domain (hecke41Point j z)) :
    (latticeJMap.eval (hecke41Point i (fractionalLinear g z hz))
      (hecke41Point_reindex_j_domain i j g h hm z hz hj)).val.Equiv
      (latticeJMap.eval (hecke41Point j z) hj).val := by
  let w := fractionalLinear h (hecke41Point j z) (hecke41Point_upper j z hz)
  let v := hecke41Point i (fractionalLinear g z hz)
  have hw := latticeJMap_action_mem h (hecke41Point j z) hj
  have hv := hecke41Point_reindex_j_domain i j g h hm z hz hj
  have he := latticeJMap.eval_congr w v hw hv (hecke41Point_reindex i j g h hm z hz)
  exact equiv_trans (latticeJMap.eval v hv).property (latticeJMap.eval w hw).property
    (latticeJMap.eval (hecke41Point j z) hj).property (equiv_symm he)
    (latticeJMap_invariant h (hecke41Point j z) hj)

end ComputableAnalysis.ModularForms
