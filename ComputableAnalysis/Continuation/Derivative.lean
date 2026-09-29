import ComputableAnalysis.Continuation.Germ
import ComputableAnalysis.Continuation.PolynomialIdentity

namespace ComputableAnalysis.FunctionTheory
open ComplexRaw Continuation

theorem Small.neg {z : ComplexRaw} {r : Rat} (h : Small z r) : Small (neg z) r := by
  rcases h with ⟨h1,h2,h3,h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n m
  · exact Rat.neg_le_neg (h2 m n)
  · have k := h1 m n
    change -r ≤ (z.compute n).hi.re at k
    change -(z.compute n).hi.re ≤ r
    grind
  · exact Rat.neg_le_neg (h4 m n)
  · have k := h3 m n
    change -r ≤ (z.compute n).hi.im at k
    change -(z.compute n).hi.im ≤ r
    grind

theorem Small.sub {z w : ComplexRaw} {r s : Rat}
    (h : Small z r) (k : Small w s) : Small (sub z w) (r+s) := h.add k.neg

theorem Small.of_scale_pos {z : ComplexRaw} {r H : Rat} (hH : 0 < H)
    (h : Small (scaleRat H z) (r*H)) : Small z r := by
  have hH0 := Rat.le_of_lt hH
  rcases h with ⟨h1,h2,h3,h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n m
  · have h := h1 n m
    change -(r*H) ≤ (QBox.scaleRat H (z.compute m)).hi.re at h
    simp only [QBox.scaleRat, if_pos hH0] at h
    change -r ≤ (z.compute m).hi.re
    apply Rat.le_of_mul_le_mul_left (c := H) _ hH
    grind
  · have h := h2 n m
    change (QBox.scaleRat H (z.compute n)).lo.re ≤ r*H at h
    simp only [QBox.scaleRat, if_pos hH0] at h
    change (z.compute n).lo.re ≤ r
    apply Rat.le_of_mul_le_mul_left (c := H) _ hH
    grind
  · have h := h3 n m
    change -(r*H) ≤ (QBox.scaleRat H (z.compute m)).hi.im at h
    simp only [QBox.scaleRat, if_pos hH0] at h
    change -r ≤ (z.compute m).hi.im
    apply Rat.le_of_mul_le_mul_left (c := H) _ hH
    grind
  · have h := h4 n m
    change (QBox.scaleRat H (z.compute n)).lo.im ≤ r*H at h
    simp only [QBox.scaleRat, if_pos hH0] at h
    change (z.compute n).lo.im ≤ r
    apply Rat.le_of_mul_le_mul_left (c := H) _ hH
    grind

private theorem le_zero_of_all (x : Rat) (h : ∀ r : QPos, x ≤ r.val) : x ≤ 0 := by
  by_cases hn : x ≤ 0
  · exact hn
  apply False.elim
  have hx : 0 < x := by grind
  have hh := h ⟨x/2, by grind⟩
  change x ≤ x/2 at hh
  grind

/-- Arbitrarily small exact coordinate differences imply equality of values. -/
theorem equiv_of_small_sub {a b : ComplexRaw}
    (h : ∀ r : QPos, Small (sub a b) r.val) : a.Equiv b := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have hr1 := le_zero_of_all ((a.compute n).lo.re - (b.compute n).hi.re)
    (fun r => by have k := (h r).2.1 n n; simpa only [sub,add,neg,realPart,imagPart,RealRaw.ofRat,QBox.add,QBox.neg,QComplex.add,QComplex.neg,Rat.sub_eq_add_neg] using k)
  have hi1 := le_zero_of_all ((a.compute n).lo.im - (b.compute n).hi.im)
    (fun r => by have k := (h r).2.2.2 n n; simpa only [sub,add,neg,realPart,imagPart,RealRaw.ofRat,QBox.add,QBox.neg,QComplex.add,QComplex.neg,Rat.sub_eq_add_neg] using k)
  have hr2 := le_zero_of_all ((b.compute n).lo.re - (a.compute n).hi.re)
    (fun r => by have k := (h r).sub_symm.2.1 n n; simpa only [sub,add,neg,realPart,imagPart,RealRaw.ofRat,QBox.add,QBox.neg,QComplex.add,QComplex.neg,Rat.sub_eq_add_neg] using k)
  have hi2 := le_zero_of_all ((b.compute n).lo.im - (a.compute n).hi.im)
    (fun r => by have k := (h r).sub_symm.2.2.2 n n; simpa only [sub,add,neg,realPart,imagPart,RealRaw.ofRat,QBox.add,QBox.neg,QComplex.add,QComplex.neg,Rat.sub_eq_add_neg] using k)
  change (_ ≤ _ ∧ _ ≤ _) ∧ (_ ≤ _ ∧ _ ≤ _)
  constructor <;> constructor <;> grind

private theorem shifted_displacement (a : ComplexRaw) (ha : a.Valid) (H : Rat) :
    (sub (add a (ofQComplex ⟨H,0⟩)) a).Equiv (ofQComplex ⟨H,0⟩) := by
  let A : PolynomialExpr := .var 0
  exact PolynomialExpr.identity (.add (.add A (.lit ⟨H,0⟩)) (.neg A)) (.lit ⟨H,0⟩)
    (fun _ => a) (fun _ => ha) (by
      intro p
      simp only [A, PolynomialExpr.rational, QComplex.add, QComplex.neg, QComplex.mk.injEq]
      constructor <;> grind)

private theorem remainder_difference (f : Map) (a d e : ComplexRaw)
    (ha : a.Valid) (hd : d.Valid) (he : e.Valid) (hfa : f.domain a)
    (H : Rat) (hfz : f.domain (add a (ofQComplex ⟨H,0⟩))) :
    (sub (remainder f a d (add a (ofQComplex ⟨H,0⟩)))
      (remainder f a e (add a (ofQComplex ⟨H,0⟩)))).Equiv
      (scaleRat H (sub e d)) := by
  let z := add a (ofQComplex ⟨H,0⟩)
  let v : Nat → ComplexRaw := fun n =>
    if n=0 then a else if n=1 then d else if n=2 then e else if n=3 then f.eval a else f.eval z
  have hv : ∀ n, (v n).Valid := by
    intro n
    dsimp [v]
    split
    · exact ha
    · split
      · exact hd
      · split
        · exact he
        · split
          · exact f.valid a ha hfa
          · exact f.valid z (add_valid ha (ofQComplex_valid _)) hfz
  let A : PolynomialExpr := .var 0
  let D : PolynomialExpr := .var 1
  let E : PolynomialExpr := .var 2
  let B : PolynomialExpr := .add (.var 4) (.neg (.var 3))
  let Z : PolynomialExpr := .add (.add A (.lit ⟨H,0⟩)) (.neg A)
  exact PolynomialExpr.identity
    (.add (.add B (.neg (.mul D Z))) (.neg (.add B (.neg (.mul E Z)))))
    (.scale H (.add E (.neg D))) v hv (by
      intro p
      simp only [A,D,E,B,Z,PolynomialExpr.rational,QComplex.add,QComplex.neg,
        QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
      constructor <;> grind)

/-- Complex derivatives are unique at every represented point of an open
domain. The proof tests an arbitrarily small rational real displacement;
the derivative definition already controls every complex displacement. -/
theorem HasDerivativeAt.unique {f : Map} (o : OpenDomain f) {a d e : ComplexRaw}
    (hd : HasDerivativeAt f a d) (he : HasDerivativeAt f a e) : d.Equiv e := by
  apply equiv_symm
  apply equiv_of_small_sub
  intro eps
  let eta : QPos := ⟨eps.val/2, by have := eps.property; grind⟩
  let rho := o.radius a hd.point_valid hd.point_mem
  let H : QPos := ⟨min rho.val (min (hd.delta eta).val (he.delta eta).val), by
    have := rho.property; have := (hd.delta eta).property; have := (he.delta eta).property
    grind⟩
  let z := add a (ofQComplex ⟨H.val,0⟩)
  have hz : z.Valid := add_valid hd.point_valid (ofQComplex_valid _)
  have hshift : Small (ofQComplex ⟨H.val,0⟩) H.val := by
    have hp := H.property
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n m <;> change _ ≤ _ <;> dsimp [ofQComplex,realPart,imagPart,QBox.point] <;> grind
  have hza : Small (sub z a) H.val :=
    Small.congr (ofQComplex_valid _) (sub_valid hz hd.point_valid)
      (equiv_symm (shifted_displacement a hd.point_valid H.val)) hshift
  have hfz := o.inside a hd.point_valid hd.point_mem z hz (hza.mono (by dsimp [H]; grind))
  have h1 := hd.estimate eta H z hz hfz (by dsimp [H]; grind) hza
  have h2 := he.estimate eta H z hz hfz (by dsimp [H]; grind) hza
  have hb := h1.sub h2
  have hh : Small (scaleRat H.val (sub e d)) (eps.val*H.val) := by
    apply Small.congr
      (sub_valid (remainder_valid f hd.point_valid hd.derivative_valid hz hd.point_mem hfz)
        (remainder_valid f he.point_valid he.derivative_valid hz he.point_mem hfz))
      (scaleRat_valid_of_nonneg (Rat.le_of_lt H.property) (sub_valid he.derivative_valid hd.derivative_valid))
      (remainder_difference f a d e hd.point_valid hd.derivative_valid he.derivative_valid hd.point_mem H.val hfz)
    exact hb.mono (by dsimp [eta]; grind)
  exact Small.of_scale_pos H.property hh


/-- Transfer a derivative across an explicitly supplied neighborhood equality.
The radius is data, so the new derivative modulus remains executable. -/
def HasDerivativeAt.congrMap {f g : Map} {a d : ComplexRaw}
    (h : HasDerivativeAt f a d) (r : QPos)
    (agree : ∀ z, z.Valid → Small (sub z a) r.val →
      f.domain z ∧ g.domain z ∧ (f.eval z).Equiv (g.eval z)) :
    HasDerivativeAt g a d where
  point_valid := h.point_valid
  point_mem := (agree a h.point_valid
    (Small.sub_self a h.point_valid (Rat.le_of_lt r.property))).2.1
  derivative_valid := h.derivative_valid
  delta := fun eps => ⟨min (h.delta eps).val r.val, by
    have := (h.delta eps).property; have := r.property; grind⟩
  estimate := by
    intro eps H z hz _ hH hza
    have hzBound : H.val ≤ r.val := by change H.val ≤ min _ _ at hH; grind
    have haPair := agree a h.point_valid
      (Small.sub_self a h.point_valid (Rat.le_of_lt r.property))
    have hzPair := agree z hz (hza.mono hzBound)
    have old := h.estimate eps H z hz hzPair.1 (by change H.val ≤ min _ _ at hH; grind) hza
    apply Small.congr
      (remainder_valid f h.point_valid h.derivative_valid hz h.point_mem hzPair.1)
      (remainder_valid g h.point_valid h.derivative_valid hz haPair.2.1 hzPair.2.1) _ old
    exact FunctionTheory.sub_congr (FunctionTheory.sub_congr hzPair.2.2 haPair.2.2)
      (equiv_refl _ (mul_valid h.derivative_valid (sub_valid hz h.point_valid)))

/-- Neighborhood equality determines the derivative, even when the two maps
have different domains and different computational representatives. -/
theorem derivative_eq_of_agreeAt {a : Continuation.Point} {f g : Map}
    (og : OpenDomain g) {d e : ComplexRaw}
    (hd : HasDerivativeAt f a.val d) (he : HasDerivativeAt g a.val e)
    (h : Continuation.AgreeAt a f g) : d.Equiv e := by
  obtain ⟨r,hr⟩ := h
  exact (hd.congrMap r hr).unique og he

end ComputableAnalysis.FunctionTheory
