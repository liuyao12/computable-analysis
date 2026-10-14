import ComputableAnalysis.ElementaryArctangentBranch

/-! Exact rational circle identities for the constructed inverse angle. -/
namespace ComputableAnalysis.ElementaryAngleAlgebra
open ComplexRaw RiemannHilbert FunctionTheory ModularForms
open ElementaryInverseBranches ElementaryArctangentBranch
set_option maxHeartbeats 2000000

theorem parts (f : ComplexRaw) (hf : f.Valid) :
    f.Equiv (add (ofRealRaw f.realPart) (imaginaryAxis f.imagPart)) := by
  intro n
  let p := (f.compute n).center
  have hp := QBox.center_mem (valid_ordered hf n)
  have ha : ((add (ofRealRaw f.realPart) (imaginaryAxis f.imagPart)).compute n).lo ≤ p ∧
      p ≤ ((add (ofRealRaw f.realPart) (imaginaryAxis f.imagPart)).compute n).hi := by
    simpa only [add,ofRealRaw,imaginaryAxis,mulI,realPart,imagPart,QBox.add,QComplex.add,
      Rat.zero_add,Rat.add_zero,Rat.neg_zero] using hp
  exact (compareAt_overlap_iff _ _ n n).mpr (QBox.overlaps_of_common_point hp ha)

theorem realVector_product (r : Rat) (c : RealRaw) (hc : c.Valid) :
    (add (ofRealRaw c) (imaginaryAxis (RealRaw.scaleRat r c))).Equiv
      (mul (ofQComplex ⟨1,r⟩) (ofRealRaw c)) := by
  intro n
  let p : QComplex := ⟨(c.compute n).midpoint,0⟩
  have hp := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _ hc n)
  have hpc : ((ofRealRaw c).compute n).lo ≤ p ∧ p ≤ ((ofRealRaw c).compute n).hi :=
    ⟨⟨hp.1,Rat.le_refl⟩,⟨hp.2,Rat.le_refl⟩⟩
  have hm := QBox.mul_contains (A := QBox.point ⟨1,r⟩) (B := (ofRealRaw c).compute n)
    (z := ⟨1,r⟩) (w := p) (QComplex.le_refl _) (QComplex.le_refl _) hpc.1 hpc.2
  have hs := QBox.scaleRat_contains (r := r) hpc.1 hpc.2
  have hscaled : ((ofRealRaw (RealRaw.scaleRat r c)).compute n).lo ≤ QComplex.scaleRat r p ∧
      QComplex.scaleRat r p ≤ ((ofRealRaw (RealRaw.scaleRat r c)).compute n).hi := by
    by_cases hr : 0 ≤ r
    · simpa only [ofRealRaw,RealRaw.scaleRat,RealRaw.scaleRatCompute,QBox.scaleRat,QComplex.scaleRat,
        Rat.mul_zero,if_pos hr] using hs
    · simpa only [ofRealRaw,RealRaw.scaleRat,RealRaw.scaleRatCompute,QBox.scaleRat,QComplex.scaleRat,
        Rat.mul_zero,if_neg hr] using hs
  have hi : ((imaginaryAxis (RealRaw.scaleRat r c)).compute n).lo ≤ ⟨0,r*p.re⟩ ∧
      ⟨0,r*p.re⟩ ≤ ((imaginaryAxis (RealRaw.scaleRat r c)).compute n).hi := by
    exact ⟨⟨Rat.le_refl,hscaled.1.1⟩,⟨Rat.le_refl,hscaled.2.1⟩⟩
  have ha := QBox.add_contains hpc.1 hpc.2 hi.1 hi.2
  have he : QComplex.add p ⟨0,r*p.re⟩ = QComplex.mul ⟨1,r⟩ p := by
    simp only [p,QComplex.add,QComplex.mul,Rat.add_zero,Rat.mul_zero,Rat.one_mul,Rat.zero_add,Rat.sub_eq_add_neg,Rat.neg_zero]
  exact (compareAt_overlap_iff _ _ n n).mpr
    (QBox.overlaps_of_common_point ha (by rw [he]; exact hm))

theorem from_slope (f : ComplexRaw) (hf : f.Valid) (r : Rat)
    (h : f.imagPart.Equiv (RealRaw.scaleRat r f.realPart)) :
    f.Equiv (mul (ofQComplex ⟨1,r⟩) (ofRealRaw f.realPart)) :=
  equiv_trans hf (add_valid (ofRealRaw_valid _ (realPart_valid hf)) (imaginaryAxis_valid (imagPart_valid hf)))
    (mul_valid (ofQComplex_valid _) (ofRealRaw_valid _ (realPart_valid hf))) (parts f hf)
    (equiv_trans (add_valid (ofRealRaw_valid _ (realPart_valid hf)) (imaginaryAxis_valid (imagPart_valid hf)))
      (add_valid (ofRealRaw_valid _ (realPart_valid hf)) (imaginaryAxis_valid (RealRaw.scaleRat_valid (realPart_valid hf))))
      (mul_valid (ofQComplex_valid _) (ofRealRaw_valid _ (realPart_valid hf)))
      (add_equiv (equiv_refl _ (ofRealRaw_valid _ (realPart_valid hf)))
        (imaginaryAxis_equiv (imagPart_valid hf) (RealRaw.scaleRat_valid (realPart_valid hf)) h))
      (realVector_product r _ (realPart_valid hf)))

theorem conjugate_product (f g : ComplexRaw) (hf : f.Valid) (hg : g.Valid) :
    (conj (mul f g)).Equiv (mul (conj f) (conj g)) := by
  intro n
  let p := (f.compute n).center
  let q := (g.compute n).center
  have hp := QBox.center_mem (valid_ordered hf n)
  have hq := QBox.center_mem (valid_ordered hg n)
  have hm := QBox.mul_contains hp.1 hp.2 hq.1 hq.2
  have hmc : ((conj (mul f g)).compute n).lo ≤ QComplex.conj (QComplex.mul p q) ∧
      QComplex.conj (QComplex.mul p q) ≤ ((conj (mul f g)).compute n).hi :=
    ⟨⟨hm.1.1,Rat.neg_le_neg hm.2.2⟩,⟨hm.2.1,Rat.neg_le_neg hm.1.2⟩⟩
  have hpc : ((conj f).compute n).lo ≤ QComplex.conj p ∧ QComplex.conj p ≤ ((conj f).compute n).hi :=
    ⟨⟨hp.1.1,Rat.neg_le_neg hp.2.2⟩,⟨hp.2.1,Rat.neg_le_neg hp.1.2⟩⟩
  have hqc : ((conj g).compute n).lo ≤ QComplex.conj q ∧ QComplex.conj q ≤ ((conj g).compute n).hi :=
    ⟨⟨hq.1.1,Rat.neg_le_neg hq.2.2⟩,⟨hq.2.1,Rat.neg_le_neg hq.1.2⟩⟩
  have hmr := QBox.mul_contains hpc.1 hpc.2 hqc.1 hqc.2
  exact (compareAt_overlap_iff _ _ n n).mpr
    (QBox.overlaps_of_common_point hmc (by rw [QComplex.conj_mul]; exact hmr))

theorem conjugate_real (c : RealRaw) (hc : c.Valid) : (conj (ofRealRaw c)).Equiv (ofRealRaw c) := by
  intro n
  have hp := QBox.center_mem (valid_ordered (ofRealRaw_valid _ hc) n)
  apply (compareAt_overlap_iff _ _ n n).mpr
  simp only [conj,ofRealRaw,QBox.conj,Rat.neg_zero,QBox.Overlaps,QComplex.le_def]
  have ho := RealRaw.interval_order_of_valid _ hc n
  unfold QInterval.width at ho
  constructor <;> constructor <;> grind only

theorem point_product (a b : QComplex) :
    (mul (ofQComplex a) (ofQComplex b)).Equiv (ofQComplex (QComplex.mul a b)) := by
  intro n
  have hm := QBox.mul_contains (A := QBox.point a) (B := QBox.point b)
    (z := a) (w := b) (QComplex.le_refl _) (QComplex.le_refl _) (QComplex.le_refl _) (QComplex.le_refl _)
  exact (compareAt_overlap_iff _ _ n n).mpr
    (QBox.overlaps_of_common_point hm ⟨QComplex.le_refl _,QComplex.le_refl _⟩)

theorem rational_circle_square (r : Rat) :
    QComplex.mul (GeometricRotationODE.pointComplex r)
      (QComplex.mul ⟨1,r⟩ ⟨1,-r⟩) = QComplex.mul ⟨1,r⟩ ⟨1,r⟩ := by
  have hd := Rat.mul_inv_cancel (1+r*r) (Rat.ne_of_gt (denominator_pos r))
  simp only [GeometricRotationODE.pointComplex,RationalCircle.Stage.point,QComplex.mul,Rat.div_def]
  congr 1 <;> grind only

theorem rotation_unit (x : RealRaw) (hx : x.Valid) :
    (mul (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val
      (conj (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val)).Equiv (ofQComplex QComplex.one) := by
  let z : Scalar := ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩
  let sum : Scalar := ⟨add z.val (conj z.val),add_valid z.property (conj_valid _ z.property)⟩
  have hi : sum.val.Equiv zero := by
    intro n
    have ho := RealRaw.interval_order_of_valid x hx n
    unfold QInterval.width at ho
    apply (compareAt_overlap_iff _ _ n n).mpr
    simp only [sum,z,add,conj,imaginaryAxis,mulI,ofRealRaw,QBox.add,QBox.conj,
      QComplex.add,zero,ofQComplex,QBox.point,QComplex.zero,QBox.Overlaps,QComplex.le_def,Rat.neg_zero,Rat.zero_add]
    constructor <;> constructor <;> grind only
  exact equiv_trans (mul_valid (entireExponentialValue z).property (conj_valid _ (entireExponentialValue z).property))
    (entireExponentialValue sum).property (ofQComplex_valid _) (entireExponential_conjugate_product z)
    (equiv_trans (entireExponentialValue sum).property (entireExponentialValue ⟨zero,ofQComplex_valid _⟩).property
      (ofQComplex_valid _) (entireExponentialValue_congr sum _ hi) entireExponential_zero)

theorem rotation_square (x : RealRaw) (hx : x.Valid) (r : Rat)
    (hr : (sineAtAngle x hx).Equiv (RealRaw.scaleRat r (cosineAtAngle x hx))) :
    (mul (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val
      (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val).Equiv
        (ofQComplex (GeometricRotationODE.pointComplex r)) := by
  let f := (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val
  have hf := (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).property
  let c := ofRealRaw f.realPart
  have hc := ofRealRaw_valid _ (realPart_valid hf)
  let k : QComplex := ⟨1,r⟩
  let b : QComplex := ⟨1,-r⟩
  let p := GeometricRotationODE.pointComplex r
  have hfc := from_slope f hf r hr
  have hconj : (conj f).Equiv (mul (ofQComplex b) c) :=
    equiv_trans (conj_valid _ hf) (conj_valid _ (mul_valid (ofQComplex_valid k) hc))
      (mul_valid (ofQComplex_valid b) hc) (conj_equiv hfc)
      (equiv_trans (conj_valid _ (mul_valid (ofQComplex_valid k) hc))
        (mul_valid (conj_valid _ (ofQComplex_valid k)) (conj_valid _ hc))
        (mul_valid (ofQComplex_valid b) hc) (conjugate_product _ _ (ofQComplex_valid k) hc)
        (mul_equiv (conj_valid _ (ofQComplex_valid k)) (ofQComplex_valid b) (conj_valid _ hc) hc
          (equiv_refl _ (ofQComplex_valid b)) (conjugate_real _ (realPart_valid hf))))
  have hF := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := hf) (hright := mul_valid (ofQComplex_valid k) hc) hfc
  have hB := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := conj_valid _ hf) (hright := mul_valid (ofQComplex_valid b) hc) hconj
  have hU := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid hf (conj_valid _ hf)) (hright := ofQComplex_valid _)
    (rotation_unit x hx)
  have hKB := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid (ofQComplex_valid k) (ofQComplex_valid b))
    (hright := ofQComplex_valid _) (point_product k b)
  have hKK := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid (ofQComplex_valid k) (ofQComplex_valid k))
    (hright := ofQComplex_valid _) (point_product k k)
  have hP := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid (ofQComplex_valid p) (ofQComplex_valid (QComplex.mul k b)))
    (hright := ofQComplex_valid _) (point_product p (QComplex.mul k b))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := mul_valid hf hf) (hright := ofQComplex_valid p)
  let F := ComplexRawQuotient.ofRaw f hf
  let B := ComplexRawQuotient.ofRaw (conj f) (conj_valid _ hf)
  let C := ComplexRawQuotient.ofRaw c hc
  let K := ComplexRawQuotient.ofQComplex k
  let T := ComplexRawQuotient.ofQComplex b
  let P := ComplexRawQuotient.ofQComplex p
  change F=K*C at hF
  change B=T*C at hB
  change F*B=1 at hU
  have hR : P*(K*T)=K*K := by
    change K*K=ComplexRawQuotient.ofQComplex (QComplex.mul k k) at hKK
    rw [hKK]
    change K*T=ComplexRawQuotient.ofQComplex (QComplex.mul k b) at hKB
    rw [hKB]
    change P*ComplexRawQuotient.ofQComplex (QComplex.mul k b)=ComplexRawQuotient.ofQComplex (QComplex.mul p (QComplex.mul k b)) at hP
    rw [hP,rational_circle_square]
  change F*F=P
  grind only

def doubleAngle (x : RealRaw) (hx : x.Valid) : Scalar :=
  ⟨imaginaryAxis (RealRaw.scaleRat 2 x),imaginaryAxis_valid (RealRaw.scaleRat_valid hx)⟩

theorem doubleAngle_add (x : RealRaw) (hx : x.Valid) :
    (doubleAngle x hx).val.Equiv (add (imaginaryAxis x) (imaginaryAxis x)) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  simp only [doubleAngle,imaginaryAxis,mulI,ofRealRaw,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show (0:Rat)≤2 by decide),add,QBox.add,QComplex.add,Rat.neg_zero,Rat.zero_add,
    QBox.Overlaps,QComplex.le_def]
  have ho := RealRaw.interval_order_of_valid x hx n
  unfold QInterval.width at ho
  constructor <;> constructor <;> grind only

theorem exponential_double (x : RealRaw) (hx : x.Valid) :
    (entireExponentialValue (doubleAngle x hx)).val.Equiv
      (mul (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val
        (entireExponentialValue ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩).val) := by
  let z : Scalar := ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩
  let sum : Scalar := ⟨add z.val z.val,add_valid z.property z.property⟩
  exact equiv_trans (entireExponentialValue _).property (entireExponentialValue sum).property
    (mul_valid (entireExponentialValue z).property (entireExponentialValue z).property)
    (entireExponentialValue_congr _ _ (doubleAngle_add x hx)) (equiv_symm (entireExponential_addition z z))

end ComputableAnalysis.ElementaryAngleAlgebra

