import ComputableAnalysis.EnclosureHolomorphic

/-! A negative test: covering all complex directions excludes conjugation.
The proof uses two exact rational displacements and a shrinking derivative
box, with no appeal to completed complex numbers. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCounterexample
open ComplexRaw FunctionTheory DomainFunctions
set_option maxHeartbeats 2000000

def conjugation : DomainFunctions.Map where
  domain _ := True
  eval z _ := ⟨conj z.val,conj_valid z.val z.property⟩
  domain_congr _ _ _ := Iff.rfl
  eval_congr _ _ _ _ he := conj_equiv he

def origin : Scalar := ⟨zero,ofQComplex_valid _⟩
def realPoint (H : QPos) : Scalar := ⟨ofQComplex ⟨H.val,0⟩,ofQComplex_valid _⟩
def imagPoint (H : QPos) : Scalar := ⟨ofQComplex ⟨0,H.val⟩,ofQComplex_valid _⟩

theorem realPoint_small (H : QPos) : Small (sub (realPoint H).val origin.val) H.val := by
  have hp := H.property
  refine ⟨?_,?_,?_,?_⟩ <;> intro i j <;>
    change _ ≤ _ <;>
    simp only [realPoint,origin,sub,add,neg,zero,ofQComplex,QBox.neg,QBox.point,QComplex.neg,QComplex.add,QBox.add,QComplex.zero,realPart,imagPart,RealRaw.ofRat] <;> grind

theorem imagPoint_small (H : QPos) : Small (sub (imagPoint H).val origin.val) H.val := by
  have hp := H.property
  refine ⟨?_,?_,?_,?_⟩ <;> intro i j <;>
    change _ ≤ _ <;>
    simp only [imagPoint,origin,sub,add,neg,zero,ofQComplex,QBox.neg,QBox.point,QComplex.neg,QComplex.add,QBox.add,QComplex.zero,realPart,imagPart,RealRaw.ofRat] <;> grind

/-- Both rational axis directions must satisfy the same first-order law. -/
theorem conjugation_not_differentiable (d : Scalar) :
    ¬ HasEnclosureDerivativeAt conjugation origin trivial d := by
  intro h
  obtain ⟨h⟩ := h.quantitative
  let eps : QPos := ⟨1/4,by decide +kernel⟩
  let H := h.delta eps
  have hr := h.estimate eps H (realPoint H) trivial Rat.le_refl (realPoint_small H)
  have hi := h.estimate eps H (imagPoint H) trivial Rat.le_refl (imagPoint_small H)
  obtain ⟨N,hN⟩ := (realPart_valid d.property).2.2 eps
  have width := hN N (Nat.le_refl _)
  have ordered := (valid_ordered d.property N).1
  have hp := H.property
  have hlohi : (d.val.compute N).lo.re*H.val ≤ (d.val.compute N).hi.re*H.val :=
    Rat.mul_le_mul_of_nonneg_right ordered (Rat.le_of_lt hp)
  have r := hr.2.1 N 0
  have i := hi.2.2.1 0 N
  change _ ≤ eps.val*H.val at r
  change -(eps.val*H.val) ≤ _ at i
  simp only [remainder,conjugation,realPoint,imagPoint,origin,sub,add,neg,mul,conj,zero,
    ofQComplex,QBox.mul,QBox.mulRealInterval,QBox.conj,QBox.neg,QBox.point,
    QComplex.conj,QComplex.neg,QComplex.add,QBox.add,QComplex.zero,realPart,imagPart,RealRaw.ofRat,Rat.mul_zero,Rat.zero_mul,
    Rat.add_zero,Rat.zero_add,Rat.neg_zero,Rat.sub_self,Rat.sub_eq_add_neg] at r i
  simp only [min4,max4,minRat,maxRat2,if_pos Rat.le_refl,if_pos hlohi,
    Rat.neg_zero,Rat.add_zero] at r i
  have hw : (d.val.compute N).hi.re-(d.val.compute N).lo.re ≤ (1/4:Rat) := width
  change _ ≤ (1/4:Rat)*H.val at r
  change -((1/4:Rat)*H.val) ≤ _ at i
  have hwidth := Rat.mul_le_mul_of_nonneg_right hw (Rat.le_of_lt hp)
  grind only [Rat.sub_eq_add_neg,Rat.add_mul,Rat.neg_mul]

/-- Conjugation preserves exact coordinate smallness. -/
theorem conjugation_small {z : ComplexRaw} {r : Rat} (h : Small z r) : Small (conj z) r := by
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro i j
    have b := h.2.2.2 j i
    change (z.compute j).lo.im ≤ r at b
    change -r ≤ -(z.compute j).lo.im
    exact Rat.neg_le_neg b
  · intro i j
    have b := h.2.2.1 j i
    change -r ≤ (z.compute i).hi.im at b
    change -(z.compute i).hi.im ≤ r
    grind only

theorem conjugation_sub (z w : ComplexRaw) (hz : z.Valid) (hw : w.Valid) :
    (conj (sub z w)).Equiv (sub (conj z) (conj w)) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have he : (conj (sub z w)).compute n = (sub (conj z) (conj w)).compute n := by
    dsimp [conj,sub,add,neg,QBox.add,QBox.neg,QBox.conj,QComplex.add,QComplex.neg,QComplex.conj]
    congr 1 <;> congr 1 <;> grind only
  rw [he]
  have ho := valid_ordered (sub_valid (conj_valid z hz) (conj_valid w hw)) n
  exact ⟨ho,ho⟩

/-- The rejected function has an executable continuity modulus. -/
def conjugation_continuous : ContinuousOn conjugation.domain conjugation.eval where
  delta _ _ eps := eps
  estimate a _ eps z _ near := by
    change Small (sub (conj z.val) (conj a.val)) eps.val
    exact Small.congr (conj_valid _ (sub_valid z.property a.property))
      (sub_valid (conj_valid z.val z.property) (conj_valid a.val a.property))
      (conjugation_sub z.val a.val z.property a.property) (conjugation_small near)

/-- Conjugation has no holomorphic witness even though it is continuous. -/
theorem conjugation_not_holomorphic : ¬ IsEnclosureHolomorphic conjugation := by
  intro h
  obtain ⟨d,hd⟩ := h.differentiable.2 origin trivial
  exact conjugation_not_differentiable d hd

end ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureCounterexample
