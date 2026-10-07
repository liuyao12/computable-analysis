import ComputableAnalysis.ModularForms.RepresentedRotationOrder

/-! A strict comparison between interior values gives a strict endpoint
comparison through exact represented order. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 2000000

theorem strict_decrease_of_order_sandwich (a b p q : Scalar)
    (hp : p.val.realPart.Le a.val.realPart)
    (hq : b.val.realPart.Le q.val.realPart)
    (h : (sub q.val p.val).realPart.Neg) :
    (sub b.val a.val).realPart.Neg := by
  obtain ⟨N,hN⟩ := h
  change (q.val.compute N).hi.re+ -(p.val.compute N).lo.re<0 at hN
  let eps : QPos := ⟨((p.val.compute N).lo.re-(q.val.compute N).hi.re)/4,by
    have hh : 0<(p.val.compute N).lo.re-(q.val.compute N).hi.re := by grind only
    rw [Rat.div_def]
    exact Rat.mul_pos hh (by decide +kernel)⟩
  obtain ⟨Na,hNa⟩ := (realPart_valid a.property).2.2 eps
  obtain ⟨Nb,hNb⟩ := (realPart_valid b.property).2.2 eps
  let M := max Na Nb
  have ha := hNa M (Nat.le_max_left _ _)
  have hb := hNb M (Nat.le_max_right _ _)
  have hl := hp N M
  have hu := hq M N
  change (a.val.compute M).hi.re-(a.val.compute M).lo.re≤eps.val at ha
  change (b.val.compute M).hi.re-(b.val.compute M).lo.re≤eps.val at hb
  change (p.val.compute N).lo.re≤(a.val.compute M).hi.re at hl
  change (b.val.compute M).lo.re≤(q.val.compute N).hi.re at hu
  refine ⟨M,?_⟩
  change (b.val.compute M).hi.re+ -(a.val.compute M).lo.re<0
  have he : eps.val=((p.val.compute N).lo.re-(q.val.compute N).hi.re)/4 := rfl
  grind only

def boundedRationalAngle (r : Rat) (hl : 1≤r) (hh : r≤2) : BoundedAngle where
  raw := RealRaw.ofRat r
  valid := RealRaw.ofRat_valid r
  bounds _ := ⟨hl,hh⟩

theorem represented_rotation_strict_decrease_of_separation (A B : BoundedAngle)
    (N M : Nat) (h : (A.raw.compute N).hi<(B.raw.compute M).lo) :
    (sub (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩).val
      (angleRotationMap.eval A.scalar ⟨trivial,trivial⟩).val).realPart.Neg := by
  let u := (A.raw.compute N).hi
  let v := (B.raw.compute M).lo
  have hao := RealRaw.interval_order_of_valid A.raw A.valid N
  have hbo := RealRaw.interval_order_of_valid B.raw B.valid M
  have hu : 1≤u := Rat.le_trans (A.bounds N).1 hao
  have hv : v≤2 := Rat.le_trans hbo (B.bounds M).2
  have hu2 : u≤2 := (A.bounds N).2
  have hv1 : 1≤v := (B.bounds M).1
  let U := boundedRationalAngle u hu hu2
  let V := boundedRationalAngle v hv1 hv
  have hAU : A.raw.Le U.raw := by
    intro n m
    exact ((RealRaw.compareAt_overlap_iff _ _ n N).1
      (RealRaw.allStagesOverlap_refl A.raw A.valid n N)).1
  have hVB : V.raw.Le B.raw := by
    intro n m
    exact ((RealRaw.compareAt_overlap_iff _ _ M m).1
      (RealRaw.allStagesOverlap_refl B.raw B.valid M m)).1
  have hp := represented_rotation_order A U hAU
  have hq := represented_rotation_order V B hVB
  have hd := rational_rotation_strict_decrease u v hu hv h
  exact strict_decrease_of_order_sandwich
    (angleRotationMap.eval A.scalar ⟨trivial,trivial⟩)
    (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩)
    (angleRotationMap.eval U.scalar ⟨trivial,trivial⟩)
    (angleRotationMap.eval V.scalar ⟨trivial,trivial⟩) hp hq hd

theorem represented_rotation_angle_unique (A B : BoundedAngle)
    (he : (angleRotationMap.eval A.scalar ⟨trivial,trivial⟩).val.realPart.Equiv
      (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩).val.realPart) : A.raw.Equiv B.raw := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  constructor
  · apply Classical.byContradiction
    intro h
    have hs : (B.raw.compute n).hi<(A.raw.compute n).lo := by grind only
    have hd := represented_rotation_strict_decrease_of_separation B A n n hs
    exact negative_increment_not_equiv
      (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩)
      (angleRotationMap.eval A.scalar ⟨trivial,trivial⟩) hd he
  · apply Classical.byContradiction
    intro h
    have hs : (A.raw.compute n).hi<(B.raw.compute n).lo := by grind only
    have hd := represented_rotation_strict_decrease_of_separation A B n n hs
    exact negative_increment_not_equiv
      (angleRotationMap.eval A.scalar ⟨trivial,trivial⟩)
      (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩) hd (RealRaw.equiv_symm he)

end ComputableAnalysis.ModularForms
