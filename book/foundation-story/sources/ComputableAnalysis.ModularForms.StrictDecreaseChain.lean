import ComputableAnalysis.ModularForms.NegativeDerivativeNeighborhood

/-! Finite strict-decrease comparisons compose over represented values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem negative_real_congr (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hz : z.val.realPart.Neg) : w.val.realPart.Neg := by
  have hp : (RealRaw.neg z.val.realPart).Pos := by
    obtain ⟨N,hN⟩ := hz
    refine ⟨N,?_⟩
    change 0< -(z.val.compute N).hi.re
    change (z.val.compute N).hi.re<0 at hN
    grind only
  have h := positive_of_equiv (RealRaw.neg_valid (realPart_valid z.property))
    (RealRaw.neg_valid (realPart_valid w.property))
    (RealRaw.neg_equiv (realPart_equiv hzw)) hp
  obtain ⟨N,hN⟩ := h
  refine ⟨N,?_⟩
  change 0< -(w.val.compute N).hi.re at hN
  change (w.val.compute N).hi.re<0
  grind only

theorem negative_real_add (z w : Scalar) (hz : z.val.realPart.Neg)
    (hw : w.val.realPart.Neg) : (add z.val w.val).realPart.Neg := by
  obtain ⟨N,hN⟩ := hz
  obtain ⟨K,hK⟩ := hw
  let M := max N K
  have hn := (z.property.2.1 N M (Nat.le_max_left _ _)).2.1
  have hk := (w.property.2.1 K M (Nat.le_max_right _ _)).2.1
  change (z.val.compute M).hi.re≤(z.val.compute N).hi.re at hn
  change (w.val.compute M).hi.re≤(w.val.compute K).hi.re at hk
  change (z.val.compute N).hi.re<0 at hN
  change (w.val.compute K).hi.re<0 at hK
  refine ⟨M,?_⟩
  change (z.val.compute M).hi.re+(w.val.compute M).hi.re<0
  grind only

theorem strict_decrease_join (a b c : Scalar)
    (hab : (sub b.val a.val).realPart.Neg)
    (hbc : (sub c.val b.val).realPart.Neg) :
    (sub c.val a.val).realPart.Neg := by
  let x : Scalar := ⟨sub b.val a.val,sub_valid b.property a.property⟩
  let y : Scalar := ⟨sub c.val b.val,sub_valid c.property b.property⟩
  let s : Scalar := ⟨add x.val y.val,add_valid x.property y.property⟩
  let v : Scalar := ⟨sub c.val a.val,sub_valid c.property a.property⟩
  have he : s.val.Equiv v.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := s.property) (hright := v.property)
    change (gridScalarValue b-gridScalarValue a)+(gridScalarValue c-gridScalarValue b)=
      gridScalarValue c-gridScalarValue a
    grind only
  exact negative_real_congr s v he (negative_real_add x y hab hbc)

theorem strict_decrease_finite_chain (v : Nat → Scalar) (n : Nat)
    (h : ∀ k, k<n+1 → (sub (v (k+1)).val (v k).val).realPart.Neg) :
    (sub (v (n+1)).val (v 0).val).realPart.Neg := by
  induction n with
  | zero => exact h 0 (by omega)
  | succ n ih =>
    have hp := ih (fun k hk => h k (by omega))
    exact strict_decrease_join (v 0) (v (n+1)) (v (n+2)) hp (h (n+1) (by omega))

end ComputableAnalysis.ModularForms
