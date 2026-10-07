import ComputableAnalysis.ModularForms.AngleSegmentDerivative

/-! Strict real-coordinate signs survive quantitatively bounded remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem negative_real_add_small (d e : Scalar) (N : Nat)
    (hd : (d.val.compute N).hi.re < 0)
    (he : Small e.val (-(d.val.compute N).hi.re/2)) :
    (add d.val e.val).realPart.Neg := by
  let c := -(d.val.compute N).hi.re
  have hc : 0<c := by dsimp [c]; grind only
  let eps : QPos := ⟨c/4,by
    rw [Rat.div_def]
    exact Rat.mul_pos hc (by decide +kernel)⟩
  obtain ⟨K,hK⟩ := (realPart_valid e.property).2.2 eps
  let M := max N K
  have hn := (d.property.2.1 N M (Nat.le_max_left _ _)).2.1
  have hb := he.2.1 M M
  have hw := hK M (Nat.le_max_right _ _)
  change (d.val.compute M).hi.re≤(d.val.compute N).hi.re at hn
  change (e.val.compute M).lo.re≤c/2 at hb
  change (e.val.compute M).hi.re-(e.val.compute M).lo.re≤c/4 at hw
  refine ⟨M,?_⟩
  change (d.val.compute M).hi.re+(e.val.compute M).hi.re<0
  have hdc : (d.val.compute N).hi.re= -c := by dsimp [c]; grind only
  rw [hdc] at hn
  generalize (d.val.compute M).hi.re=a at hn ⊢
  generalize (e.val.compute M).lo.re=b at hb hw
  generalize (e.val.compute M).hi.re=v at hw ⊢
  grind only

theorem negative_real_add_small_equiv (d e v : Scalar) (N : Nat)
    (hd : (d.val.compute N).hi.re < 0)
    (he : Small e.val (-(d.val.compute N).hi.re/2))
    (hv : (add d.val e.val).Equiv v.val) : v.val.realPart.Neg := by
  have hp := negative_real_add_small d e N hd he
  have hn : (RealRaw.neg (add d.val e.val).realPart).Pos := by
    obtain ⟨K,hK⟩ := hp
    refine ⟨K,?_⟩
    change 0< -((add d.val e.val).compute K).hi.re
    change ((add d.val e.val).compute K).hi.re<0 at hK
    grind only
  have ht := positive_of_equiv
    (RealRaw.neg_valid (realPart_valid (add_valid d.property e.property)))
    (RealRaw.neg_valid (realPart_valid v.property))
    (RealRaw.neg_equiv (realPart_equiv hv)) hn
  obtain ⟨K,hK⟩ := ht
  refine ⟨K,?_⟩
  change 0< -(v.val.compute K).hi.re at hK
  change (v.val.compute K).hi.re<0
  grind only

end ComputableAnalysis.ModularForms
