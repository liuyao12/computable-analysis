import ComputableAnalysis.ModularForms.StrictIncrementOrder

/-! Exact order passes through justified arbitrarily accurate approximations. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem real_order_of_accurate_approximations (x y : Scalar)
    (h : ∀ eps : QPos, ∃ a b : Scalar,
      b.val.realPart.Le a.val.realPart ∧
      Small (sub x.val a.val) eps.val ∧ Small (sub y.val b.val) eps.val) :
    y.val.realPart.Le x.val.realPart := by
  intro n m
  change (y.val.compute n).lo.re≤(x.val.compute m).hi.re
  apply Classical.byContradiction
  intro hn
  have hg : 0<(y.val.compute n).lo.re-(x.val.compute m).hi.re := by grind only
  let eps : QPos := ⟨((y.val.compute n).lo.re-(x.val.compute m).hi.re)/8,by
    rw [Rat.div_def]
    exact Rat.mul_pos hg (by decide +kernel)⟩
  obtain ⟨a,b,hab,hx,hy⟩ := h eps
  obtain ⟨Na,hNa⟩ := (realPart_valid a.property).2.2 eps
  obtain ⟨Nb,hNb⟩ := (realPart_valid b.property).2.2 eps
  let K := max n (max m (max Na Nb))
  have hNaK : Na≤K := by dsimp [K]; omega
  have hNbK : Nb≤K := by dsimp [K]; omega
  have hnK : n≤K := by dsimp [K]; omega
  have hmK : m≤K := by dsimp [K]; omega
  have hwa := hNa K hNaK
  have hwb := hNb K hNbK
  have ho := hab K K
  have hl := hx.1 K K
  have hu := hy.2.1 K K
  change (a.val.compute K).hi.re-(a.val.compute K).lo.re≤eps.val at hwa
  change (b.val.compute K).hi.re-(b.val.compute K).lo.re≤eps.val at hwb
  change (b.val.compute K).lo.re≤(a.val.compute K).hi.re at ho
  have hxn := (x.property.2.1 m K hmK).2.1
  have hyn := (y.property.2.1 n K hnK).1
  change -eps.val≤(x.val.compute K).hi.re+ -(a.val.compute K).lo.re at hl
  change (y.val.compute K).lo.re+ -(b.val.compute K).hi.re≤eps.val at hu
  have he : eps.val=((y.val.compute n).lo.re-(x.val.compute m).hi.re)/8 := rfl
  grind only

end ComputableAnalysis.ModularForms
