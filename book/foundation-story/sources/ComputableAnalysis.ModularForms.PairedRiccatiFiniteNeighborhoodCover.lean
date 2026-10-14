import ComputableAnalysis.ModularForms.PairedRiccatiParameterNeighborhood

/-! A finite bisection cover by actual Riccati neighborhoods. This is an
existence theorem, not an executable uniform-mesh selector. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

inductive RiccatiNeighborhoodCover (p q : Scalar) (eps : QPos) : QInterval → Prop
  | neighborhood (J : QInterval) (t : UnitInterval.Point)
      (bound : ∀ u : Rat, J.lo≤u → u≤J.hi → 0≤u → u≤1 →
        Small (sub (pairedEntireRiccatiMap.eval (AffineSegment.point p q u) trivial).val
          (pairedEntireRiccatiMap.eval (RepresentedAffineSegment.point p q t) trivial).val)
          eps.val) : RiccatiNeighborhoodCover p q eps J
  | split (J : QInterval)
      (left : RiccatiNeighborhoodCover p q eps (bisectInterval J false))
      (right : RiccatiNeighborhoodCover p q eps (bisectInterval J true)) :
      RiccatiNeighborhoodCover p q eps J

theorem pairedRiccati_finite_neighborhood_cover (p q : Scalar) (W : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val) (eps : QPos) :
    RiccatiNeighborhoodCover p q eps ⟨0,1⟩ := by
  apply represented_interval_cover (RiccatiNeighborhoodCover p q eps) ⟨0,1⟩
    (by decide +kernel)
  · intro J hl hr
    exact RiccatiNeighborhoodCover.split J hl hr
  · intro x hx hl hh
    let t : UnitInterval.Point := ⟨x,hx,hl,hh⟩
    obtain ⟨r,hr⟩ := pairedRiccati_parameter_neighborhood p q W hd t eps
    refine ⟨r, ?_⟩
    intro J hJ
    apply RiccatiNeighborhoodCover.neighborhood J t
    intro u hulo huhi hu0 hu1
    have hn := hJ u hulo huhi
    exact hr u hu0 hu1 hn.1 hn.2

end ComputableAnalysis.ModularForms
