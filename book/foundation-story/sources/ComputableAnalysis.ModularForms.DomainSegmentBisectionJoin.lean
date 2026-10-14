import ComputableAnalysis.ModularForms.DyadicSampleAverage

import ComputableAnalysis.ModularForms.DomainLocalEndpointVariation
import ComputableAnalysis.ModularForms.PairedRiccatiGlobalSegmentVariation

/-! Domain-safe joining of endpoint variation estimates on the unit
parameter segment, without extending the map outside its domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Coverage of the actual represented unit segment supplies every rational
endpoint certificate needed by bisection, by exact affine agreement. -/
theorem domainSegment_rational_mem (f : DomainFunctions.Map) (p q : Scalar)
    (mem : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (u : Rat) (hu : 0≤u) (hu1 : u≤1) : f.domain (AffineSegment.point p q u) := by
  let t := UnitInterval.rational u hu hu1
  have he := RepresentedAffineSegment.rational_agreement p q u hu hu1
  exact (f.domain_congr (RepresentedAffineSegment.point p q t)
    (AffineSegment.point p q u) he).1 (mem t)

/-- Endpoint comparison only for ordered intervals inside the unit segment. -/
def domainSegmentEndpointGood (f : DomainFunctions.Map) (p q : Scalar)
    (mem : ∀ u : Rat, 0≤u → u≤1 → f.domain (AffineSegment.point p q u))
    (C W : Rat) (I : QInterval) : Prop :=
  ∀ (ho : I.lo≤I.hi) (hl : 0≤I.lo) (hh : I.hi≤1),
    Small (sub (f.eval (AffineSegment.point p q I.hi) (mem I.hi (Rat.le_trans hl ho) hh)).val
      (f.eval (AffineSegment.point p q I.lo) (mem I.lo hl (Rat.le_trans ho hh))).val)
      (C*W*I.width)

/-- The two half-interval estimates join, retaining genuine endpoint
domain evidence and the full segment restriction. -/
theorem domainSegmentEndpointGood_join (f : DomainFunctions.Map) (p q : Scalar)
    (mem : ∀ u : Rat, 0≤u → u≤1 → f.domain (AffineSegment.point p q u))
    (C W : Rat) (I : QInterval)
    (hl : domainSegmentEndpointGood f p q mem C W (bisectInterval I false))
    (hr : domainSegmentEndpointGood f p q mem C W (bisectInterval I true)) :
    domainSegmentEndpointGood f p q mem C W I := by
  intro ho hlo hhi
  have hm := midpoint_mem I ho
  have hm0 := Rat.le_trans hlo hm.1
  have hm1 := Rat.le_trans hm.2 hhi
  have hleft := hl hm.1 hlo hm1
  have hright := hr hm.2 hm0 hhi
  let A := f.eval (AffineSegment.point p q I.hi) (mem I.hi (Rat.le_trans hlo ho) hhi)
  let B := f.eval (AffineSegment.point p q I.midpoint) (mem I.midpoint hm0 hm1)
  let D := f.eval (AffineSegment.point p q I.lo) (mem I.lo hlo (Rat.le_trans ho hhi))
  have hb := LocalODE.small_add hright hleft
  have hs := Small.congr (add_valid (sub_valid A.property B.property) (sub_valid B.property D.property))
    (sub_valid A.property D.property) (representedDifference_split A B D) hb
  have he : C*W*(bisectInterval I true).width+C*W*(bisectInterval I false).width=C*W*I.width := by
    rw [bisectInterval_width,bisectInterval_width]
    grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.ModularForms
