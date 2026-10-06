import ComputableAnalysis.RiemannHilbert.ChartIntersectionAgreement

/-! Representation and quantitative-data invariance for translated charts.
Centers, endpoints, coefficients and vectors may have different valid names;
the independently certified chart bounds may also differ. -/
namespace ComputableAnalysis.RiemannHilbert.SystemChart
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

theorem seed_congr (c d : SystemChart n)
    (hc : c.center.val.Equiv d.center.val) (ha : ∀ k, (c.coefficients k).Equiv (d.coefficients k))
    (p q : Scalar) (hpq : p.val.Equiv q.val) (hp : c.domain p) (hq : d.domain q)
    (v u : Fiber n) (hvu : v ≈ u) : c.seed p hp v ≈ d.seed q hq u :=
  initialFromValue_congr c.coefficients d.coefficients c.linear d.linear ha
    c.M c.K d.M d.K c.nonnegM c.nonnegK d.nonnegM d.nonnegK c.compatible d.compatible c.majorant d.majorant
    (Centered.offset c.center p) (Centered.offset d.center q) (Centered.offset_congr _ _ _ _ hc hpq) hp hq v u hvu

theorem through_data_congr (c d : SystemChart n)
    (hc : c.center.val.Equiv d.center.val) (ha : ∀ k, (c.coefficients k).Equiv (d.coefficients k))
    (p q : Scalar) (hpq : p.val.Equiv q.val) (hp : c.domain p) (hq : d.domain q)
    (v u : Fiber n) (hvu : v ≈ u) (z w : Scalar) (hzw : z.val.Equiv w.val) (hz : c.domain z) (hw : d.domain w) :
    c.through p hp v z hz ≈ d.through q hq u w hw :=
  c.value_congr d (c.seed p hp v) (d.seed q hq u) hc ha (c.seed_congr d hc ha p q hpq hp hq v u hvu) z w hzw hz hw

theorem operator_congr (c d : SystemChart n)
    (hc : c.center.val.Equiv d.center.val) (ha : ∀ k, (c.coefficients k).Equiv (d.coefficients k))
    (z w : Scalar) (hzw : z.val.Equiv w.val) (hz : c.domain z) (hw : d.domain w)
    (v u : Fiber n) (hvu : v ≈ u) : (c.operator z hz).eval v ≈ (d.operator w hw).eval u :=
  coefficientValueMap_congr c.coefficients d.coefficients ha c.M c.K d.M d.K
    c.nonnegM c.nonnegK d.nonnegM d.nonnegK c.majorant d.majorant
    (Centered.offset c.center z) (Centered.offset d.center w) (Centered.offset_congr _ _ _ _ hc hzw) hz hw v u hvu

theorem transport_congr (c d : SystemChart n)
    (hc : c.center.val.Equiv d.center.val) (ha : ∀ k, (c.coefficients k).Equiv (d.coefficients k))
    (p q p' q' : Scalar) (hpp' : p.val.Equiv p'.val) (hqq' : q.val.Equiv q'.val)
    (hp : c.domain p) (hq : c.domain q) (hp' : d.domain p') (hq' : d.domain q') :
    (c.transport p q hp hq).toValueIso.forward.Equiv (d.transport p' q' hp' hq').toValueIso.forward :=
  LocalSystem.transport_congr c.coefficients d.coefficients c.linear d.linear ha
    c.M c.K d.M d.K c.nonnegM c.nonnegK d.nonnegM d.nonnegK c.compatible d.compatible c.majorant d.majorant
    (Centered.offset c.center p) (Centered.offset c.center q) (Centered.offset d.center p') (Centered.offset d.center q')
    (Centered.offset_congr _ _ _ _ hc hpp') (Centered.offset_congr _ _ _ _ hc hqq') hp hq hp' hq'

theorem sameOperator_of_data (c d : SystemChart n)
    (hc : c.center.val.Equiv d.center.val) (ha : ∀ k, (c.coefficients k).Equiv (d.coefficients k)) :
    ChartIntersection.SameOperator c d :=
  fun z hz hw v => c.operator_congr d hc ha z z (equiv_refl _ z.property) hz hw v v (Setoid.refl _)

end ComputableAnalysis.RiemannHilbert.SystemChart
