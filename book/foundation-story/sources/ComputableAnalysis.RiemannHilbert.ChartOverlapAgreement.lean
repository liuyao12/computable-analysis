import ComputableAnalysis.RiemannHilbert.CenteredChartTransport

/-! Exact agreement of actual solutions on overlaps of differently centered
coefficient charts. The premise identifies the coefficient operators; the
solution agreement is derived by uniform analytic uniqueness. -/
namespace ComputableAnalysis.RiemannHilbert.ChartOverlap
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

def radius (c d : SystemChart n) (p : Scalar) (hc : c.domain p) (hd : d.domain p) : QPos :=
  smallerRadius (c.neighborhoodRadius p hc) (d.neighborhoodRadius p hd)

theorem inside_left (c d : SystemChart n) (p : Scalar) (hc : c.domain p) (hd : d.domain p)
    (z : Scalar) (hz : Centered.domain p (radius c d p hc hd).val z) : c.domain z :=
  c.neighborhood_inside p hc z (interior_mono _ _ (Centered.offset p z) (smallerRadius_le_left _ _) hz)

theorem inside_right (c d : SystemChart n) (p : Scalar) (hc : c.domain p) (hd : d.domain p)
    (z : Scalar) (hz : Centered.domain p (radius c d p hc hd).val z) : d.domain z :=
  d.neighborhood_inside p hd z (interior_mono _ _ (Centered.offset p z) (smallerRadius_le_right _ _) hz)

theorem small_left (c d : SystemChart n) (p : Scalar) (hc : c.domain p) (hd : d.domain p) :
    2*(radius c d p hc hd).val*(8*c.M) ≤ (1 : Rat)/2 := by
  have hr : (radius c d p hc hd).val ≤ (c.neighborhoodRadius p hc).val :=
    smallerRadius_le_left (c.neighborhoodRadius p hc) (d.neighborhoodRadius p hd)
  have hs := c.neighborhood_small p hc
  have hM : 0 ≤ 16*c.M := Rat.mul_nonneg (by decide) c.nonnegM
  have hh := Rat.mul_le_mul_of_nonneg_left hr hM
  grind

def SameOperator (c d : SystemChart n) (p : Scalar) (hc : c.domain p) (hd : d.domain p) : Prop :=
  ∀ z (hz : Centered.domain p (radius c d p hc hd).val z),
    (c.operator z (inside_left c d p hc hd z hz)).Equiv (d.operator z (inside_right c d p hc hd z hz))

/-- This compares whole neighborhoods of actual holomorphic functions. Neither
an endpoint equality nor a postulated solution transition is the premise. -/
theorem through_agreement (c d : SystemChart n) (p : Scalar) (hc : c.domain p) (hd : d.domain p)
    (hA : SameOperator c d p hc hd) (v : Fiber n) (z : Scalar)
    (hz : Centered.domain p (radius c d p hc hd).val z) :
    c.through p hc v z (inside_left c d p hc hd z hz) ≈
      d.through p hd v z (inside_right c d p hc hd z hz) := by
  let R := radius c d p hc hd
  let left := fun z hz => inside_left c d p hc hd z hz
  let right := fun z hz => inside_right c d p hc hd z hz
  let f : Centered.Field (n := n) p R.val := fun z hz => c.through p hc v z (left z hz)
  let g : Centered.Field (n := n) p R.val := fun z hz => d.through p hd v z (right z hz)
  let A : Centered.OperatorField (n := n) p R.val := fun z hz => c.operator z (left z hz)
  refine Centered.equal p R A f g (8*c.M) (4*initialBound (c.seed p hc v)) (4*initialBound (d.seed p hd v))
    (Rat.mul_nonneg (by decide) c.nonnegM) (small_left c d p hc hd)
    (Rat.mul_nonneg (by decide) (initialBound_nonneg (c.seed p hc v)))
    (Rat.mul_nonneg (by decide) (initialBound_nonneg (d.seed p hd v)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (c.delta (c.seed p hc v)) (d.delta (d.seed p hd v)) ?_ ?_ z hz
  · intro z w hz hw hzw
    exact c.through_congr p hc v v (Setoid.refl _) z w hzw (left z hz) (left w hw)
  · intro z w hz hw hzw
    exact d.through_congr p hd v v (Setoid.refl _) z w hzw (right z hz) (right w hw)
  · exact Setoid.trans (c.through_normalized p hc v) (Setoid.symm (d.through_normalized p hd v))
  · intro z hz; exact c.through_bound p hc v z (left z hz)
  · intro z hz; exact d.through_bound p hd v z (right z hz)
  · intro z hz; exact c.operator_linear z (left z hz)
  · intro z hz B hB x hx; exact c.operator_bound z (left z hz) B hB x hx
  · intro eps H w z hw hz hH hzw
    exact c.value_uniform_remainder (c.seed p hc v) eps H w z (left w hw) (left z hz) hH hzw
  · intro eps H w z hw hz hH hzw
    have hs := d.value_uniform_remainder (d.seed p hd v) eps H w z (right w hw) (right z hz) hH hzw
    let displacement : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
    exact bound_congr (Fiber.sub_congr (Setoid.refl _)
      (Fiber.scale_congr (a := displacement) (b := displacement) (equiv_refl _ displacement.property)
        (Setoid.symm (hA w hw (d.through p hd v w (right w hw)))))) hs

theorem transport_agreement (c d : SystemChart n) (p : Scalar) (hc : c.domain p) (hd : d.domain p)
    (hA : SameOperator c d p hc hd) (q : Scalar)
    (hq : Centered.domain p (radius c d p hc hd).val q) :
    (c.transport p q hc (inside_left c d p hc hd q hq)).toValueIso.forward.Equiv
      (d.transport p q hd (inside_right c d p hc hd q hq)).toValueIso.forward :=
  fun v => through_agreement c d p hc hd hA v q hq

/-- Replacing the chart for an edge in this connected common neighborhood
changes neither its forward transport nor its inverse value. -/
theorem inverse_transport_agreement (c d : SystemChart n) (p : Scalar) (hc : c.domain p) (hd : d.domain p)
    (hA : SameOperator c d p hc hd) (q : Scalar)
    (hq : Centered.domain p (radius c d p hc hd).val q) :
    (c.transport p q hc (inside_left c d p hc hd q hq)).toValueIso.backward.Equiv
      (d.transport p q hd (inside_right c d p hc hd q hq)).toValueIso.backward :=
  ValueIso.inverse_congr _ _ (transport_agreement c d p hc hd hA q hq)

end ComputableAnalysis.RiemannHilbert.ChartOverlap
