import ComputableAnalysis.RiemannHilbert.ChartOverlapAgreement
import ComputableAnalysis.RiemannHilbert.UniformSegmentUniqueness

/-! Chart independence on the entire intersection of two constructed disks.
Convex segment coverage and the automatic chart radius supply every
geometric and contraction hypothesis of the comparison theorem. -/
namespace ComputableAnalysis.RiemannHilbert.SystemChart
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

theorem displacement_bound (c : SystemChart n) (p q : Scalar) (hp : c.domain p) (hq : c.domain q) :
    Small (AffineSegment.displacement p q).val (2*c.radius.val) := by
  have hs := SeriesLimitLaws.small_sub
    (interior_bound _ (Centered.offset c.center q) hq) (interior_bound _ (Centered.offset c.center p) hp)
  have he : c.radius.val+c.radius.val=2*c.radius.val := by grind
  rw [he] at hs
  exact Small.congr
    (sub_valid (Centered.offset c.center q).property (Centered.offset c.center p).property)
    (AffineSegment.displacement p q).property (Centered.offset_difference c.center p q) hs

theorem diameter_small (c : SystemChart n) : 4*c.radius.val*(8*c.M) ≤ (1 : Rat)/2 := by
  have hd : 0 < 32*(c.K+1) := Rat.mul_pos (by decide) (by have := c.nonnegK; grind)
  have he : c.radius.val*(32*(c.K+1))=1 := Rat.div_mul_cancel (Rat.ne_of_gt hd)
  have hpos := Rat.le_of_lt c.radius.property
  have hcoef : 32*c.M ≤ 16*(c.K+1) := by have := c.compatible; grind
  have hmul := Rat.mul_le_mul_of_nonneg_right hcoef hpos
  have he2 : 16*(c.K+1)*c.radius.val=(1 : Rat)/2 := by grind
  rw [he2] at hmul
  grind

end ComputableAnalysis.RiemannHilbert.SystemChart

namespace ComputableAnalysis.RiemannHilbert.ChartIntersection
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

def domain (c d : SystemChart n) (z : Scalar) : Prop := c.domain z ∧ d.domain z

def SameOperator (c d : SystemChart n) : Prop :=
  ∀ z (hc : c.domain z) (hd : d.domain z), (c.operator z hc).Equiv (d.operator z hd)

/-- Different centers and independently bounded coefficient presentations
give the same actual normalized holomorphic function on their intersection
when they describe the same coefficient operator there. -/
theorem through_agreement (c d : SystemChart n) (hA : SameOperator c d)
    (p : Scalar) (hc : c.domain p) (hd : d.domain p) (v : Fiber n)
    (q : Scalar) (hcq : c.domain q) (hdq : d.domain q) :
    c.through p hc v q hcq ≈ d.through p hd v q hdq := by
  let D := domain c d
  let f : UniformSegment.Field (n := n) D := fun z hz => c.through p hc v z hz.1
  let g : UniformSegment.Field (n := n) D := fun z hz => d.through p hd v z hz.2
  let A : UniformSegment.OperatorField (n := n) D := fun z hz => c.operator z hz.1
  let W : QPos := ⟨2*c.radius.val, Rat.mul_pos (by decide) c.radius.property⟩
  have hsmall : 2*W.val*(8*c.M) ≤ (1 : Rat)/2 := by
    have hs := c.diameter_small
    dsimp [W]
    grind
  refine UniformSegment.equal D p q ⟨hc,hd⟩ ⟨hcq,hdq⟩
    (fun t ht => ⟨AffineSegment.mem c.center p q c.radius.val hc hcq t ht,
      AffineSegment.mem d.center p q d.radius.val hd hdq t ht⟩)
    W (c.displacement_bound p q hc hcq) A f g (8*c.M)
    (4*initialBound (c.seed p hc v)) (4*initialBound (d.seed p hd v))
    (Rat.mul_nonneg (by decide) c.nonnegM) hsmall
    (Rat.mul_nonneg (by decide) (initialBound_nonneg (c.seed p hc v)))
    (Rat.mul_nonneg (by decide) (initialBound_nonneg (d.seed p hd v)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (c.delta (c.seed p hc v)) (d.delta (d.seed p hd v)) ?_ ?_
  · intro z w hz hw hzw
    exact c.through_congr p hc v v (Setoid.refl _) z w hzw hz.1 hw.1
  · intro z w hz hw hzw
    exact d.through_congr p hd v v (Setoid.refl _) z w hzw hz.2 hw.2
  · exact Setoid.trans (c.through_normalized p hc v) (Setoid.symm (d.through_normalized p hd v))
  · intro z hz; exact c.through_bound p hc v z hz.1
  · intro z hz; exact d.through_bound p hd v z hz.2
  · intro z hz; exact c.operator_linear z hz.1
  · intro z hz B hB x hx; exact c.operator_bound z hz.1 B hB x hx
  · intro eps H w z hw hz hH hzw
    exact c.value_uniform_remainder (c.seed p hc v) eps H w z hw.1 hz.1 hH hzw
  · intro eps H w z hw hz hH hzw
    have hs := d.value_uniform_remainder (d.seed p hd v) eps H w z hw.2 hz.2 hH hzw
    let displacement : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
    exact bound_congr (Fiber.sub_congr (Setoid.refl _)
      (Fiber.scale_congr (a := displacement) (b := displacement) (equiv_refl _ displacement.property)
        (Setoid.symm (hA w hw.1 hw.2 (d.through p hd v w hw.2))))) hs

theorem transport_agreement (c d : SystemChart n) (hA : SameOperator c d)
    (p q : Scalar) (hcp : c.domain p) (hdp : d.domain p) (hcq : c.domain q) (hdq : d.domain q) :
    (c.transport p q hcp hcq).toValueIso.forward.Equiv (d.transport p q hdp hdq).toValueIso.forward :=
  fun v => through_agreement c d hA p hcp hdp v q hcq hdq

theorem inverse_transport_agreement (c d : SystemChart n) (hA : SameOperator c d)
    (p q : Scalar) (hcp : c.domain p) (hdp : d.domain p) (hcq : c.domain q) (hdq : d.domain q) :
    (c.transport p q hcp hcq).toValueIso.backward.Equiv (d.transport p q hdp hdq).toValueIso.backward :=
  ValueIso.inverse_congr _ _ (transport_agreement c d hA p q hcp hdp hcq hdq)

end ComputableAnalysis.RiemannHilbert.ChartIntersection
