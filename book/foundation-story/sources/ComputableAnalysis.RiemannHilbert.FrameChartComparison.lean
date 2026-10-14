import ComputableAnalysis.RiemannHilbert.ConnectionFrameChange
import ComputableAnalysis.RiemannHilbert.ChartIntersectionAgreement

/-! Comparing actual chart solutions through a varying horizontal linear
map. The proof derives the product derivative errors and uses covered-segment
uniqueness; transport naturality is a conclusion, not input transition data. -/
namespace ComputableAnalysis.RiemannHilbert.FrameComparison
open ComplexRaw FunctionTheory LocalODE LocalSystem LinearField
variable {n m : Nat}

def domain (c : SystemChart n) (d : SystemChart m) (z : Scalar) : Prop := c.domain z ∧ d.domain z

theorem through_agreement (c : SystemChart n) (d : SystemChart m)
    (G DG : LinearField.Field (n := n) (m := m) (domain c d))
    (hlinear : ∀ z hz, IsLinear (G z hz))
    (hcongr : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (hcompat : LinearField.Compatible G DG (fun z hz => c.operator z hz.1) (fun z hz => d.operator z hz.2))
    (P Q : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((G z hz).eval x) (P*E))
    (hDGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((DG z hz).eval x) (Q*E))
    (deltaG : QPos → QPos)
    (hGrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) H.val → ∀ E, 0 ≤ E → ∀ x, CoordinateBound x E →
        CoordinateBound (LinearField.operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*E))
    (p q : Scalar) (hcp : c.domain p) (hdp : d.domain p) (hcq : c.domain q) (hdq : d.domain q) (v : Fiber n) :
    (G q ⟨hcq,hdq⟩).eval (c.through p hcp v q hcq) ≈
      d.through p hdp ((G p ⟨hcp,hdp⟩).eval v) q hdq := by
  let D := domain c d
  let old : UniformSegment.Field (n := n) D := fun z hz => c.through p hcp v z hz.1
  let A : UniformSegment.OperatorField (n := n) D := fun z hz => c.operator z hz.1
  let Bop : UniformSegment.OperatorField (n := m) D := fun z hz => d.operator z hz.2
  let seedValue := (G p ⟨hcp,hdp⟩).eval v
  let target : UniformSegment.Field (n := m) D := fun z hz => d.through p hdp seedValue z hz.2
  let B := 4*initialBound (c.seed p hcp v)
  let C := 4*initialBound (d.seed p hdp seedValue)
  let U := 8*c.M
  have hB : 0 ≤ B := Rat.mul_nonneg (by decide) (initialBound_nonneg (c.seed p hcp v))
  have hC : 0 ≤ C := Rat.mul_nonneg (by decide) (initialBound_nonneg (d.seed p hdp seedValue))
  have hU : 0 ≤ U := Rat.mul_nonneg (by decide) c.nonnegM
  let deltaF := c.delta (c.seed p hcp v)
  let deltaProd := LinearField.productDelta P Q B (U*B) hP hQ hB (Rat.mul_nonneg hU hB) deltaF deltaG
  let W : QPos := ⟨2*d.radius.val, Rat.mul_pos (by decide) d.radius.property⟩
  have hsmall : 2*W.val*(8*d.M) ≤ (1 : Rat)/2 := by
    have hs := d.diameter_small
    dsimp [W]
    grind
  refine UniformSegment.equal D p q ⟨hcp,hdp⟩ ⟨hcq,hdq⟩
    (fun t ht => ⟨AffineSegment.mem c.center p q c.radius.val hcp hcq t ht,
      AffineSegment.mem d.center p q d.radius.val hdp hdq t ht⟩)
    W (d.displacement_bound p q hdp hdq) Bop (LinearField.product G old) target
    (8*d.M) (P*B) C (Rat.mul_nonneg (by decide) d.nonnegM) hsmall
    (Rat.mul_nonneg hP hB) hC ?_ ?_ ?_ ?_ ?_ ?_ ?_ deltaProd (d.delta (d.seed p hdp seedValue)) ?_ ?_
  · exact LinearField.product_congr G old hcongr
      (fun z w hz hw hzw => c.through_congr p hcp v v (Setoid.refl _) z w hzw hz.1 hw.1)
  · intro z w hz hw hzw
    exact d.through_congr p hdp seedValue seedValue (Setoid.refl _) z w hzw hz.2 hw.2
  · exact Setoid.trans ((G p ⟨hcp,hdp⟩).congr (c.through_normalized p hcp v))
      (Setoid.symm (d.through_normalized p hdp seedValue))
  · intro z hz
    exact hGbound z hz B hB (old z hz) (c.through_bound p hcp v z hz.1)
  · intro z hz
    exact d.through_bound p hdp seedValue z hz.2
  · intro z hz
    exact d.operator_linear z hz.2
  · intro z hz E hE x hx
    exact d.operator_bound z hz.2 E hE x hx
  · intro eps H w z hw hz hH hzw
    exact LinearField.horizontal_product_remainder G DG A Bop old hlinear hcompat P Q U B hP hQ hU hB
      hGbound hDGbound (fun z hz E hE x hx => c.operator_bound z hz.1 E hE x hx)
      (fun z hz => c.through_bound p hcp v z hz.1)
      deltaF deltaG
      (fun eps H w z hw hz hH hzw => c.value_uniform_remainder (c.seed p hcp v) eps H w z hw.1 hz.1 hH hzw)
      hGrem eps H w z hw hz hH hzw
  · intro eps H w z hw hz hH hzw
    exact d.value_uniform_remainder (d.seed p hdp seedValue) eps H w z hw.2 hz.2 hH hzw

theorem transport_natural (c : SystemChart n) (d : SystemChart m)
    (G DG : LinearField.Field (n := n) (m := m) (domain c d))
    (hlinear : ∀ z hz, IsLinear (G z hz))
    (hcongr : ∀ z w hz hw, z.val.Equiv w.val → (G z hz).Equiv (G w hw))
    (hcompat : LinearField.Compatible G DG (fun z hz => c.operator z hz.1) (fun z hz => d.operator z hz.2))
    (P Q : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((G z hz).eval x) (P*E))
    (hDGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((DG z hz).eval x) (Q*E))
    (deltaG : QPos → QPos)
    (hGrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) H.val → ∀ E, 0 ≤ E → ∀ x, CoordinateBound x E →
        CoordinateBound (LinearField.operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*E))
    (p q : Scalar) (hcp : c.domain p) (hdp : d.domain p) (hcq : c.domain q) (hdq : d.domain q) :
    ((G p ⟨hcp,hdp⟩).followedBy (d.transport p q hdp hdq).toValueIso.forward).Equiv
      ((c.transport p q hcp hcq).toValueIso.forward.followedBy (G q ⟨hcq,hdq⟩)) :=
  fun v => Setoid.symm (through_agreement c d G DG hlinear hcongr hcompat P Q hP hQ hGbound hDGbound deltaG hGrem
    p q hcp hdp hcq hdq v)

end ComputableAnalysis.RiemannHilbert.FrameComparison
