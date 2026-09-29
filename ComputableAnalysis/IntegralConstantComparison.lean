import ComputableAnalysis.IntegralUniformApproximation

/-! Exact constant comparisons for supplied justified integrals. These laws
use existing witnesses and do not impose an existence criterion on integrands. -/
namespace ComputableAnalysis.Integral

theorem HasIntegral.lower_const {F : FunctionOnInterval} {I : RealRaw}
    (hI : HasIntegral F I) {c : Rat}
    (hc : ∀ x (hx : inDomainInterval F.lower F.upper x) n, c ≤ (F.compute x hx n).hi) :
    (RealRaw.ofRat ((F.upper-F.lower)*c)).Le I := by
  obtain ⟨B,_⟩ := hI.tight ⟨1,by decide⟩
  let D : Bounds F := { B with lower := fun _ => c, lower_le := fun _ _ x hx n => hc x _ n }
  have he : D.lowerSum=(F.upper-F.lower)*c := by
    unfold Bounds.lowerSum
    change rectangleSum (fun k => (B.partition.point (k+1)-B.partition.point k)*c) B.partition.pieces = _
    rw [rectangleSum_scale,rectangleSum_telescope,B.partition.left_endpoint,B.partition.right_endpoint]
  intro n m
  have h := (hI.bounds D m).1
  rw [he] at h
  exact h

theorem HasIntegral.upper_const {F : FunctionOnInterval} {I : RealRaw}
    (hI : HasIntegral F I) {c : Rat}
    (hc : ∀ x (hx : inDomainInterval F.lower F.upper x) n, (F.compute x hx n).lo ≤ c) :
    I.Le (RealRaw.ofRat ((F.upper-F.lower)*c)) := by
  obtain ⟨B,_⟩ := hI.tight ⟨1,by decide⟩
  let D : Bounds F := { B with upper := fun _ => c, upper_ge := fun _ _ x hx n => hc x _ n }
  have he : D.upperSum=(F.upper-F.lower)*c := by
    unfold Bounds.upperSum
    change rectangleSum (fun k => (B.partition.point (k+1)-B.partition.point k)*c) B.partition.pieces = _
    rw [rectangleSum_scale,rectangleSum_telescope,B.partition.left_endpoint,B.partition.right_endpoint]
  intro n m
  have h := (hI.bounds D n).2
  rw [he] at h
  exact h

theorem HasIntegral.nonneg {F : FunctionOnInterval} {I : RealRaw}
    (hI : HasIntegral F I)
    (hf : ∀ x (hx : inDomainInterval F.lower F.upper x) n, 0 ≤ (F.compute x hx n).hi) : (RealRaw.ofRat 0).Le I := by
  have h := hI.lower_const hf
  rw [Rat.mul_zero] at h
  exact h

/-- Comparison with a represented constant lower bound. -/
theorem HasIntegral.lower_real {f : Rat → RealRaw} {a b : Rat}
    {hf : ∀ x, a ≤ x ∧ x ≤ b → (f x).Valid} {I C : RealRaw}
    (hI : HasIntegral (onInterval f a b hf) I) (hab : a ≤ b)
    (hC : ∀ x, a ≤ x → x ≤ b → C.Le (f x)) :
    (RealRaw.scaleRat (b-a) C).Le I := by
  intro n m
  have h := hI.lower_const (c := (C.compute n).lo) (by
    intro x hx k
    exact hC x hx.1 hx.2 n k)
  have hh := h n m
  have hnon : 0 ≤ b-a := by grind
  simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hnon]
  exact hh

/-- Comparison with a represented constant upper bound. -/
theorem HasIntegral.upper_real {f : Rat → RealRaw} {a b : Rat}
    {hf : ∀ x, a ≤ x ∧ x ≤ b → (f x).Valid} {I C : RealRaw}
    (hI : HasIntegral (onInterval f a b hf) I) (hab : a ≤ b)
    (hC : ∀ x, a ≤ x → x ≤ b → (f x).Le C) :
    I.Le (RealRaw.scaleRat (b-a) C) := by
  intro n m
  have h := hI.upper_const (c := (C.compute m).hi) (by
    intro x hx k
    exact hC x hx.1 hx.2 k m)
  have hh := h n m
  have hnon : 0 ≤ b-a := by grind
  simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hnon]
  exact hh

end ComputableAnalysis.Integral
