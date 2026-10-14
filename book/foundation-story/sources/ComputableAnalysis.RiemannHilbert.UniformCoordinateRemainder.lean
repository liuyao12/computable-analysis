import ComputableAnalysis.RiemannHilbert.CoordinatePullbackChart
import ComputableAnalysis.RiemannHilbert.LinearFieldProductBounds

/-! Uniform first-order errors for actual coordinate-pulled chart solutions.
Finite chain-rule algebra separates the old solution error from the scalar
coordinate error. A rational modulus is constructed from the justified input
moduli and bounds; horizontality or transport agreement is not assumed. -/
namespace ComputableAnalysis.RiemannHilbert.UniformCoordinate
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

theorem remainder_algebra (x y v : Fiber n) (h dg imageDelta : Scalar) :
    Fiber.sub (Fiber.sub x y) (Fiber.scale h (Fiber.scale dg v)) ≈
      Fiber.add (Fiber.sub (Fiber.sub x y) (Fiber.scale imageDelta v))
        (Fiber.scale ⟨sub imageDelta.val (mul dg.val h.val),
          sub_valid imageDelta.property (mul_valid dg.property h.property)⟩ v) := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Fiber.sub (Fiber.sub x y) (Fiber.scale h (Fiber.scale dg v))).property i)
    (hright := (Fiber.add (Fiber.sub (Fiber.sub x y) (Fiber.scale imageDelta v))
      (Fiber.scale ⟨sub imageDelta.val (mul dg.val h.val),
        sub_valid imageDelta.property (mul_valid dg.property h.property)⟩ v)).property i)
  let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
  let Y := ComplexRawQuotient.ofRaw (y.val i) (y.property i)
  let V := ComplexRawQuotient.ofRaw (v.val i) (v.property i)
  let H := ComplexRawQuotient.ofRaw h.val h.property
  let G := ComplexRawQuotient.ofRaw dg.val dg.property
  let D := ComplexRawQuotient.ofRaw imageDelta.val imageDelta.property
  change (X-Y)-H*(G*V)=((X-Y)-D*V)+(D-G*H)*V
  grind only

def scaledRadius (L : Rat) (hL : 0 ≤ L) (r : QPos) : QPos :=
  ⟨r.val/(L+1), by rw [Rat.div_def]; exact Rat.mul_pos r.property ((Rat.inv_pos).2 (by grind only))⟩

theorem scaledRadius_bound (L : Rat) (hL : 0 ≤ L) (r H : QPos)
    (hH : H.val ≤ (scaledRadius L hL r).val) : (L+1)*H.val ≤ r.val := by
  have hs := Rat.mul_le_mul_of_nonneg_left hH (show 0 ≤ L+1 by grind only)
  have he : (L+1)*(scaledRadius L hL r).val=r.val := by
    unfold scaledRadius
    rw [Rat.mul_comm]
    exact Rat.div_mul_cancel (Rat.ne_of_gt (show 0 < L+1 by grind only))
  rw [he] at hs
  exact hs

def errorShare (L K : Rat) (hL : 0 ≤ L) (hK : 0 ≤ K) (eps : QPos) : QPos :=
  LinearField.errorShare (L+1) (2*K) (by grind only) (Rat.mul_nonneg (by decide +kernel) hK) eps

theorem error_budget (L K : Rat) (hL : 0 ≤ L) (hK : 0 ≤ K) (eps H : QPos) :
    (errorShare L K hL hK eps).val*((L+1)*H.val)+
      2*((errorShare L K hL hK eps).val*H.val)*K ≤ eps.val*H.val := by
  let eta := errorShare L K hL hK eps
  have he : eta.val*(4*((L+1)+2*K+1))=eps.val :=
    Rat.div_mul_cancel (Rat.ne_of_gt (show 0 < 4*((L+1)+2*K+1) by grind only))
  have hEta := Rat.le_of_lt eta.property
  have hH := Rat.le_of_lt H.property
  have hm := Rat.mul_le_mul_of_nonneg_right
    (show (L+1)+2*K ≤ 4*((L+1)+2*K+1) by grind only) hEta
  have hs := Rat.mul_le_mul_of_nonneg_right hm hH
  change eta.val*((L+1)*H.val)+2*(eta.val*H.val)*K ≤ eps.val*H.val
  calc
    _ = ((L+1)+2*K)*eta.val*H.val := by grind only
    _ ≤ 4*((L+1)+2*K+1)*eta.val*H.val := hs
    _ = eps.val*H.val := by rw [Rat.mul_comm (4*((L+1)+2*K+1)) eta.val, he]

def derivativeBound (c : SystemChart n) (initial : Fiber n) : Rat := (8*c.M)*(4*initialBound initial)

theorem derivativeBound_nonneg (c : SystemChart n) (initial : Fiber n) : 0 ≤ derivativeBound c initial :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) c.nonnegM)
    (Rat.mul_nonneg (by decide +kernel) (initialBound_nonneg initial))

def delta (c : SystemChart n) (initial : Fiber n) (L : Rat) (hL : 0 ≤ L)
    (deltaG : QPos → QPos) (eps : QPos) : QPos :=
  let eta := errorShare L (derivativeBound c initial) hL (derivativeBound_nonneg c initial) eps
  smallerRadius (scaledRadius L hL (c.delta initial eta)) (deltaG eta)

theorem pulled_remainder (c : SystemChart n) (initial : Fiber n) (g : DomainFunctions.Map)
    (hg : DomainFunctions.Holomorphic g) (L : Rat) (hL : 0 ≤ L)
    (hLip : ∀ w z (hw : CoordinatePullbackChart.domain c g w) (hz : CoordinatePullbackChart.domain c g z)
      (H : QPos), Small (sub z.val w.val) H.val →
      Small (sub (g.eval z (CoordinatePullbackChart.inner_mem hz)).val
        (g.eval w (CoordinatePullbackChart.inner_mem hw)).val) (L*H.val))
    (deltaG : QPos → QPos)
    (hGrem : ∀ (eps H : QPos) w z (hw : CoordinatePullbackChart.domain c g w)
      (hz : CoordinatePullbackChart.domain c g z), H.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) H.val →
      Small (sub (sub (g.eval z (CoordinatePullbackChart.inner_mem hz)).val
        (g.eval w (CoordinatePullbackChart.inner_mem hw)).val)
        (mul (hg.derivative w (CoordinatePullbackChart.inner_mem hw)).val (sub z.val w.val))) (eps.val*H.val))
    (eps H : QPos) (w z : Scalar) (hw : CoordinatePullbackChart.domain c g w)
    (hz : CoordinatePullbackChart.domain c g z) (hH : H.val ≤ (delta c initial L hL deltaG eps).val)
    (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (UniformSegment.remainder (CoordinatePullbackChart.coefficient c g hg)
      (fun z hz => (CoordinatePullbackChart.pulledSolution c initial g).eval z hz) w z hw hz) (eps.val*H.val) := by
  let eta := errorShare L (derivativeBound c initial) hL (derivativeBound_nonneg c initial) eps
  let step : QPos := ⟨(L+1)*H.val, Rat.mul_pos (by grind only) H.property⟩
  let gw := g.eval w (CoordinatePullbackChart.inner_mem hw)
  let gz := g.eval z (CoordinatePullbackChart.inner_mem hz)
  let cw := CoordinatePullbackChart.image_mem hw
  let cz := CoordinatePullbackChart.image_mem hz
  have hF : step.val ≤ (c.delta initial eta).val :=
    scaledRadius_bound L hL _ H (Rat.le_trans hH (smallerRadius_le_left _ _))
  have hG : H.val ≤ (deltaG eta).val := Rat.le_trans hH (smallerRadius_le_right _ _)
  have hImage : Small (sub gz.val gw.val) step.val := (hLip w z hw hz H hzw).mono (by
    dsimp [step]; have h := H.property; grind only)
  have h1 := c.value_uniform_remainder initial eta step gw gz cw cz hF hImage
  have h2 := bound_scale (c := ⟨sub (sub gz.val gw.val)
      (mul (hg.derivative w (CoordinatePullbackChart.inner_mem hw)).val (sub z.val w.val)),
      sub_valid (sub_valid gz.property gw.property)
        (mul_valid (hg.derivative w (CoordinatePullbackChart.inner_mem hw)).property (sub_valid z.property w.property))⟩)
    (x := (c.operator gw cw).eval (c.value initial gw cw))
    (Rat.mul_nonneg (Rat.le_of_lt eta.property) (Rat.le_of_lt H.property))
    (derivativeBound_nonneg c initial) (hGrem eta H w z hw hz hG hzw)
    (c.operator_bound gw cw (4*initialBound initial)
      (Rat.mul_nonneg (by decide +kernel) (initialBound_nonneg initial)) _ (c.value_bound initial gw cw))
  have hs := bound_congr (Setoid.symm (remainder_algebra (c.value initial gz cz) (c.value initial gw cw)
    ((c.operator gw cw).eval (c.value initial gw cw))
    ⟨sub z.val w.val, sub_valid z.property w.property⟩
    (hg.derivative w (CoordinatePullbackChart.inner_mem hw))
    ⟨sub gz.val gw.val, sub_valid gz.property gw.property⟩)) (bound_add h1 h2)
  intro i
  exact (hs i).mono (error_budget L (derivativeBound c initial) hL (derivativeBound_nonneg c initial) eps H)

end ComputableAnalysis.RiemannHilbert.UniformCoordinate
