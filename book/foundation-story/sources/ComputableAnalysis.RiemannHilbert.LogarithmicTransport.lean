import ComputableAnalysis.RiemannHilbert.LogarithmicODEUniqueness
import ComputableAnalysis.RiemannHilbert.ExponentialAddition

/-! Constructed local transport and normalized solutions for A/z. Actual
holomorphicity, solution equations and uniform remainders are proved. A
supplied justified uniform solution is classified by its initial vector;
the frame and every comparison radius are constructed inside the proof. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField NonzeroBoxSearch
set_option maxHeartbeats 1000000
variable {n : Nat}

def transport (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p q : Scalar) (hp : RelativeLogarithm.domain c hc p) (hq : RelativeLogarithm.domain c hc q) : LinearIso n n :=
  (frame A hA c hc p hp).inverse.followedBy (frame A hA c hc q hq)

theorem transport_self (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) :
    (transport A hA c hc p p hp hp).toValueIso.forward.Equiv ValueMap.identity :=
  (frame A hA c hc p hp).toValueIso.forward_backward

theorem transport_comp (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p q r : Scalar) (hp : RelativeLogarithm.domain c hc p) (hq : RelativeLogarithm.domain c hc q)
    (hr : RelativeLogarithm.domain c hc r) :
    ((transport A hA c hc p q hp hq).toValueIso.forward.followedBy
      (transport A hA c hc q r hq hr).toValueIso.forward).Equiv (transport A hA c hc p r hp hr).toValueIso.forward :=
  fun x => (frame A hA c hc r hr).toValueIso.forward.congr
    ((frame A hA c hc q hq).toValueIso.backward_forward ((frame A hA c hc p hp).toValueIso.backward.eval x))

theorem transport_backward (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p q : Scalar) (hp : RelativeLogarithm.domain c hc p) (hq : RelativeLogarithm.domain c hc q) :
    (transport A hA c hc p q hp hq).toValueIso.backward.Equiv (transport A hA c hc q p hq hp).toValueIso.forward :=
  fun _ => Setoid.refl _

theorem transport_exponential_difference (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p q : Scalar) (hp : RelativeLogarithm.domain c hc p) (hq : RelativeLogarithm.domain c hc q) :
    (transport A hA c hc p q hp hq).toValueIso.forward.Equiv
      (MatrixExponential.value A hA
        ⟨sub ((RelativeLogarithm.function c hc).eval q hq).val ((RelativeLogarithm.function c hc).eval p hp).val,
          sub_valid ((RelativeLogarithm.function c hc).eval q hq).property ((RelativeLogarithm.function c hc).eval p hp).property⟩) := by
  intro x
  let lp := (RelativeLogarithm.function c hc).eval p hp
  let lq := (RelativeLogarithm.function c hc).eval q hq
  have hn := MatrixExponential.value_negative_parameter A hA lp x
  have ha := MatrixExponential.value_add A hA lq ⟨neg lp.val, neg_valid lp.property⟩ x
  exact Setoid.trans ((MatrixExponential.value A hA lq).congr (Setoid.symm hn))
    (Setoid.trans (Setoid.symm ha) (MatrixExponential.value_congr A A hA hA (fun _ => Setoid.refl _) _ _
      (add_comm_equiv _ _ (neg_valid lp.property) lq.property) x x (Setoid.refl _)))

theorem transport_names_congr (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (hAB : A.Equiv B)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (hcd : c.val.Equiv d.val)
    (p p' q q' : Scalar) (hp : RelativeLogarithm.domain c hc p) (hp' : RelativeLogarithm.domain d hd p')
    (hq : RelativeLogarithm.domain c hc q) (hq' : RelativeLogarithm.domain d hd q')
    (hpp : p.val.Equiv p'.val) (hqq : q.val.Equiv q'.val) :
    (transport A hA c hc p q hp hq).toValueIso.forward.Equiv (transport B hB d hd p' q' hp' hq').toValueIso.forward :=
  ValueMap.followedBy_congr (inverse_names_congr A B hA hB hAB c d hc hd hcd p p' hp hp' hpp)
    (frame_names_congr A B hA hB hAB c d hc hd hcd q q' hq hq' hqq)

def solution (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n) : DomainVectorFunctions.Map n :=
  vector A hA c hc ((frame A hA c hc p hp).toValueIso.backward.eval x)

def solution_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (solution A hA c hc p hp x) :=
  vector_holomorphic A hA c hc _

theorem solution_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n) :
    (solution A hA c hc p hp x).eval p hp ≈ x := (frame A hA c hc p hp).toValueIso.forward_backward x

theorem solution_ode (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n)
    (hH : DomainVectorFunctions.Holomorphic (solution A hA c hc p hp x))
    (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    DomainVectorFunctions.derivative (solution A hA c hc p hp x) hH z hz ≈
      (operator A c hc z hz).eval ((solution A hA c hc p hp x).eval z hz) :=
  vector_derivative_ode A hA c hc _ hH z hz

theorem solution_transport (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p q : Scalar) (hp : RelativeLogarithm.domain c hc p) (hq : RelativeLogarithm.domain c hc q) (x : Fiber n) :
    (solution A hA c hc p hp x).eval q hq ≈ (transport A hA c hc p q hp hq).toValueIso.forward.eval x := Setoid.refl _

def solutionBound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n) : Rat :=
  valueBound A*initialBound ((frame A hA c hc p hp).toValueIso.backward.eval x)

theorem solutionBound_nonneg (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n) : 0 ≤ solutionBound A hA c hc p hp x :=
  Rat.mul_nonneg (valueBound_nonneg A) (LocalSystem.initialBound_nonneg _)

theorem solution_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n) (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    CoordinateBound ((solution A hA c hc p hp x).eval z hz) (solutionBound A hA c hc p hp x) :=
  forward_bound A hA c hc z hz _ (LocalSystem.initialBound_nonneg _) _ (LocalSystem.initialBound_valid _)

def solutionDelta (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n) (eps : QPos) : QPos :=
  uniformDelta A c hc ⟨eps.val/(initialBound ((frame A hA c hc p hp).toValueIso.backward.eval x)+1), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by have := LocalSystem.initialBound_nonneg ((frame A hA c hc p hp).toValueIso.backward.eval x); grind only))⟩

theorem solution_uniform_remainder (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p : Scalar) (hp : RelativeLogarithm.domain c hc p) (x : Fiber n) (eps H : QPos)
    (w z : Scalar) (hw : RelativeLogarithm.domain c hc w) (hz : RelativeLogarithm.domain c hc z)
    (hH : H.val ≤ (solutionDelta A hA c hc p hp x eps).val) (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (UniformSegment.remainder (operator A c hc) (solution A hA c hc p hp x).eval w z hw hz) (eps.val*H.val) := by
  let y := (frame A hA c hc p hp).toValueIso.backward.eval x
  let E := initialBound y
  have hE : 0 ≤ E := LocalSystem.initialBound_nonneg y
  let eta : QPos := ⟨eps.val/(E+1), by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by grind only))⟩
  have hb := forward_uniform_remainder A hA c hc eta H w z hw hz hH hzw E hE y (LocalSystem.initialBound_valid y)
  have he : operatorRemainder (forwardField (frame A hA c hc)) (slope A hA c hc) w z hw hz y ≈
      UniformSegment.remainder (operator A c hc) (solution A hA c hc p hp x).eval w z hw hz :=
    Fiber.sub_congr (Setoid.refl _)
      (Fiber.scale_congr (equiv_refl _ (sub_valid z.property w.property)) (slope_ode A hA c hc w hw y))
  have hs := bound_congr he hb
  have hid : eta.val*(E+1)=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt (by grind only))
  have heps : eta.val*E ≤ eps.val := by have := eta.property; grind only
  have hm := Rat.mul_le_mul_of_nonneg_right heps (Rat.le_of_lt H.property)
  intro i
  apply (hs i).mono
  calc
    (eta.val*H.val)*E=(eta.val*E)*H.val := by grind only
    _ ≤ eps.val*H.val := hm

/-- Every supplied uniform solution agrees with the constructed local
transport of its initial value. The hypotheses certify the supplied field's
equation and convergence; the asserted endpoint identity is proved. -/
theorem classify_uniform_solution (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (c : Scalar) (hc : Nonzero c)
    (p q : Scalar) (hp : RelativeLogarithm.domain c hc p) (hq : RelativeLogarithm.domain c hc q)
    (f : UniformSegment.Field (n := n) (RelativeLogarithm.domain c hc)) (B : Rat) (hB : 0 ≤ B)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hfB : ∀ z hz, CoordinateBound (f z hz) B) (deltaF : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val → Small (sub z.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (operator A c hc) f w z hw hz) (eps.val*H.val)) :
    f q hq ≈ (transport A hA c hc p q hp hq).toValueIso.forward.eval (f p hp) := by
  have he := ode_equal A hA c hc p q hp hq f (solution A hA c hc p hp (f p hp)).eval
    B (solutionBound A hA c hc p hp (f p hp)) hB (solutionBound_nonneg A hA c hc p hp (f p hp))
    hfcongr (solution A hA c hc p hp (f p hp)).eval_congr
    (Setoid.symm (solution_initial A hA c hc p hp (f p hp))) hfB
    (solution_bound A hA c hc p hp (f p hp)) deltaF (solutionDelta A hA c hc p hp (f p hp))
    hfrem (solution_uniform_remainder A hA c hc p hp (f p hp))
  exact Setoid.trans he (solution_transport A hA c hc p q hp hq (f p hp))

end ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
