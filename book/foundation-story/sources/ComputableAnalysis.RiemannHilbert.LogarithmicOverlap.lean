import ComputableAnalysis.RiemannHilbert.LogarithmicTransport

/-! Actual independence of normalized local transport on chart overlaps.
Every overlap contains the affine segment between its points. Constructed
solution estimates and proved uniqueness identify both transports; no branch
comparison or constant transition matrix is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField NonzeroBoxSearch
set_option maxHeartbeats 1000000
variable {n : Nat}

def overlap (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (z : Scalar) : Prop :=
  RelativeLogarithm.domain c hc z ∧ RelativeLogarithm.domain d hd z

theorem overlap_affine_mem (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d)
    (p q : Scalar) (hp : overlap c d hc hd p) (hq : overlap c d hc hd q)
    (t : Rat) (ht : UniformPath.unitInterval t) : overlap c d hc hd (AffineSegment.point p q t) :=
  ⟨RelativeLogarithm.affine_mem c hc p q hp.1 hq.1 t ht, RelativeLogarithm.affine_mem d hd p q hp.2 hq.2 t ht⟩

theorem transport_overlap (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (p q : Scalar)
    (hp : overlap c d hc hd p) (hq : overlap c d hc hd q) :
    (transport A hA c hc p q hp.1 hq.1).toValueIso.forward.Equiv
      (transport A hA d hd p q hp.2 hq.2).toValueIso.forward := by
  intro x
  let f : UniformSegment.Field (n := n) (overlap c d hc hd) := fun z hz => (solution A hA c hc p hp.1 x).eval z hz.1
  let g : UniformSegment.Field (n := n) (overlap c d hc hd) := fun z hz => (solution A hA d hd p hp.2 x).eval z hz.2
  have he := ode_equal_on A hA c hc (overlap c d hc hd) (fun _ hz => hz.1) p q hp hq
    (overlap_affine_mem c d hc hd p q hp hq) f g
    (solutionBound A hA c hc p hp.1 x) (solutionBound A hA d hd p hp.2 x)
    (solutionBound_nonneg A hA c hc p hp.1 x) (solutionBound_nonneg A hA d hd p hp.2 x)
    (fun z w hz hw hzw => (solution A hA c hc p hp.1 x).eval_congr z w hz.1 hw.1 hzw)
    (fun z w hz hw hzw => (solution A hA d hd p hp.2 x).eval_congr z w hz.2 hw.2 hzw)
    (Setoid.trans (solution_initial A hA c hc p hp.1 x) (Setoid.symm (solution_initial A hA d hd p hp.2 x)))
    (fun z hz => solution_bound A hA c hc p hp.1 x z hz.1)
    (fun z hz => solution_bound A hA d hd p hp.2 x z hz.2)
    (solutionDelta A hA c hc p hp.1 x) (solutionDelta A hA d hd p hp.2 x)
    (fun eps H w z hw hz => solution_uniform_remainder A hA c hc p hp.1 x eps H w z hw.1 hz.1)
    (fun eps H w z hw hz => solution_uniform_remainder A hA d hd p hp.2 x eps H w z hw.2 hz.2)
  exact Setoid.trans (Setoid.symm (solution_transport A hA c hc p q hp.1 hq.1 x))
    (Setoid.trans he (solution_transport A hA d hd p q hp.2 hq.2 x))

theorem transport_backward_overlap (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (p q : Scalar)
    (hp : overlap c d hc hd p) (hq : overlap c d hc hd q) :
    (transport A hA c hc p q hp.1 hq.1).toValueIso.backward.Equiv
      (transport A hA d hd p q hp.2 hq.2).toValueIso.backward :=
  ValueIso.inverse_congr _ _ (transport_overlap A hA c d hc hd p q hp hq)

def transition (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (z : Scalar) (hz : overlap c d hc hd z) : LinearIso n n :=
  (frame A hA c hc z hz.1).followedBy (frame A hA d hd z hz.2).inverse

theorem transition_constant (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d : Scalar) (hc : Nonzero c) (hd : Nonzero d) (p q : Scalar)
    (hp : overlap c d hc hd p) (hq : overlap c d hc hd q) :
    (transition A hA c d hc hd q hq).toValueIso.forward.Equiv (transition A hA c d hc hd p hp).toValueIso.forward := by
  intro x
  let y := (frame A hA c hc p hp.1).toValueIso.forward.eval x
  have hf : (transport A hA c hc p q hp.1 hq.1).toValueIso.forward.eval y ≈
      (frame A hA c hc q hq.1).toValueIso.forward.eval x :=
    (frame A hA c hc q hq.1).toValueIso.forward.congr ((frame A hA c hc p hp.1).toValueIso.backward_forward x)
  have he := transport_overlap A hA c d hc hd p q hp hq y
  exact Setoid.trans ((frame A hA d hd q hq.2).toValueIso.backward.congr (Setoid.symm hf))
    (Setoid.trans ((frame A hA d hd q hq.2).toValueIso.backward.congr he)
      ((frame A hA d hd q hq.2).toValueIso.backward_forward
        ((frame A hA d hd p hp.2).toValueIso.backward.eval y)))

theorem transition_self (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c : Scalar) (hc : Nonzero c) (z : Scalar) (hz : RelativeLogarithm.domain c hc z) :
    (transition A hA c c hc hc z ⟨hz,hz⟩).toValueIso.forward.Equiv ValueMap.identity :=
  (frame A hA c hc z hz).toValueIso.backward_forward

theorem transition_cocycle (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (c d e : Scalar) (hc : Nonzero c) (hd : Nonzero d) (he : Nonzero e)
    (z : Scalar) (hzc : RelativeLogarithm.domain c hc z) (hzd : RelativeLogarithm.domain d hd z)
    (hze : RelativeLogarithm.domain e he z) :
    ((transition A hA c d hc hd z ⟨hzc,hzd⟩).toValueIso.forward.followedBy
      (transition A hA d e hd he z ⟨hzd,hze⟩).toValueIso.forward).Equiv
      (transition A hA c e hc he z ⟨hzc,hze⟩).toValueIso.forward :=
  fun x => (frame A hA e he z hze).toValueIso.backward.congr
    ((frame A hA d hd z hzd).toValueIso.forward_backward ((frame A hA c hc z hzc).toValueIso.forward.eval x))

end ComputableAnalysis.RiemannHilbert.LogarithmicLocalModel
