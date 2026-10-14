import ComputableAnalysis.ModularForms.PairedRiccatiDerivativeRectangleVariation
import ComputableAnalysis.ModularForms.PairedRiccatiRectangleLinearization

/-! Uniform fine cells lie in actual derivative-continuity neighborhoods.
Unlike variation-only covers, these retain spatial neighborhood evidence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

inductive RectangleContinuityNeighborhoodCover (g : Scalar → Scalar)
    (hc : ContinuousOn (fun _ : Scalar => True) (fun a _ => g a)) (eps : QPos) :
    QInterval × QInterval → Prop
  | neighborhood (J : QInterval × QInterval) (a : Scalar)
      (bound : ∀ q : QComplex, rationalRectangleContains J q →
        Small (sub (ofQComplex q) a.val) (hc.delta a trivial eps).val) :
      RectangleContinuityNeighborhoodCover g hc eps J
  | split (J : QInterval × QInterval)
      (ll : RectangleContinuityNeighborhoodCover g hc eps (bisectRectangle J (false,false)))
      (lr : RectangleContinuityNeighborhoodCover g hc eps (bisectRectangle J (false,true)))
      (rl : RectangleContinuityNeighborhoodCover g hc eps (bisectRectangle J (true,false)))
      (rr : RectangleContinuityNeighborhoodCover g hc eps (bisectRectangle J (true,true))) :
      RectangleContinuityNeighborhoodCover g hc eps J

theorem continuous_rectangle_neighborhood_cover (g : Scalar → Scalar)
    (hc : ContinuousOn (fun _ : Scalar => True) (fun a _ => g a))
    (eps : QPos) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) : RectangleContinuityNeighborhoodCover g hc eps J := by
  apply represented_rectangle_cover (RectangleContinuityNeighborhoodCover g hc eps) J hX hY
  · intro K ll lr rl rr
    exact RectangleContinuityNeighborhoodCover.split K ll lr rl rr
  · intro x y hx hy hxl hxu hyl hyu
    let a : Scalar := ⟨coordinateComplex x y,coordinateComplex_valid x y hx hy⟩
    let H := hc.delta a trivial eps
    refine ⟨H, ?_⟩
    intro K hKx hKy
    apply RectangleContinuityNeighborhoodCover.neighborhood K a
    intro q hq
    exact rectangleNear_complex_displacement K x y H hKx hKy q hq

def rectangleContinuityNeighborhood (g : Scalar → Scalar)
    (hc : ContinuousOn (fun _ : Scalar => True) (fun a _ => g a)) (eps : QPos)
    (J : QInterval × QInterval) : Prop :=
  ∃ a : Scalar, ∀ q : QComplex, rationalRectangleContains J q →
    Small (sub (ofQComplex q) a.val) (hc.delta a trivial eps).val

theorem rectangleContinuityNeighborhood_uniform_depth (g : Scalar → Scalar)
    (hc : ContinuousOn (fun _ : Scalar => True) (fun a _ => g a)) (eps : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (cover : RectangleContinuityNeighborhoodCover g hc eps J) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      rectangleContinuityNeighborhood g hc eps (rectangleBisection J choice n) := by
  induction cover with
  | neighborhood J a hc =>
    refine ⟨0, ?_⟩
    intro choice n hn
    exact ⟨a,fun q hq => hc q (rectangleBisection_contains_initial J hX hY choice n q hq)⟩
  | split J ll lr rl rr ill ilr irl irr =>
    have ho (r s : Bool) :
        (bisectRectangle J (r,s)).1.lo≤(bisectRectangle J (r,s)).1.hi ∧
        (bisectRectangle J (r,s)).2.lo≤(bisectRectangle J (r,s)).2.hi :=
      ⟨(bisectInterval_bounds J.1 hX r).2.1,(bisectInterval_bounds J.2 hY s).2.1⟩
    obtain ⟨LL,hLL⟩ := ill (ho false false).1 (ho false false).2
    obtain ⟨LR,hLR⟩ := ilr (ho false true).1 (ho false true).2
    obtain ⟨RL,hRL⟩ := irl (ho true false).1 (ho true false).2
    obtain ⟨RR,hRR⟩ := irr (ho true true).1 (ho true true).2
    refine ⟨max (max LL LR) (max RL RR)+1, ?_⟩
    intro choice n hn
    have hnpos : 0<n := by omega
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    subst n
    rw [rectangleBisection_shift]
    have hp : choice 0=((choice 0).1,(choice 0).2) := rfl
    rw [hp]
    cases hx : (choice 0).1 <;> cases hy : (choice 0).2
    · exact hLL (fun k => choice (k+1)) m (by omega)
    · exact hLR (fun k => choice (k+1)) m (by omega)
    · exact hRL (fun k => choice (k+1)) m (by omega)
    · exact hRR (fun k => choice (k+1)) m (by omega)

theorem pairedRiccati_uniform_derivative_neighborhoods (eps : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      ∃ a : Scalar, ∀ q : QComplex,
        rationalRectangleContains (rectangleBisection J choice n) q →
        Small (sub (ofQComplex q) a.val)
          (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val :=
  rectangleContinuityNeighborhood_uniform_depth pairedRiccatiDerivativeValue
    pairedEntireRiccatiMap_holomorphic.continuousDerivative eps J hX hY
    (continuous_rectangle_neighborhood_cover pairedRiccatiDerivativeValue
      pairedEntireRiccatiMap_holomorphic.continuousDerivative eps J hX hY)

theorem pairedRiccati_uniform_cell_linearization (eps : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      ∃ a : Scalar, ∀ p q : QComplex, ∀ W : QPos,
        rationalRectangleContains (rectangleBisection J choice n) p →
        rationalRectangleContains (rectangleBisection J choice n) q →
        Small (sub (ofQComplex q) (ofQComplex p)) W.val →
        Small (remainder pairedEntireRiccatiMap
          ⟨ofQComplex p,ofQComplex_valid _⟩ trivial
          (pairedEntireRiccatiMap_holomorphic.derivative a trivial)
          ⟨ofQComplex q,ofQComplex_valid _⟩ trivial) (4*eps.val*W.val) := by
  obtain ⟨N,hN⟩ := pairedRiccati_uniform_derivative_neighborhoods eps J hX hY
  refine ⟨N, ?_⟩
  intro choice n hn
  obtain ⟨a,ha⟩ := hN choice n hn
  refine ⟨a, ?_⟩
  intro p q W hp hq hd
  exact pairedRiccati_neighborhood_linearization a
    ⟨ofQComplex p,ofQComplex_valid _⟩ ⟨ofQComplex q,ofQComplex_valid _⟩ W eps hd
    (ha p hp) (ha q hq)

end ComputableAnalysis.ModularForms
