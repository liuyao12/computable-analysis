import ComputableAnalysis.RiemannHilbert.ContourSegmentBisection

/-! Finite derivative-continuity neighborhoods derived from actual holomorphicity. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

def domainDerivativeRadius (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) : QPos :=
  minRadius (hf.openDomain.radius a ha) (hf.continuousDerivative.delta a ha eps)

inductive DomainRectangleNeighborhoodCover (f : DomainFunctions.Map) (hf : Holomorphic f) (eps : QPos) :
    QInterval × QInterval → Prop
  | neighborhood (J : QInterval × QInterval) (a : Scalar) (ha : f.domain a)
      (bound : ∀ q : QComplex, rationalRectangleContains J q →
        Small (sub (ofQComplex q) a.val) (domainDerivativeRadius f hf a ha eps).val) :
      DomainRectangleNeighborhoodCover f hf eps J
  | split (J : QInterval × QInterval)
      (ll : DomainRectangleNeighborhoodCover f hf eps (bisectRectangle J (false,false)))
      (lr : DomainRectangleNeighborhoodCover f hf eps (bisectRectangle J (false,true)))
      (rl : DomainRectangleNeighborhoodCover f hf eps (bisectRectangle J (true,false)))
      (rr : DomainRectangleNeighborhoodCover f hf eps (bisectRectangle J (true,true))) :
      DomainRectangleNeighborhoodCover f hf eps J

theorem domain_rectangle_neighborhood_cover (f : DomainFunctions.Map) (hf : Holomorphic f)
    (eps : QPos) (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z) :
    DomainRectangleNeighborhoodCover f hf eps J := by
  apply represented_rectangle_cover (DomainRectangleNeighborhoodCover f hf eps) J hX hY
  · intro K ll lr rl rr
    exact DomainRectangleNeighborhoodCover.split K ll lr rl rr
  · intro x y hx hy hxl hxu hyl hyu
    let a : Scalar := ⟨coordinateComplex x y,coordinateComplex_valid x y hx hy⟩
    have ha : f.domain a := hdom a ⟨hxl,hxu,hyl,hyu⟩
    let H := domainDerivativeRadius f hf a ha eps
    refine ⟨H, ?_⟩
    intro K hKx hKy
    exact DomainRectangleNeighborhoodCover.neighborhood K a ha
      (fun q hq => rectangleNear_complex_displacement K x y H hKx hKy q hq)

def domainRectangleNeighborhood (f : DomainFunctions.Map) (hf : Holomorphic f) (eps : QPos)
    (J : QInterval × QInterval) : Prop :=
  ∃ a : Scalar, ∃ ha : f.domain a, ∀ q : QComplex, rationalRectangleContains J q →
    Small (sub (ofQComplex q) a.val) (domainDerivativeRadius f hf a ha eps).val

theorem domainRectangleNeighborhood_uniform_depth (f : DomainFunctions.Map) (hf : Holomorphic f)
    (eps : QPos) (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (cover : DomainRectangleNeighborhoodCover f hf eps J) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      domainRectangleNeighborhood f hf eps (rectangleBisection J choice n) := by
  induction cover with
  | neighborhood J a ha hc =>
    refine ⟨0, ?_⟩
    intro choice n hn
    exact ⟨a,ha,fun q hq => hc q (rectangleBisection_contains_initial J hX hY choice n q hq)⟩
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

end ComputableAnalysis.RiemannHilbert.RectangularContour
