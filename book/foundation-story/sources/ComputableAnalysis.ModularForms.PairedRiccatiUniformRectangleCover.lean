import ComputableAnalysis.ModularForms.PairedRiccatiRectangleCover

/-! A common depth derived from actual finite rectangle neighborhoods. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem rectangleBisection_shift (J : QInterval × QInterval)
    (choice : Nat → Bool × Bool) (n : Nat) :
    rectangleBisection J choice (n+1)=
      rectangleBisection (bisectRectangle J (choice 0)) (fun k => choice (k+1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rectangleBisection,ih]; rfl

theorem rectangleBisection_contains_initial (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (choice : Nat → Bool × Bool) (n : Nat) (q : QComplex)
    (hq : rationalRectangleContains (rectangleBisection J choice n) q) :
    rationalRectangleContains J q := by
  rw [rectangleBisection_coordinates] at hq
  have hx := bisectionInterval_nested J.1 hX (fun k => (choice k).1) 0 n (Nat.zero_le n)
  have hy := bisectionInterval_nested J.2 hY (fun k => (choice k).2) 0 n (Nat.zero_le n)
  exact ⟨Rat.le_trans hx.1 hq.1,Rat.le_trans hq.2.1 hx.2.2,
    Rat.le_trans hy.1 hq.2.2.1,Rat.le_trans hq.2.2.2 hy.2.2⟩

def riccatiRectangleNeighborhood (eps : QPos) (J : QInterval × QInterval) : Prop :=
  ∃ a : Scalar, ∃ H : QPos,
    H.val≤((pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta eps).val ∧
    ∀ q : QComplex, rationalRectangleContains J q → Small (sub (ofQComplex q) a.val) H.val

theorem riccatiRectangleCover_uniform_depth (eps : QPos) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (cover : RiccatiDerivativeRectangleCover eps J) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      riccatiRectangleNeighborhood eps (rectangleBisection J choice n) := by
  induction cover with
  | neighborhood J a H hr hc =>
    refine ⟨0, ?_⟩
    intro choice n hn
    exact ⟨a,H,hr,fun q hq => hc q (rectangleBisection_contains_initial J hX hY choice n q hq)⟩
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

theorem pairedRiccati_uniform_rectangle_cover (eps : QPos) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    ∃ N, ∀ choice : Nat → Bool × Bool, ∀ n, N≤n →
      riccatiRectangleNeighborhood eps (rectangleBisection J choice n) :=
  riccatiRectangleCover_uniform_depth eps J hX hY
    (pairedRiccati_finite_rectangle_cover eps J hX hY)

end ComputableAnalysis.ModularForms
