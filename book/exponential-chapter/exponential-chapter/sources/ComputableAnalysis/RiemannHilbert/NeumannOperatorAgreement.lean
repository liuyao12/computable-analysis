import ComputableAnalysis.RiemannHilbert.NeumannSeries

/-! Equivalent contraction operators give the same represented Neumann
sum, independently of their executable expressions and certified bounds. -/
namespace ComputableAnalysis.RiemannHilbert.Neumann
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

theorem power_congr (e f : ValueMap (Fiber n) (Fiber n)) (hef : e.Equiv f) (k : Nat) :
    (power e k).Equiv (power f k) := by
  induction k with
  | zero => exact ValueMap.equiv_refl _
  | succ k ih => exact ValueMap.followedBy_congr ih hef

theorem valueMap_congr (e f : ValueMap (Fiber n) (Fiber n)) (hef : e.Equiv f)
    (q r : Rat) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqsmall : q ≤ (1 : Rat)/2) (hrsmall : r ≤ (1 : Rat)/2)
    (he : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (e.eval x) (q*B))
    (hf : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (f.eval x) (r*B)) :
    (valueMap e q hq hqsmall he).Equiv (valueMap f r hr hrsmall hf) :=
  fun x => VectorGeometric.value_congr _ _ (fun k => power_congr e f hef k x)
    (initialBound x) q (initialBound x) r (initialBound_nonneg x) hq (initialBound_nonneg x) hr hqsmall hrsmall
    (term_bound e q hq he _ (initialBound_nonneg x) x (initialBound_valid x))
    (term_bound f r hr hf _ (initialBound_nonneg x) x (initialBound_valid x))

end ComputableAnalysis.RiemannHilbert.Neumann
