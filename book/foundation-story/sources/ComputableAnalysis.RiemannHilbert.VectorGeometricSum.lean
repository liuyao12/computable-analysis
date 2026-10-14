import ComputableAnalysis.RiemannHilbert.VectorFiniteSums

/-! Represented geometric sums of finite vectors, without a scalar power
parameter or an abstract completion. -/
namespace ComputableAnalysis.RiemannHilbert.VectorGeometric
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def value (t : Nat → Fiber n) (C q : Rat) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hsmall : q ≤ (1 : Rat)/2) (ht : ∀ k, CoordinateBound (t k) (2*C*q^k)) : Fiber n :=
  ⟨fun i => ScalarSeries.value (fun k => (t k).val i) (fun k => (t k).property i) C q,
    fun i => ScalarSeries.value_valid _ (fun k => (t k).property i) C q hC hq hsmall (fun k => ht k i)⟩

theorem value_close (t : Nat → Fiber n) (C q : Rat) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hsmall : q ≤ (1 : Rat)/2) (ht : ∀ k, CoordinateBound (t k) (2*C*q^k)) (N : Nat) :
    CoordinateBound (Fiber.sub (value t C q hC hq hsmall ht) (vectorBlock t 0 N)) (4*C*q^N) := by
  intro i
  change Small (sub _ ((vectorBlock t 0 N).val i)) _
  rw [vectorBlock_coordinate]
  exact ScalarSeries.value_close _ (fun k => (t k).property i) C q hC hq hsmall (fun k => ht k i) N

theorem value_bound (t : Nat → Fiber n) (C q : Rat) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hsmall : q ≤ (1 : Rat)/2) (ht : ∀ k, CoordinateBound (t k) (2*C*q^k)) :
    CoordinateBound (value t C q hC hq hsmall ht) (4*C) :=
  fun i => ScalarSeries.value_bound _ (fun k => (t k).property i) C q hC hq hsmall (fun k => ht k i)

theorem value_congr (t u : Nat → Fiber n) (htu : ∀ k, t k ≈ u k) (C q D r : Rat)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hsmall : q ≤ (1 : Rat)/2) (hrsmall : r ≤ (1 : Rat)/2)
    (ht : ∀ k, CoordinateBound (t k) (2*C*q^k)) (hu : ∀ k, CoordinateBound (u k) (2*D*r^k)) :
    value t C q hC hq hsmall ht ≈ value u D r hD hr hrsmall hu :=
  fun i => ScalarSeries.value_congr _ _ (fun k => (t k).property i) (fun k => (u k).property i)
    C q D r hC hq hD hr hsmall hrsmall (fun k => ht k i) (fun k => hu k i) (fun k => htu k i)

end ComputableAnalysis.RiemannHilbert.VectorGeometric
