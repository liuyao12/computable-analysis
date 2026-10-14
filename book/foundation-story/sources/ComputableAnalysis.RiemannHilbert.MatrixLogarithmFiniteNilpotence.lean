import ComputableAnalysis.RiemannHilbert.MatrixLogarithmNilpotent

/-! Finite stabilization of the actual matrix logarithm at any supplied
nilpotence index. The index is evidence about powers of the operator;
agreement with the represented infinite sum follows from its proved tails. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}
set_option maxHeartbeats 1000000

def NilpotentAt (E : ValueMap (Fiber n) (Fiber n)) (s : Nat) : Prop :=
  ∀ x, (Neumann.power E s).eval x ≈ Fiber.zero n

theorem nilpotentAt_tail (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (s : Nat) (hNil : NilpotentAt E s) (k : Nat) (x : Fiber n) :
    (Neumann.power E (k+s)).eval x ≈ Fiber.zero n := by
  induction k with
  | zero => simpa only [Nat.zero_add] using hNil x
  | succ k ih =>
    have he : k+1+s=(k+s)+1 := by omega
    rw [he]
    exact Setoid.trans (E.congr ih) hE.zero

theorem nilpotentAt_coefficient_tail (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (s : Nat) (hNil : NilpotentAt E s) (k : Nat) (x : Fiber n) :
    (coefficientMap E (k+s)).eval x ≈ Fiber.zero n :=
  Setoid.trans (Fiber.scale_congr (equiv_refl _ (LocalLogarithm.coefficient_valid (k+s)))
    (nilpotentAt_tail E hE s hNil k x)) (Fiber.scale_zero _)

theorem nilpotentAt_prefix_stabilizes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (s : Nat) (hNil : NilpotentAt E s) (z : Scalar) (N : Nat) (x : Fiber n) :
    (finitePrefix E z (N+s)).eval x ≈ (finitePrefix E z s).eval x := by
  induction N with
  | zero => simpa only [Nat.zero_add] using (Setoid.refl ((finitePrefix E z s).eval x))
  | succ N ih =>
    have he : N+1+s=(N+s)+1 := by omega
    rw [he]
    change Fiber.add (vectorBlock (VectorSeries.term (fun j => (coefficientMap E j).eval x) z) 0 (N+s))
      (VectorSeries.term (fun j => (coefficientMap E j).eval x) z (0+(N+s))) ≈ _
    rw [Nat.zero_add]
    exact Setoid.trans (Fiber.add_congr (Setoid.refl _)
      (Setoid.trans (Fiber.scale_congr (equiv_refl _ (power_valid z.val z.property (N+s)))
        (nilpotentAt_coefficient_tail E hE s hNil N x)) (Fiber.scale_zero _)))
      (Setoid.trans (Fiber.add_zero _) ih)

/-- The actual infinite evaluator agrees with a finite polynomial whenever
the supplied represented operator has a justified finite nilpotence index. -/
theorem parameterValue_finite_nilpotent (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (hsmall : SmallOperator E) (s : Nat) (hNil : NilpotentAt E s)
    (z : Scalar) (hz : interior radius.val z) :
    (parameterValue E hsmall z hz).Equiv (finitePrefix E z s) :=
  fun x => value_of_stabilized_prefix E hsmall x z hz s _
    (fun N => nilpotentAt_prefix_stabilizes E hE s hNil z N x)

theorem value_finite_nilpotent (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (hsmall : SmallOperator E) (s : Nat) (hNil : NilpotentAt E s) :
    (value E hsmall).Equiv (finitePrefix E unit s) :=
  parameterValue_finite_nilpotent E hE hsmall s hNil unit unit_mem

theorem finite_nilpotent_index_agreement (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (s t : Nat) (hs : NilpotentAt E s) (ht : NilpotentAt E t) (z : Scalar) :
    (finitePrefix E z s).Equiv (finitePrefix E z t) := by
  intro x
  have ha := nilpotentAt_prefix_stabilizes E hE s hs z t x
  have hb := nilpotentAt_prefix_stabilizes E hE t ht z s x
  rw [Nat.add_comm t s] at ha
  exact Setoid.trans (Setoid.symm ha) hb

/-- Finite nilpotent logarithms preserve linear intertwiners even when the
two ranks and justified nilpotence indices differ. No smallness is needed. -/
theorem finite_nilpotent_intertwines {m : Nat}
    (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (s : Nat) (hs : NilpotentAt E s)
    (F : ValueMap (Fiber m) (Fiber m)) (hF : IsLinear F) (t : Nat) (ht : NilpotentAt F t)
    (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hEF : ∀ x, N.eval (E.eval x) ≈ F.eval (N.eval x)) (z : Scalar) (x : Fiber n) :
    N.eval ((finitePrefix E z s).eval x) ≈ (finitePrefix F z t).eval (N.eval x) := by
  have ha := nilpotentAt_prefix_stabilizes E hE s hs z t x
  rw [Nat.add_comm t s] at ha
  exact Setoid.trans (N.congr (Setoid.symm ha))
    (Setoid.trans (prefix_intertwines E F N hN hEF x z (s+t))
      (nilpotentAt_prefix_stabilizes F hF t ht z s (N.eval x)))

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
