import ComputableAnalysis.RiemannHilbert.LinearDifference
import ComputableAnalysis.RiemannHilbert.VectorGeometricSum

/-! Finite geometric operator sums and their exact telescoping defect. -/
namespace ComputableAnalysis.RiemannHilbert.Neumann
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def power (e : ValueMap (Fiber n) (Fiber n)) : Nat → ValueMap (Fiber n) (Fiber n)
  | 0 => ValueMap.identity
  | k+1 => (power e k).followedBy e

theorem power_linear (e : ValueMap (Fiber n) (Fiber n)) (he : IsLinear e) (k : Nat) :
    IsLinear (power e k) := by
  induction k with
  | zero => exact IsLinear.identity n
  | succ k ih => exact IsLinear.followedBy ih he

theorem power_bound (e : ValueMap (Fiber n) (Fiber n)) (q : Rat) (hq : 0 ≤ q)
    (he : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (e.eval x) (q*B))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) (k : Nat) :
    CoordinateBound ((power e k).eval x) (B*q^k) := by
  induction k with
  | zero =>
    change CoordinateBound x (B*q^0)
    simpa only [Rat.pow_zero, Rat.mul_one] using hx
  | succ k ih =>
    have hs := he (B*q^k) (Rat.mul_nonneg hB (Rat.pow_nonneg hq)) ((power e k).eval x) ih
    have hh : q*(B*q^k)=B*q^(k+1) := by rw [Rat.pow_succ]; grind
    rw [hh] at hs; exact hs

theorem term_bound (e : ValueMap (Fiber n) (Fiber n)) (q : Rat) (hq : 0 ≤ q)
    (he : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (e.eval x) (q*B))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) (k : Nat) :
    CoordinateBound ((power e k).eval x) (2*B*q^k) := by
  intro i
  apply (power_bound e q hq he B hB x hx k i).mono
  have hh := Rat.mul_nonneg hB (Rat.pow_nonneg hq : 0 ≤ q^k)
  grind

def finiteSum (e : ValueMap (Fiber n) (Fiber n)) (N : Nat) : ValueMap (Fiber n) (Fiber n) :=
  blockMap (power e) 0 N

theorem finiteSum_linear (e : ValueMap (Fiber n) (Fiber n)) (he : IsLinear e) (N : Nat) :
    IsLinear (finiteSum e N) := blockMap_linear _ (power_linear e he) 0 N

theorem finiteSum_succ (e : ValueMap (Fiber n) (Fiber n)) (N : Nat) (x : Fiber n) :
    (finiteSum e (N+1)).eval x = Fiber.add ((finiteSum e N).eval x) ((power e N).eval x) := by
  simp only [finiteSum, blockMap, vectorBlock.eq_2, Nat.zero_add]

/-- Exact finite Neumann defect, independent of any convergence assertion. -/
theorem finite_defect (e : ValueMap (Fiber n) (Fiber n)) (he : IsLinear e) (x : Fiber n) (N : Nat) :
    Fiber.sub ((finiteSum e N).eval x) (e.eval ((finiteSum e N).eval x)) ≈
      Fiber.sub x ((power e N).eval x) := by
  induction N with
  | zero =>
    change Fiber.sub (Fiber.zero n) (e.eval (Fiber.zero n)) ≈ Fiber.sub x x
    exact Setoid.trans (Fiber.sub_congr (Setoid.refl _) he.zero)
      (Setoid.trans (Fiber.sub_zero (Fiber.zero n))
        (Setoid.symm (Fiber.bound_zero_equiv (Fiber.sub_zero_bound (Setoid.refl x)))))
  | succ N ih =>
    rw [finiteSum_succ]
    have h1 := Fiber.sub_congr
      (Setoid.refl (Fiber.add ((finiteSum e N).eval x) ((power e N).eval x)))
      (he.1 ((finiteSum e N).eval x) ((power e N).eval x))
    exact Setoid.trans h1 (Setoid.trans (Fiber.sub_add_sub _ _ _ _)
      (Setoid.trans (Fiber.add_congr ih (Setoid.refl _))
        (Setoid.symm (Fiber.difference_split x ((power e (N+1)).eval x) ((power e N).eval x)))))

theorem finite_inverse (f : ValueMap (Fiber n) (Fiber n)) (hf : IsLinear f) (x : Fiber n) (N : Nat) :
    f.eval ((finiteSum (ValueMap.difference ValueMap.identity f) N).eval x) ≈
      Fiber.sub x ((power (ValueMap.difference ValueMap.identity f) N).eval x) :=
  Setoid.trans (Setoid.symm (ValueMap.complement f _))
    (finite_defect _ (ValueMap.difference_linear ValueMap.identity f (IsLinear.identity n) hf) x N)

theorem finite_inverse_error (f : ValueMap (Fiber n) (Fiber n)) (hf : IsLinear f) (q : Rat) (hq : 0 ≤ q)
    (hdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity f).eval x) (q*B))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) (N : Nat) :
    CoordinateBound (Fiber.sub (f.eval ((finiteSum (ValueMap.difference ValueMap.identity f) N).eval x)) x)
      (B*q^N) := by
  let E := ValueMap.difference ValueMap.identity f
  have ht := power_bound E q hq hdev B hB x hx N
  have he : Fiber.sub (Fiber.sub x ((power E N).eval x)) x ≈ Fiber.neg ((power E N).eval x) := by
    intro i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (Fiber.sub (Fiber.sub x ((power E N).eval x)) x).property i)
      (hright := (Fiber.neg ((power E N).eval x)).property i)
    change (ComplexRawQuotient.ofRaw (x.val i) (x.property i)-
      ComplexRawQuotient.ofRaw (((power E N).eval x).val i) (((power E N).eval x).property i))-
      ComplexRawQuotient.ofRaw (x.val i) (x.property i) =
      -ComplexRawQuotient.ofRaw (((power E N).eval x).val i) (((power E N).eval x).property i)
    grind
  have hs : CoordinateBound (Fiber.neg ((power E N).eval x)) (B*q^N) :=
    fun i => SeriesLimitLaws.small_neg (ht i)
  exact bound_congr (Setoid.symm (Setoid.trans
    (Fiber.sub_congr (finite_inverse f hf x N) (Setoid.refl x)) he)) hs

end ComputableAnalysis.RiemannHilbert.Neumann
