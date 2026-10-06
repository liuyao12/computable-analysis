import ComputableAnalysis.RiemannHilbert.ExponentialPowerFormula
import ComputableAnalysis.RiemannHilbert.EntireExponentialODE

/-! Exponentiation preserves supplied linear intertwiners. The statement
allows different finite ranks and arbitrary represented residues and vectors.
Finite-prefix naturality and constructed tails prove the exact entire law. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n m : Nat}

theorem coefficient_intertwines (A : ValueMap (Fiber n) (Fiber n))
    (B : ValueMap (Fiber m) (Fiber m)) (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hAB : ∀ x, N.eval (A.eval x) ≈ B.eval (N.eval x)) (x : Fiber n) (k : Nat) :
    N.eval (coefficient A x k) ≈ coefficient B (N.eval x) k := by
  induction k with
  | zero => exact Setoid.refl _
  | succ k ih =>
      exact Setoid.trans (linear_ratScale N hN _ (A.eval (coefficient A x k)))
        (ratScale_congr _ (Setoid.trans (hAB _) (B.congr ih)))

theorem prefix_intertwines (A : ValueMap (Fiber n) (Fiber n))
    (B : ValueMap (Fiber m) (Fiber m)) (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hAB : ∀ x, N.eval (A.eval x) ≈ B.eval (N.eval x)) (x : Fiber n) (z : Scalar) (k : Nat) :
    N.eval ((finitePrefix A z k).eval x) ≈ (finitePrefix B z k).eval (N.eval x) := by
  change N.eval (vectorBlock (VectorSeries.term (coefficient A x) z) 0 k) ≈
    vectorBlock (VectorSeries.term (coefficient B (N.eval x)) z) 0 k
  exact Setoid.trans (vectorBlock_map N hN (VectorSeries.term (coefficient A x) z) 0 k)
    (vectorBlock_congr (fun j => N.eval (VectorSeries.term (coefficient A x) z j))
      (VectorSeries.term (coefficient B (N.eval x)) z)
      (fun j => Setoid.trans
        (hN.2 ⟨power z.val j, power_valid z.val z.property j⟩ (coefficient A x j))
        (Fiber.scale_congr (equiv_refl _ (power_valid z.val z.property j))
          (coefficient_intertwines A B N hN hAB x j))) 0 k)

theorem value_intertwines (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (B : ValueMap (Fiber m) (Fiber m)) (hB : IsLinear B)
    (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hAB : ∀ x, N.eval (A.eval x) ≈ B.eval (N.eval x)) (z : Scalar) (x : Fiber n) :
    N.eval ((value A hA z).eval x) ≈ (value B hB z).eval (N.eval x) := by
  let R := pointRadius z
  let E := LocalSystem.initialBound x
  let F := LocalSystem.initialBound (N.eval x)
  let L := ValueMap.linearBound N
  let e := fun k : Nat => 8*discBudget A R.val*E*(2*rate R.val*R.val)^k
  let f := fun k : Nat => 8*discBudget B R.val*F*(2*rate R.val*R.val)^k
  have hL : 0 ≤ L := ValueMap.linearBound_nonneg N
  have he := prefix_error_shrinks A R E (LocalSystem.initialBound_nonneg x)
  have hf := prefix_error_shrinks B R F (LocalSystem.initialBound_nonneg (N.eval x))
  have hsum := RepresentedCauchySum.sum_shrinks _ _ (SeriesLimitLaws.shrinks_scale _ he L hL) hf
  intro i
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 _ hsum
  intro k
  have ha := value_prefix_close A hA R z (pointRadius_inside z) E (LocalSystem.initialBound_nonneg x)
    x (LocalSystem.initialBound_valid x) k
  have hb := value_prefix_close B hB R z (pointRadius_inside z) F (LocalSystem.initialBound_nonneg (N.eval x))
    (N.eval x) (LocalSystem.initialBound_valid (N.eval x)) k
  have hq : 0 ≤ 2*rate R.val*R.val := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide) (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property)))) (Rat.le_of_lt R.property)
  have he0 : 0 ≤ e k := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg A R.val)) (LocalSystem.initialBound_nonneg x))
    (Rat.pow_nonneg hq)
  have hl := ValueMap.difference_bound N hN L (ValueMap.linear_bound N hN) _ he0 _ _ ha
  have hp := prefix_intertwines A B N hN hAB x z k
  have hr : Small (sub ((N.eval ((finitePrefix A z k).eval x)).val i)
      (((value B hB z).eval (N.eval x)).val i)) (f k) :=
    Small.congr
      ((Fiber.sub ((finitePrefix B z k).eval (N.eval x)) ((value B hB z).eval (N.eval x))).property i)
      ((Fiber.sub (N.eval ((finitePrefix A z k).eval x)) ((value B hB z).eval (N.eval x))).property i)
      (FunctionTheory.sub_congr (equiv_symm (hp i))
        (equiv_refl _ (((value B hB z).eval (N.eval x)).property i)))
      (RepresentedCauchySum.small_sub_symm _ _ _ (hb i))
  have hs := LocalODE.small_add (hl i) hr
  have hc := Small.congr
    ((Fiber.add (Fiber.sub (N.eval ((value A hA z).eval x)) (N.eval ((finitePrefix A z k).eval x)))
      (Fiber.sub (N.eval ((finitePrefix A z k).eval x)) ((value B hB z).eval (N.eval x)))).property i)
    ((Fiber.sub (N.eval ((value A hA z).eval x)) ((value B hB z).eval (N.eval x))).property i)
    (equiv_symm (Fiber.difference_split _ _ _ i)) hs
  simpa only [Rat.zero_add, Fiber.sub] using hc

theorem value_commutes (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (z : Scalar) (x : Fiber n) :
    A.eval ((value A hA z).eval x) ≈ (value A hA z).eval (A.eval x) :=
  value_intertwines A hA A hA A hA (fun _ => Setoid.refl _) z x

end ComputableAnalysis.RiemannHilbert.MatrixExponential
