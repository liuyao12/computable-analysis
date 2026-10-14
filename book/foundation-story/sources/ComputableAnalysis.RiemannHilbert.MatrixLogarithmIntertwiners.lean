import ComputableAnalysis.RiemannHilbert.MatrixLogarithmFields
import ComputableAnalysis.RiemannHilbert.OperatorBounds

/-! Naturality of the constructed near-identity Taylor matrix sum. Finite
power identities and the explicit geometric tails prove the exact law for
linear intertwiners between arbitrary finite ranks and represented entries. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n m : Nat}
set_option maxHeartbeats 1000000

theorem coefficient_intertwines (E : ValueMap (Fiber n) (Fiber n))
    (F : ValueMap (Fiber m) (Fiber m)) (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hEF : ∀ x, N.eval (E.eval x) ≈ F.eval (N.eval x)) (x : Fiber n) (k : Nat) :
    N.eval ((coefficientMap E k).eval x) ≈ (coefficientMap F k).eval (N.eval x) :=
  Setoid.trans (hN.2 ⟨LocalLogarithm.coefficient k,LocalLogarithm.coefficient_valid k⟩ _)
    (Fiber.scale_congr (equiv_refl _ (LocalLogarithm.coefficient_valid k))
      (OperatorPower.intertwines E F N hEF x k))

theorem prefix_intertwines (E : ValueMap (Fiber n) (Fiber n))
    (F : ValueMap (Fiber m) (Fiber m)) (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hEF : ∀ x, N.eval (E.eval x) ≈ F.eval (N.eval x)) (x : Fiber n) (z : Scalar) (k : Nat) :
    N.eval ((finitePrefix E z k).eval x) ≈ (finitePrefix F z k).eval (N.eval x) := by
  change N.eval (vectorBlock (VectorSeries.term (fun j => (coefficientMap E j).eval x) z) 0 k) ≈
    vectorBlock (VectorSeries.term (fun j => (coefficientMap F j).eval (N.eval x)) z) 0 k
  exact Setoid.trans (vectorBlock_map N hN _ 0 k)
    (vectorBlock_congr _ _ (fun j => Setoid.trans
      (hN.2 ⟨power z.val j,power_valid z.val z.property j⟩ _)
      (Fiber.scale_congr (equiv_refl _ (power_valid z.val z.property j))
        (coefficient_intertwines E F N hN hEF x j))) 0 k)

theorem prefix_error_shrinks (B : Rat) (hB : 0 ≤ B) :
    ShrinksToZero (fun k : Nat => 8*B*(1/8 : Rat)^k) := by
  simpa only [Rat.mul_one,show 2*contraction*radius.val=(1 : Rat)/8 by decide +kernel]
    using operatorError_shrinks 1 B contraction radius.val (by decide +kernel) hB
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem parameterValue_intertwines (E : ValueMap (Fiber n) (Fiber n)) (hsmallE : SmallOperator E)
    (F : ValueMap (Fiber m) (Fiber m)) (hsmallF : SmallOperator F)
    (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hEF : ∀ x, N.eval (E.eval x) ≈ F.eval (N.eval x))
    (z : Scalar) (hz : interior radius.val z) (x : Fiber n) :
    N.eval ((parameterValue E hsmallE z hz).eval x) ≈
      (parameterValue F hsmallF z hz).eval (N.eval x) := by
  let B := LocalSystem.initialBound x
  let C := LocalSystem.initialBound (N.eval x)
  let L := ValueMap.linearBound N
  let e := fun k : Nat => 8*B*(1/8 : Rat)^k
  let f := fun k : Nat => 8*C*(1/8 : Rat)^k
  have hL : 0 ≤ L := ValueMap.linearBound_nonneg N
  have he := prefix_error_shrinks B (LocalSystem.initialBound_nonneg x)
  have hf := prefix_error_shrinks C (LocalSystem.initialBound_nonneg (N.eval x))
  have hs := RepresentedCauchySum.sum_shrinks _ _ (SeriesLimitLaws.shrinks_scale _ he L hL) hf
  intro i
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 _ hs
  intro k
  have ha := parameterValue_close E hsmallE z hz B (LocalSystem.initialBound_nonneg x)
    x (LocalSystem.initialBound_valid x) k
  have hb := parameterValue_close F hsmallF z hz C (LocalSystem.initialBound_nonneg (N.eval x))
    (N.eval x) (LocalSystem.initialBound_valid (N.eval x)) k
  have he0 : 0 ≤ e k := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) (LocalSystem.initialBound_nonneg x))
    (Rat.pow_nonneg (by decide +kernel))
  have hl := ValueMap.difference_bound N hN L (ValueMap.linear_bound N hN) _ he0 _ _ ha
  have hp := prefix_intertwines E F N hN hEF x z k
  have hr : Small (sub ((N.eval ((finitePrefix E z k).eval x)).val i)
      (((parameterValue F hsmallF z hz).eval (N.eval x)).val i)) (f k) :=
    Small.congr
      ((Fiber.sub ((finitePrefix F z k).eval (N.eval x)) ((parameterValue F hsmallF z hz).eval (N.eval x))).property i)
      ((Fiber.sub (N.eval ((finitePrefix E z k).eval x)) ((parameterValue F hsmallF z hz).eval (N.eval x))).property i)
      (FunctionTheory.sub_congr (equiv_symm (hp i))
        (equiv_refl _ (((parameterValue F hsmallF z hz).eval (N.eval x)).property i)))
      (RepresentedCauchySum.small_sub_symm _ _ _ (hb i))
  have hadd := LocalODE.small_add (hl i) hr
  have hc := Small.congr
    ((Fiber.add (Fiber.sub (N.eval ((parameterValue E hsmallE z hz).eval x)) (N.eval ((finitePrefix E z k).eval x)))
      (Fiber.sub (N.eval ((finitePrefix E z k).eval x)) ((parameterValue F hsmallF z hz).eval (N.eval x)))).property i)
    ((Fiber.sub (N.eval ((parameterValue E hsmallE z hz).eval x)) ((parameterValue F hsmallF z hz).eval (N.eval x))).property i)
    (equiv_symm (Fiber.difference_split _ _ _ i)) hadd
  simpa only [Rat.zero_add,Fiber.sub] using hc

theorem value_intertwines (E : ValueMap (Fiber n) (Fiber n)) (hsmallE : SmallOperator E)
    (F : ValueMap (Fiber m) (Fiber m)) (hsmallF : SmallOperator F)
    (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hEF : ∀ x, N.eval (E.eval x) ≈ F.eval (N.eval x)) (x : Fiber n) :
    N.eval ((value E hsmallE).eval x) ≈ (value F hsmallF).eval (N.eval x) :=
  parameterValue_intertwines E hsmallE F hsmallF N hN hEF unit unit_mem x

theorem parameterValue_commutes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (x : Fiber n) :
    E.eval ((parameterValue E hsmall z hz).eval x) ≈ (parameterValue E hsmall z hz).eval (E.eval x) :=
  parameterValue_intertwines E hsmall E hsmall E hE (fun _ => Setoid.refl _) z hz x

theorem value_commutes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E) (x : Fiber n) :
    E.eval ((value E hsmall).eval x) ≈ (value E hsmall).eval (E.eval x) :=
  parameterValue_commutes E hE hsmall unit unit_mem x

theorem identityPlus_intertwines (E : ValueMap (Fiber n) (Fiber n)) (F : ValueMap (Fiber m) (Fiber m))
    (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hEF : ∀ x, N.eval (E.eval x) ≈ F.eval (N.eval x)) (z : Scalar) (x : Fiber n) :
    N.eval ((identityPlus E z).eval x) ≈ (identityPlus F z).eval (N.eval x) :=
  Setoid.trans (hN.1 x (Fiber.scale z (E.eval x)))
    (Fiber.add_congr (Setoid.refl _) (Setoid.trans (hN.2 z (E.eval x))
      (Fiber.scale_congr (equiv_refl _ z.property) (hEF x))))

theorem resolvent_intertwines (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmallE : SmallOperator E)
    (F : ValueMap (Fiber m) (Fiber m)) (hF : IsLinear F) (hsmallF : SmallOperator F)
    (N : ValueMap (Fiber n) (Fiber m)) (hN : IsLinear N)
    (hEF : ∀ x, N.eval (E.eval x) ≈ F.eval (N.eval x))
    (z : Scalar) (hz : interior radius.val z) (x : Fiber n) :
    N.eval ((resolvent E hE hsmallE z hz).eval x) ≈
      (resolvent F hF hsmallF z hz).eval (N.eval x) := by
  have hi : (identityPlus F z).eval (N.eval ((resolvent E hE hsmallE z hz).eval x)) ≈ N.eval x :=
    Setoid.trans (Setoid.symm (identityPlus_intertwines E F N hN hEF z _))
      (N.congr (resolvent_left E hE hsmallE z hz x))
  exact Setoid.symm (Setoid.trans ((resolvent F hF hsmallF z hz).congr (Setoid.symm hi))
    (resolvent_right F hF hsmallF z hz _))

theorem resolvent_commutes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (x : Fiber n) :
    E.eval ((resolvent E hE hsmall z hz).eval x) ≈ (resolvent E hE hsmall z hz).eval (E.eval x) :=
  resolvent_intertwines E hE hsmall E hE hsmall E hE (fun _ => Setoid.refl _) z hz x

theorem parameterValues_commute (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z w : Scalar) (hz : interior radius.val z) (hw : interior radius.val w) (x : Fiber n) :
    (parameterValue E hsmall z hz).eval ((parameterValue E hsmall w hw).eval x) ≈
      (parameterValue E hsmall w hw).eval ((parameterValue E hsmall z hz).eval x) :=
  Setoid.symm (parameterValue_intertwines E hsmall E hsmall (parameterValue E hsmall w hw)
    (parameterValue_linear E hE hsmall w hw)
    (fun y => Setoid.symm (parameterValue_commutes E hE hsmall w hw y)) z hz x)

theorem parameterValue_resolvent_commutes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z w : Scalar) (hz : interior radius.val z) (hw : interior radius.val w) (x : Fiber n) :
    (parameterValue E hsmall z hz).eval ((resolvent E hE hsmall w hw).eval x) ≈
      (resolvent E hE hsmall w hw).eval ((parameterValue E hsmall z hz).eval x) :=
  Setoid.symm (parameterValue_intertwines E hsmall E hsmall (resolvent E hE hsmall w hw)
    (resolvent_linear E hE hsmall w hw)
    (fun y => Setoid.symm (resolvent_commutes E hE hsmall w hw y)) z hz x)

theorem field_derivative_commutes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (hM : LinearField.MatrixHolomorphic (field E hsmall) (vector E hsmall (Fiber.zero n)).domain_congr (field_congr E hsmall))
    (z w : Scalar) (hz : interior radius.val z) (hw : interior radius.val w) (x : Fiber n) :
    (parameterValue E hsmall z hz).eval ((LinearField.derivativeField hM w hw).eval x) ≈
      (LinearField.derivativeField hM w hw).eval ((parameterValue E hsmall z hz).eval x) :=
  Setoid.trans ((parameterValue E hsmall z hz).congr (field_derivative_resolvent E hE hsmall hM w hw x))
    (Setoid.trans (parameterValue_resolvent_commutes E hE hsmall z w hz hw (E.eval x))
      (Setoid.trans ((resolvent E hE hsmall w hw).congr (Setoid.symm (parameterValue_commutes E hE hsmall z hz x)))
        (Setoid.symm (field_derivative_resolvent E hE hsmall hM w hw _))))

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
