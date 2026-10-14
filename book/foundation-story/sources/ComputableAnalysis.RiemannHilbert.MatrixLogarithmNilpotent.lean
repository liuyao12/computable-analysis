import ComputableAnalysis.RiemannHilbert.MatrixLogarithmIntertwiners
import ComputableAnalysis.RiemannHilbert.ExponentialNilpotent

/-! A complete logarithm client: for a small represented square-zero
operator, the actual Taylor sum equals the operator and exponentiating it
gives identity plus that operator. No exponential identity is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}
set_option maxHeartbeats 1000000

theorem value_of_stabilized_prefix (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E)
    (x : Fiber n) (z : Scalar) (hz : interior radius.val z) (s : Nat) (v : Fiber n)
    (h : ∀ N, (finitePrefix E z (N+s)).eval x ≈ v) : (parameterValue E hsmall z hz).eval x ≈ v := by
  have he := SeriesLimitLaws.shrinks_shift _ (prefix_error_shrinks (LocalSystem.initialBound x)
    (LocalSystem.initialBound_nonneg x)) s
  intro i
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 _ he
  intro N
  have hs := parameterValue_close E hsmall z hz (LocalSystem.initialBound x) (LocalSystem.initialBound_nonneg x)
    x (LocalSystem.initialBound_valid x) (N+s) i
  simpa only [Rat.zero_add,Fiber.sub] using Small.congr
    ((Fiber.sub ((parameterValue E hsmall z hz).eval x) ((finitePrefix E z (N+s)).eval x)).property i)
    ((Fiber.sub ((parameterValue E hsmall z hz).eval x) v).property i)
    (FunctionTheory.sub_congr (equiv_refl _ (((parameterValue E hsmall z hz).eval x).property i)) (h N i)) hs

theorem power_nil_tail (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (hNil : ∀ x, E.eval (E.eval x) ≈ Fiber.zero n) (x : Fiber n) (k : Nat) :
    (Neumann.power E (k+2)).eval x ≈ Fiber.zero n := by
  induction k with
  | zero => exact hNil x
  | succ k ih =>
    have he : k+1+2=(k+2)+1 := by omega
    rw [he]
    exact Setoid.trans (E.congr ih) hE.zero

theorem coefficient_nil_tail (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (hNil : ∀ x, E.eval (E.eval x) ≈ Fiber.zero n) (x : Fiber n) (k : Nat) :
    (coefficientMap E (k+2)).eval x ≈ Fiber.zero n :=
  Setoid.trans (Fiber.scale_congr (equiv_refl _ (LocalLogarithm.coefficient_valid (k+2)))
    (power_nil_tail E hE hNil x k)) (Fiber.scale_zero _)

theorem nil_prefix_two (E : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) (z : Scalar) :
    (finitePrefix E z 2).eval x ≈ Fiber.scale z (E.eval x) := by
  change Fiber.add (Fiber.add (Fiber.zero n)
    (Fiber.scale ⟨one,ofQComplex_valid _⟩ ((coefficientMap E 0).eval x)))
    (Fiber.scale ⟨power z.val 1,power_valid z.val z.property 1⟩ ((coefficientMap E 1).eval x)) ≈ _
  exact Setoid.trans (Fiber.add_congr
    (Setoid.trans (Fiber.add_congr (Setoid.refl _)
      (Setoid.trans (Fiber.scale_congr (equiv_refl _ (ofQComplex_valid _)) (coefficientMap_zero E x)) (Fiber.scale_zero _)))
      (Fiber.add_zero _))
    (Fiber.scale_congr (one_mul_equiv _ z.property) (coefficientMap_one E x))) (Fiber.zero_add _)

theorem nil_prefix_stabilizes (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E)
    (hNil : ∀ x, E.eval (E.eval x) ≈ Fiber.zero n) (x : Fiber n) (z : Scalar) (N : Nat) :
    (finitePrefix E z (N+2)).eval x ≈ Fiber.scale z (E.eval x) := by
  induction N with
  | zero => exact nil_prefix_two E x z
  | succ N ih =>
    have he : N+1+2=(N+2)+1 := by omega
    rw [he]
    change Fiber.add (vectorBlock (VectorSeries.term (fun j => (coefficientMap E j).eval x) z) 0 (N+2))
      (VectorSeries.term (fun j => (coefficientMap E j).eval x) z (0+(N+2))) ≈ _
    rw [Nat.zero_add]
    exact Setoid.trans (Fiber.add_congr (Setoid.refl _)
      (Setoid.trans (Fiber.scale_congr (equiv_refl _ (power_valid z.val z.property (N+2)))
        (coefficient_nil_tail E hE hNil x N)) (Fiber.scale_zero _)))
      (Setoid.trans (Fiber.add_zero _) ih)

theorem parameterValue_nilpotent (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (hNil : ∀ x, E.eval (E.eval x) ≈ Fiber.zero n) (z : Scalar) (hz : interior radius.val z) :
    (parameterValue E hsmall z hz).Equiv (OperatorPower.scaled E z) :=
  fun x => value_of_stabilized_prefix E hsmall x z hz 2 _ (nil_prefix_stabilizes E hE hNil x z)

theorem value_nilpotent (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (hNil : ∀ x, E.eval (E.eval x) ≈ Fiber.zero n) : (value E hsmall).Equiv E :=
  fun x => Setoid.trans (parameterValue_nilpotent E hE hsmall hNil unit unit_mem x)
    (fun i => one_mul_equiv _ ((E.eval x).property i))

theorem exponential_value_nilpotent (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (hNil : ∀ x, E.eval (E.eval x) ≈ Fiber.zero n) :
    (MatrixExponential.value (value E hsmall) (value_linear E hE hsmall) unit).Equiv (identityPlus E unit) :=
  fun x => Setoid.trans (MatrixExponential.value_congr (value E hsmall) E (value_linear E hE hsmall) hE
    (value_nilpotent E hE hsmall hNil) unit unit (equiv_refl _ unit.property) x x (Setoid.refl _))
    (MatrixExponential.value_nilpotent E hE hNil unit x)

theorem resolvent_nilpotent_image (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (hNil : ∀ x, E.eval (E.eval x) ≈ Fiber.zero n) (z : Scalar) (hz : interior radius.val z) (x : Fiber n) :
    (resolvent E hE hsmall z hz).eval (E.eval x) ≈ E.eval x := by
  have hf : (identityPlus E z).eval (E.eval x) ≈ E.eval x :=
    Setoid.trans (Fiber.add_congr (Setoid.refl _)
      (Setoid.trans (Fiber.scale_congr (equiv_refl _ z.property) (hNil x)) (Fiber.scale_zero z))) (Fiber.add_zero _)
  exact Setoid.trans ((resolvent E hE hsmall z hz).congr (Setoid.symm hf))
    (resolvent_right E hE hsmall z hz (E.eval x))

theorem nilpotent_derivative (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (hNil : ∀ x, E.eval (E.eval x) ≈ Fiber.zero n) (x : Fiber n)
    (hF : DomainVectorFunctions.Holomorphic (vector E hsmall x)) (z : Scalar) (hz : interior radius.val z) :
    DomainVectorFunctions.derivative (vector E hsmall x) hF z hz ≈ E.eval x :=
  Setoid.trans (vector_derivative_resolvent E hE hsmall x hF z hz)
    (resolvent_nilpotent_image E hE hsmall hNil z hz x)

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
