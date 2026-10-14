import ComputableAnalysis.RiemannHilbert.LocalLogarithmDerivative
import ComputableAnalysis.RiemannHilbert.NeumannOperatorAgreement
import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixDifferentiation

/-! The actual Taylor matrix sum near identity. Its rational coefficient
algorithm, validity, convergence, linearity, representation invariance and
genuine holomorphic parameter dependence are constructed. Identification
as an inverse of matrix exponentiation is a separate theorem. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}
set_option maxHeartbeats 1000000

def contraction : Rat := 1/32
def radius : QPos := ⟨2,by decide +kernel⟩
def SmallOperator (E : ValueMap (Fiber n) (Fiber n)) : Prop :=
  ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (E.eval x) (contraction*B)

def coefficientMap (E : ValueMap (Fiber n) (Fiber n)) (k : Nat) : ValueMap (Fiber n) (Fiber n) :=
  (Neumann.power E k).followedBy (Fiber.scaleMap ⟨LocalLogarithm.coefficient k,LocalLogarithm.coefficient_valid k⟩)

theorem coefficientMap_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (k : Nat) :
    IsLinear (coefficientMap E k) :=
  IsLinear.followedBy (Neumann.power_linear E hE k) (Fiber.scaleMap_linear _)

theorem coefficientMap_congr (E F : ValueMap (Fiber n) (Fiber n)) (hEF : E.Equiv F) (k : Nat) :
    (coefficientMap E k).Equiv (coefficientMap F k) :=
  ValueMap.followedBy_congr (Neumann.power_congr E F hEF k) (ValueMap.equiv_refl _)

theorem coefficientMap_majorant (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) :
    OperatorMajorant (coefficientMap E) 1 contraction := by
  intro k B hB x hx
  have hp := Neumann.power_bound E contraction (by decide +kernel) hsmall B hB x hx k
  have hc := LocalLogarithm.coefficient_bound k
  have ho : ∀ j : Nat, (1 : Rat)^j=1 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Rat.pow_succ,ih,Rat.one_mul]
  rw [ho k,Rat.mul_one] at hc
  have hs := bound_scale (c := ⟨LocalLogarithm.coefficient k,LocalLogarithm.coefficient_valid k⟩)
    (by decide +kernel) (Rat.mul_nonneg hB (Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ contraction))) hc hp
  have he : 2*1*(B*contraction^k)=2*1*contraction^k*B := by grind only
  rw [he] at hs
  exact hs

def parameterValue (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) : ValueMap (Fiber n) (Fiber n) :=
  operatorValue (coefficientMap E) z 1 contraction radius.val (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (coefficientMap_majorant E hsmall) (interior_bound radius.val z hz) (by decide +kernel)

theorem parameterValue_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) : IsLinear (parameterValue E hsmall z hz) :=
  operatorValue_linear (coefficientMap E) (coefficientMap_linear E hE) z 1 contraction radius.val
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (coefficientMap_majorant E hsmall)
    (interior_bound radius.val z hz) (by decide +kernel)

def finitePrefix (E : ValueMap (Fiber n) (Fiber n)) (z : Scalar) (N : Nat) := operatorPrefixMap (coefficientMap E) z N

theorem prefix_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (z : Scalar) (N : Nat) :
    IsLinear (finitePrefix E z N) := operatorPrefixMap_linear _ (coefficientMap_linear E hE) z N

theorem parameterValue_close (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) (N : Nat) :
    CoordinateBound (Fiber.sub ((parameterValue E hsmall z hz).eval x) ((finitePrefix E z N).eval x)) (8*B*(1/8 : Rat)^N) := by
  have hs := operatorValue_close (coefficientMap E) z 1 contraction radius.val B
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hB (coefficientMap_majorant E hsmall)
    (interior_bound radius.val z hz) (by decide +kernel) x hx N
  simpa only [parameterValue,finitePrefix,show 2*contraction*radius.val=(1 : Rat)/8 by decide +kernel,Rat.mul_one] using hs

theorem parameterValue_bound (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((parameterValue E hsmall z hz).eval x) (8*B) := by
  simpa only [parameterValue,Rat.mul_one] using operatorValue_bound (coefficientMap E) z 1 contraction radius.val B
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hB (coefficientMap_majorant E hsmall)
    (interior_bound radius.val z hz) (by decide +kernel) x hx

def vector (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) (x : Fiber n) : DomainVectorFunctions.Map n where
  domain := interior radius.val
  eval z hz := (parameterValue E hsmall z hz).eval x
  domain_congr z w hzw :=
    ⟨Centered.interior_congr radius.val z w hzw,
      Centered.interior_congr radius.val w z (equiv_symm hzw)⟩
  eval_congr z w hz hw hzw := VectorSeries.value_congr _ _ z w (fun _ => Setoid.refl _) hzw
    (2*1*initialBound x) contraction radius.val (2*1*initialBound x) contraction radius.val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg x)) (by decide +kernel) (by decide +kernel)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg x)) (by decide +kernel) (by decide +kernel)
    (operatorCoefficient_bound (coefficientMap E) 1 contraction _ (LocalSystem.initialBound_nonneg x)
      (coefficientMap_majorant E hsmall) x (LocalSystem.initialBound_valid x))
    (operatorCoefficient_bound (coefficientMap E) 1 contraction _ (LocalSystem.initialBound_nonneg x)
      (coefficientMap_majorant E hsmall) x (LocalSystem.initialBound_valid x))
    (interior_bound radius.val z hz) (interior_bound radius.val w hw) (by decide +kernel) (by decide +kernel)

def coordinateMap (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) (x : Fiber n) (i : Fin n) : CertifiedFunctions.Map :=
  BoundedSeries.seriesMap (fun k => ((coefficientMap E k).eval x).val i) (fun k => ((coefficientMap E k).eval x).property i)
    (2*1*initialBound x) contraction radius.val (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg x))
    (by decide +kernel) (by decide +kernel)
    (fun k => operatorCoefficient_bound (coefficientMap E) 1 contraction _ (LocalSystem.initialBound_nonneg x)
      (coefficientMap_majorant E hsmall) x (LocalSystem.initialBound_valid x) k i) (by decide +kernel)

def coordinateMap_holomorphic (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) (x : Fiber n) (i : Fin n) :
    CertifiedFunctions.Holomorphic (coordinateMap E hsmall x i) :=
  BoundedSeries.seriesMap_holomorphic _ _ (2*1*initialBound x) contraction radius.val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (by decide)) (LocalSystem.initialBound_nonneg x)) (by decide +kernel) (by decide +kernel)
    (fun k => operatorCoefficient_bound (coefficientMap E) 1 contraction _ (LocalSystem.initialBound_nonneg x)
      (coefficientMap_majorant E hsmall) x (LocalSystem.initialBound_valid x) k i) (by decide +kernel)

def vector_holomorphic (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (vector E hsmall x) where
  openDomain := ⟨interiorRadius radius.val,interiorRadius_inside radius.val⟩
  coordinates i := DomainFunctions.ofCertifiedHolomorphic (coordinateMap_holomorphic E hsmall x i)

def unit : Scalar := ⟨one,ofQComplex_valid _⟩
theorem unit_mem : interior radius.val unit := by
  refine ⟨1,by decide +kernel,by decide +kernel,?_⟩
  exact ⟨fun _ _ => by change (-1 : Rat) ≤ 1; decide +kernel,fun _ _ => Rat.le_refl,
    fun _ _ => by change (-1 : Rat) ≤ 0; decide +kernel,fun _ _ => by change (0 : Rat) ≤ 1; decide +kernel⟩

def value (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E) := parameterValue E hsmall unit unit_mem
theorem value_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E) :
    IsLinear (value E hsmall) := parameterValue_linear E hE hsmall unit unit_mem

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
