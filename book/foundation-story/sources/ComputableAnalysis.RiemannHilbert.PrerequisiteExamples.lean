import ComputableAnalysis.RiemannHilbert.LocalSystemCoefficients
import ComputableAnalysis.RiemannHilbert.HorizontalDescent
import ComputableAnalysis.RiemannHilbert.ConstantSolution

/-! Concrete represented-fiber clients of the prerequisite laws. -/
namespace ComputableAnalysis.RiemannHilbert.PrerequisiteExamples

/-- A fresh evaluator for identity, with inverse laws only asserted as value
agreement. It may be substituted for literal identity in every word. -/
def identityAlternative (n : Nat) : LinearIso n n := by
  let forward : ValueMap (Fiber n) (Fiber n) :=
    ⟨fun x => Fiber.add (Fiber.zero n) x,
      fun h => Fiber.add_congr (Setoid.refl _) h⟩
  let iso : ValueIso (Fiber n) (Fiber n) :=
    ⟨forward, ValueMap.identity, Fiber.zero_add, Fiber.zero_add⟩
  exact ⟨iso, IsLinear.congr (IsLinear.identity n)
    (fun x => Setoid.symm (Fiber.zero_add x))⟩

theorem alternative_word (w : List (Letter Bool)) (x : Fiber n) :
    ValueTransport.run (fun _ => (identityAlternative n).toValueIso) w x ≈
      ValueTransport.run (fun _ => (LinearIso.identity n).toValueIso) w x :=
  ValueTransport.run_forward_generators_congr (V := Fiber n) (I := Bool)
    (fun _ => (identityAlternative n).toValueIso)
    (fun _ => (LinearIso.identity n).toValueIso)
    (fun _ x => (show Fiber.add (Fiber.zero n) x ≈ x from Fiber.zero_add x)) w x

/-- A concrete finite coordinate permutation. -/
def swapIndex (i : Fin 2) : Fin 2 := if i.val = 0 then 1 else 0

theorem swapIndex_twice (i : Fin 2) : swapIndex (swapIndex i) = i := by
  apply Fin.ext
  by_cases h : i.val = 0
  · simp [swapIndex, h]
  · have hi : i.val = 1 := by omega
    simp [swapIndex, hi]

def swap : LinearIso 2 2 := LinearIso.reindex swapIndex swapIndex swapIndex_twice swapIndex_twice

def zeroMap (n : Nat) : ValueMap (Fiber n) (Fiber n) :=
  ⟨fun _ => Fiber.zero n, fun _ => Setoid.refl _⟩

theorem zeroMap_linear (n : Nat) : IsLinear (zeroMap n) :=
  ⟨fun _ _ => Setoid.symm (Fiber.zero_add (Fiber.zero n)),
    fun a _ => Setoid.symm (Fiber.scale_zero a)⟩

/-- Constant matrix system with the swap matrix, all higher coefficients zero. -/
def swapSystem (k : Nat) : ValueMap (Fiber 2) (Fiber 2) :=
  if k = 0 then swap.toValueIso.forward else zeroMap 2

theorem swapSystem_linear (k : Nat) : IsLinear (swapSystem k) := by
  unfold swapSystem
  split
  · exact swap.linear
  · exact zeroMap_linear 2

def initial : Fiber 2 :=
  ⟨fun i => ComplexRaw.ofQComplex (QComplex.ofRat (if i.val = 0 then 1 else 2)),
    fun _ => ComplexRaw.ofQComplex_valid _⟩

/-- Constructed formal solution, without assuming an endpoint formula. -/
theorem swapSystem_solution : LocalSystem.CoefficientSolution swapSystem
    (LocalSystem.coefficient swapSystem initial) initial :=
  LocalSystem.coefficient_solution swapSystem initial

theorem swapSystem_superposition (k : Nat) :
    IsLinear (LocalSystem.coefficientMap swapSystem k) :=
  LocalSystem.coefficientMap_linear swapSystem swapSystem_linear k

/-- Scalar constant coefficient system whose finite values start the
exponential series. The example does not assert convergence of that series. -/
def unitCoefficient (k : Nat) : ComplexRaw :=
  if k = 0 then ComplexRaw.one else ComplexRaw.zero

theorem unitCoefficient_valid (k : Nat) : (unitCoefficient k).Valid := by
  unfold unitCoefficient
  split <;> exact ComplexRaw.ofQComplex_valid _

theorem exponential_formal_solution : LocalODE.CoefficientSolution unitCoefficient
    (LocalODE.coefficient unitCoefficient ComplexRaw.one) ComplexRaw.one :=
  LocalODE.coefficient_solution unitCoefficient ComplexRaw.one unitCoefficient_valid
    (ComplexRaw.ofQComplex_valid QComplex.one)

/-- Genuine holomorphic coordinate solutions of the zero system, with
arbitrary represented initial data. -/
def zeroSystemCoordinate (x : Fiber n) (i : Fin n) :
    FunctionTheory.Holomorphic (ConstantSolution.scalarMap ⟨x.val i, x.property i⟩) :=
  ConstantSolution.holomorphic ⟨x.val i, x.property i⟩

end ComputableAnalysis.RiemannHilbert.PrerequisiteExamples
