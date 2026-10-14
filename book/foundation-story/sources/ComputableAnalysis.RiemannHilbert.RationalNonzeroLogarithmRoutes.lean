import ComputableAnalysis.RiemannHilbert.RationalLogarithmMeshes
import ComputableAnalysis.RiemannHilbert.ContinuedJordanLogarithm

/-! A literal three-segment route from one to every nonzero rational
complex point. Directed-coordinate separation is constructed on each leg,
and the proved mesh algorithm produces a genuine logarithm continuation. -/
namespace ComputableAnalysis.RiemannHilbert.RationalNonzeroLogarithmRoutes
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch ReciprocalExamples LogarithmContinuation
open RationalSeparatedSegments ContinuedJordanLogarithm
set_option maxHeartbeats 1000000

def side (c : QComplex) : Rat := if 0 ≤ c.im then 1 else -1
def firstCorner (c : QComplex) : QComplex := ⟨1,side c⟩
def secondCorner (c : QComplex) : QComplex := ⟨c.re,side c⟩

def firstSeparation (c : QComplex) : Separation QComplex.one (firstCorner c) where
  axis := .real
  positive := true
  gap := ⟨1,by decide +kernel⟩
  lower_left := by change (1 : Rat) ≤ 1; decide +kernel
  lower_right := by change (1 : Rat) ≤ 1; decide +kernel

def secondSeparation (c : QComplex) : Separation (firstCorner c) (secondCorner c) where
  axis := .imag
  positive := decide (0 ≤ c.im)
  gap := ⟨1,by decide +kernel⟩
  lower_left := by by_cases hi : 0 ≤ c.im <;> simp [directed,coordinate,firstCorner,side,hi] <;> decide +kernel
  lower_right := by by_cases hi : 0 ≤ c.im <;> simp [directed,coordinate,secondCorner,side,hi] <;> decide +kernel

private theorem min_one_pos (r : Rat) (hr : 0 < r) : 0 < min 1 r := by grind

def finalSeparation (c : QComplex) (hc : QComplex.normSq c ≠ 0) : Separation (secondCorner c) c :=
  if hr : 0 < c.re then {
    axis := .real, positive := true, gap := ⟨c.re,hr⟩
    lower_left := Rat.le_refl, lower_right := Rat.le_refl }
  else if hr : c.re < 0 then {
    axis := .real, positive := false, gap := ⟨-c.re,by grind only⟩
    lower_left := Rat.le_refl, lower_right := Rat.le_refl }
  else if hi : 0 < c.im then {
    axis := .imag, positive := true, gap := ⟨min 1 c.im,min_one_pos c.im hi⟩
    lower_left := by have h : 0 ≤ c.im := Rat.le_of_lt hi; simp only [directed,coordinate,secondCorner,side,if_pos h,if_true]; grind
    lower_right := by change min 1 c.im ≤ c.im; grind }
  else {
    axis := .imag, positive := false
    gap := ⟨min 1 (-c.im),by
      have hre : c.re=0 := by grind only
      have him : c.im ≠ 0 := by
        intro him
        apply hc
        unfold QComplex.normSq
        rw [hre,him]
        decide +kernel
      have hneg : 0 < -c.im := by grind only
      exact min_one_pos _ hneg⟩
    lower_left := by
      have hre : c.re=0 := by grind only
      have him : c.im ≠ 0 := by
        intro him
        apply hc
        unfold QComplex.normSq
        rw [hre,him]
        decide +kernel
      have hn : ¬ 0 ≤ c.im := by grind only
      simp only [directed,coordinate,secondCorner,side,if_neg hn,Bool.false_eq_true,if_false]
      grind
    lower_right := by change min 1 (-c.im) ≤ -c.im; grind }

def route (c : QComplex) (hc : QComplex.normSq c ≠ 0) : Chain oneScalar one_nonzero (rational c) (rational_nonzero c hc) :=
  append (RationalLogarithmMeshes.chain QComplex.one (firstCorner c) (firstSeparation c))
    (append (RationalLogarithmMeshes.chain (firstCorner c) (secondCorner c) (secondSeparation c))
      (RationalLogarithmMeshes.chain (secondCorner c) c (finalSeparation c hc)))

def scalarLog (c : QComplex) (hc : QComplex.normSq c ≠ 0) : Scalar := value (route c hc) zeroSeed

theorem scalarLog_exponential (c : QComplex) (hc : QComplex.normSq c ≠ 0) :
    (MatrixExponential.scalarExponential (scalarLog c hc)).val.Equiv (rational c).val :=
  value_exponential (route c hc) zeroSeed MatrixExponential.scalarExponential_zero

def germ (c : QComplex) (hc : QComplex.normSq c ≠ 0) := terminalFunction (route c hc) zeroSeed
def germ_holomorphic (c : QComplex) (hc : QComplex.normSq c ≠ 0) : DomainFunctions.Holomorphic (germ c hc) :=
  terminalHolomorphic (route c hc) zeroSeed

theorem path_nonzero (c : QComplex) (hc : QComplex.normSq c ≠ 0) (t : UnitInterval.Point) :
    Nonzero ((path (route c hc)).eval t) := LogarithmContinuation.path_nonzero (route c hc) t

end ComputableAnalysis.RiemannHilbert.RationalNonzeroLogarithmRoutes
