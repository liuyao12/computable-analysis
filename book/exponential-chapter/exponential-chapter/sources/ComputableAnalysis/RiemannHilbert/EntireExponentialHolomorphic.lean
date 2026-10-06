import ComputableAnalysis.RiemannHilbert.EntireMatrixExponential
import ComputableAnalysis.RiemannHilbert.DomainVectorLocality
import ComputableAnalysis.RiemannHilbert.HolomorphicMatrixAction

/-! Actual holomorphic witnesses for the entire represented matrix
exponential. Local witnesses agree on overlapping discs and therefore give
derivatives and continuity on the whole represented complex plane. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}

def discCoordinate (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (x : Fiber n) (i : Fin n) : CertifiedFunctions.Map :=
  BoundedSeries.seriesMap (fun k => (coefficient A x k).val i)
    (fun k => (coefficient A x k).property i)
    (2*discBudget A R.val*LocalSystem.initialBound x) (rate R.val) R.val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg A R.val)) (LocalSystem.initialBound_nonneg x))
    (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property))) (Rat.le_of_lt R.property)
    (fun k => operatorCoefficient_bound (coefficientMap A) _ _ _ (LocalSystem.initialBound_nonneg x)
      (disc_majorant A hA R.val (Rat.le_of_lt R.property)) x (LocalSystem.initialBound_valid x) k i)
    (rate_small R.val (Rat.le_of_lt R.property))

def discCoordinate_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (x : Fiber n) (i : Fin n) : CertifiedFunctions.Holomorphic (discCoordinate A hA R x i) :=
  BoundedSeries.seriesMap_holomorphic _ _ _ _ _
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg A R.val)) (LocalSystem.initialBound_nonneg x))
    (Rat.le_of_lt (rate_pos R.val (Rat.le_of_lt R.property))) (Rat.le_of_lt R.property)
    (fun k => operatorCoefficient_bound (coefficientMap A) _ _ _ (LocalSystem.initialBound_nonneg x)
      (disc_majorant A hA R.val (Rat.le_of_lt R.property)) x (LocalSystem.initialBound_valid x) k i)
    (rate_small R.val (Rat.le_of_lt R.property))

def discVector (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (x : Fiber n) : DomainVectorFunctions.Map n where
  domain := interior R.val
  eval z hz := (onDisc A hA R z hz).eval x
  domain_congr z w hzw := by
    constructor
    · rintro ⟨r, hr, hrR, hz⟩
      exact ⟨r, hr, hrR, Small.congr z.property w.property hzw hz⟩
    · rintro ⟨r, hr, hrR, hw⟩
      exact ⟨r, hr, hrR, Small.congr w.property z.property (equiv_symm hzw) hw⟩
  eval_congr z w hz hw hzw := onDisc_congr A A hA hA (fun _ => Setoid.refl _) R R z w hz hw hzw x x (Setoid.refl _)

def discVector_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (R : QPos) (x : Fiber n) : DomainVectorFunctions.Holomorphic (discVector A hA R x) where
  openDomain := ⟨interiorRadius R.val, interiorRadius_inside R.val⟩
  coordinates i := DomainFunctions.ofCertifiedHolomorphic (discCoordinate_holomorphic A hA R x i)

def vector (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (x : Fiber n) : DomainVectorFunctions.Map n where
  domain := fun _ => True
  eval z _ := (value A hA z).eval x
  domain_congr := fun _ _ _ => Iff.rfl
  eval_congr z w _ _ hzw := value_congr A A hA hA (fun _ => Setoid.refl _) z w hzw x x (Setoid.refl _)

def vector_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (x : Fiber n) :
    DomainVectorFunctions.Holomorphic (vector A hA x) :=
  DomainVectorFunctions.holomorphic_of_local (vector A hA x)
    (fun a _ => discVector A hA (pointRadius a) x)
    (fun a _ => discVector_holomorphic A hA (pointRadius a) x)
    (fun a _ => pointRadius_inside a) (fun _ _ _ _ => True.intro)
    (fun _ _ z hz => Setoid.symm (value_onDisc A hA _ z hz x))

def field (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    LinearField.Field (n := n) (m := n) (fun _ => True) :=
  fun z _ => value A hA z

theorem field_congr (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z w : Scalar) (_hz _hw : True) (hzw : z.val.Equiv w.val) : (field A hA z _hz).Equiv (field A hA w _hw) :=
  fun x => value_congr A A hA hA (fun _ => Setoid.refl _) z w hzw x x (Setoid.refl _)

def field_holomorphic (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) :
    LinearField.MatrixHolomorphic (field A hA) (fun _ _ _ => Iff.rfl) (field_congr A hA) :=
  fun i j => (vector_holomorphic A hA (Fiber.basis i)).coordinates j

theorem value_initial (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (x : Fiber n) :
    (value A hA ⟨zero, ofQComplex_valid _⟩).eval x ≈ x := by
  intro i
  exact BoundedSeries.seriesMap_initial _ _ _ _ _
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (discBudget_nonneg A _)) (LocalSystem.initialBound_nonneg x))
    (Rat.le_of_lt (rate_pos _ (Rat.le_of_lt (pointRadius ⟨zero, ofQComplex_valid _⟩).property)))
    (Rat.le_of_lt (pointRadius ⟨zero, ofQComplex_valid _⟩).property)
    (fun k => operatorCoefficient_bound (coefficientMap A) _ _ _ (LocalSystem.initialBound_nonneg x)
      (disc_majorant A hA _ (Rat.le_of_lt (pointRadius ⟨zero, ofQComplex_valid _⟩).property))
      x (LocalSystem.initialBound_valid x) k i)
    (rate_small _ (Rat.le_of_lt (pointRadius ⟨zero, ofQComplex_valid _⟩).property))

end ComputableAnalysis.RiemannHilbert.MatrixExponential
