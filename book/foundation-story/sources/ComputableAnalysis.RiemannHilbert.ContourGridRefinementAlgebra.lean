import ComputableAnalysis.RiemannHilbert.ContourRadiusConcatenation
import ComputableAnalysis.RiemannHilbert.RationalDilation

/-! Finite block reindexing and repeated coarse weights. These are exact
represented-value identities, independent of continuity or a chosen limit. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

theorem gridValueSum_constant (n : Nat) (a : ScalarAlgebra.Value) :
    gridValueSum n (fun _ => a)=(n:ScalarAlgebra.Value)*a := by
  induction n with
  | zero => change 0=0*a; grind only
  | succ n ih =>
    rw [gridValueSum,ih]
    change (n:ScalarAlgebra.Value)*a+a=ScalarAlgebra.natural (n+1)*a
    rw [ScalarAlgebra.natural_succ]
    change ScalarAlgebra.natural n*a+a=(ScalarAlgebra.natural n+1)*a
    rw [ComplexRawQuotient.add_mul]
    change ScalarAlgebra.natural n*a+a=ScalarAlgebra.natural n*a+ScalarAlgebra.natural 1*a
    have h1 := ComplexRawQuotient.one_mul a
    change ScalarAlgebra.natural 1*a=a at h1
    rw [h1]

theorem gridValueSum_blocks (M F : Nat) (f : Nat → ScalarAlgebra.Value) :
    gridValueSum (M*F) f=gridValueSum M (fun j => gridValueSum F (fun t => f (j*F+t))) := by
  induction M with
  | zero => simp only [Nat.zero_mul,gridValueSum]
  | succ M ih =>
    rw [Nat.succ_mul,gridValueSum_concat,ih,gridValueSum]

theorem gridScalarSum_blocks (M F : Nat) (f : Nat → Scalar) :
    gridScalarSum (M*F) f ≈ gridScalarSum M (fun j => gridScalarSum F (fun t => f (j*F+t))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum (M*F) f).property)
    (hright := (gridScalarSum M (fun j => gridScalarSum F (fun t => f (j*F+t)))).property)
  change gridScalarValue (gridScalarSum (M*F) f)=
    gridScalarValue (gridScalarSum M (fun j => gridScalarSum F (fun t => f (j*F+t))))
  simp only [gridScalarSum_value]
  exact gridValueSum_blocks M F _

theorem gridScalarSum_constant (n : Nat) (a : Scalar) :
    gridScalarSum n (fun _ => a) ≈ scale (n:Rat) a := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum n (fun _ => a)).property)
    (hright := (scale (n:Rat) a).property)
  change gridScalarValue (gridScalarSum n (fun _ => a))=
    ComplexRawQuotient.scaleRat (n:Rat) (gridScalarValue a)
  rw [gridScalarSum_value,gridValueSum_constant,ScalarAlgebra.scale_natural]

theorem gridScalarSum_scaled_constant (n : Nat) (r : Rat) (a : Scalar) :
    gridScalarSum n (fun _ => scale r a) ≈ scale ((n:Rat)*r) a :=
  Setoid.trans (gridScalarSum_constant n (scale r a))
    (scaleRat_scaleRat_equiv (n:Rat) r a.val a.property)

theorem gridScalarSum_sub_agreement (M : Nat) (f g : Nat → Scalar) :
    gridScalarSum M (fun j => gridScalarSub (f j) (g j)) ≈
      gridScalarSub (gridScalarSum M f) (gridScalarSum M g) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum M (fun j => gridScalarSub (f j) (g j))).property)
    (hright := (gridScalarSub (gridScalarSum M f) (gridScalarSum M g)).property)
  change gridScalarValue (gridScalarSum M (fun j => gridScalarSub (f j) (g j)))=
    gridScalarValue (gridScalarSub (gridScalarSum M f) (gridScalarSum M g))
  simp only [gridScalarValue_sub,gridScalarSum_value,gridValueSum_sub]

theorem gridScalarDoubleSum_sub_agreement (M F : Nat) (f g : Nat → Nat → Scalar) :
    gridScalarSum M (fun j => gridScalarSum F (fun t => gridScalarSub (f j t) (g j t))) ≈
      gridScalarSub (gridScalarSum M (fun j => gridScalarSum F (f j)))
        (gridScalarSum M (fun j => gridScalarSum F (g j))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum M (fun j => gridScalarSum F (fun t => gridScalarSub (f j t) (g j t)))).property)
    (hright := (gridScalarSub (gridScalarSum M (fun j => gridScalarSum F (f j)))
      (gridScalarSum M (fun j => gridScalarSum F (g j)))).property)
  change gridScalarValue (gridScalarSum M (fun j => gridScalarSum F (fun t => gridScalarSub (f j t) (g j t))))=
    gridScalarValue (gridScalarSub (gridScalarSum M (fun j => gridScalarSum F (f j)))
      (gridScalarSum M (fun j => gridScalarSum F (g j))))
  simp only [gridScalarValue_sub,gridScalarSum_value,gridValueSum_sub]

end ComputableAnalysis.RiemannHilbert.RectangularContour
