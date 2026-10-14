import ComputableAnalysis.ModularForms.RepresentedScalarValue
import ComputableAnalysis.ModularForms.RectangleSubdivisionSum

/-! Discrete Stokes for supplied valid represented edge samples.
Interior edges cancel as exact values, independently of interval names. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def gridValueSum : Nat → (Nat → ScalarAlgebra.Value) → ScalarAlgebra.Value
  | 0, _ => 0
  | n+1, f => gridValueSum n f+f n

theorem gridValueSum_add (n : Nat) (f g : Nat → ScalarAlgebra.Value) :
    gridValueSum n (fun j => f j+g j)=gridValueSum n f+gridValueSum n g := by
  induction n with
  | zero => simp only [gridValueSum]; grind only
  | succ n ih => simp only [gridValueSum,ih]; grind only

theorem gridValueSum_sub (n : Nat) (f g : Nat → ScalarAlgebra.Value) :
    gridValueSum n (fun j => f j-g j)=gridValueSum n f-gridValueSum n g := by
  induction n with
  | zero => simp only [gridValueSum]; grind only
  | succ n ih => simp only [gridValueSum,ih]; grind only

theorem gridValueSum_zero (n : Nat) : gridValueSum n (fun _ => (0:ScalarAlgebra.Value))=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gridValueSum,ih]; grind only

theorem gridValueSum_telescope (n : Nat) (f : Nat → ScalarAlgebra.Value) :
    gridValueSum n (fun j => f (j+1)-f j)=f n-f 0 := by
  induction n with
  | zero => simp only [gridValueSum]; grind only
  | succ n ih => simp only [gridValueSum,ih]; grind only

theorem gridValueSum_comm (m n : Nat) (f : Nat → Nat → ScalarAlgebra.Value) :
    gridValueSum m (fun j => gridValueSum n (f j))=
      gridValueSum n (fun k => gridValueSum m (fun j => f j k)) := by
  induction m with
  | zero => simp only [gridValueSum,gridValueSum_zero]
  | succ m ih => simp only [gridValueSum]; rw [gridValueSum_add,ih]

def gridValueCell (h v : Nat → Nat → ScalarAlgebra.Value) (j k : Nat) : ScalarAlgebra.Value :=
  (h j k-h j (k+1))+(v (j+1) k-v j k)

def gridValueBoundary (h v : Nat → Nat → ScalarAlgebra.Value) (m n : Nat) : ScalarAlgebra.Value :=
  gridValueSum m (fun j => h j 0-h j n)+gridValueSum n (fun k => v m k-v 0 k)

theorem gridValue_discrete_stokes (h v : Nat → Nat → ScalarAlgebra.Value) (m n : Nat) :
    gridValueSum m (fun j => gridValueSum n (fun k => gridValueCell h v j k))=
      gridValueBoundary h v m n := by
  unfold gridValueCell gridValueBoundary
  simp only [gridValueSum_add]
  congr 1
  · congr 1
    funext j
    have hb := gridValueSum_telescope n (h j)
    rw [gridValueSum_sub] at hb ⊢
    grind only
  · rw [gridValueSum_comm]
    congr 1
    funext k
    exact gridValueSum_telescope m (fun j => v j k)

def gridScalarSub (a b : Scalar) : Scalar := ⟨sub a.val b.val,sub_valid a.property b.property⟩
def gridScalarSum : Nat → (Nat → Scalar) → Scalar
  | 0, _ => ⟨zero,ofQComplex_valid _⟩
  | n+1, f => scalarSum (gridScalarSum n f) (f n)
def gridScalarCell (h v : Nat → Nat → Scalar) (j k : Nat) : Scalar :=
  scalarSum (gridScalarSub (h j k) (h j (k+1))) (gridScalarSub (v (j+1) k) (v j k))
def gridScalarBoundary (h v : Nat → Nat → Scalar) (m n : Nat) : Scalar :=
  scalarSum (gridScalarSum m (fun j => gridScalarSub (h j 0) (h j n)))
    (gridScalarSum n (fun k => gridScalarSub (v m k) (v 0 k)))


theorem gridScalarValue_add (a b : Scalar) :
    gridScalarValue (scalarSum a b)=gridScalarValue a+gridScalarValue b :=
  ComplexRawQuotient.ofRaw_add a.val b.val a.property b.property

theorem gridScalarValue_sub (a b : Scalar) :
    gridScalarValue (gridScalarSub a b)=gridScalarValue a-gridScalarValue b := by
  change ComplexRawQuotient.ofRaw (add a.val (neg b.val))
    (add_valid a.property (neg_valid b.property))=_
  rw [ComplexRawQuotient.ofRaw_add,ComplexRawQuotient.ofRaw_neg]
  · rfl
  · exact neg_valid b.property

theorem gridScalarSum_value (n : Nat) (f : Nat → Scalar) :
    gridScalarValue (gridScalarSum n f)=gridValueSum n (fun j => gridScalarValue (f j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change gridScalarValue (scalarSum (gridScalarSum n f) (f n))=_
    rw [gridScalarValue_add,ih]
    rfl

theorem representedGrid_discrete_stokes (h v : Nat → Nat → Scalar) (m n : Nat) :
    (gridScalarSum m (fun j => gridScalarSum n (fun k => gridScalarCell h v j k))).val.Equiv
      (gridScalarBoundary h v m n).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum m (fun j => gridScalarSum n (fun k => gridScalarCell h v j k))).property)
    (hright := (gridScalarBoundary h v m n).property)
  change gridScalarValue (gridScalarSum m (fun j => gridScalarSum n (fun k => gridScalarCell h v j k)))=
    gridScalarValue (gridScalarBoundary h v m n)
  simp only [gridScalarSum_value,gridScalarCell,gridScalarBoundary,
    gridScalarValue_add,gridScalarValue_sub]
  exact gridValue_discrete_stokes (fun j k => gridScalarValue (h j k))
    (fun j k => gridScalarValue (v j k)) m n

end ComputableAnalysis.ModularForms
