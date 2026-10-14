import ComputableAnalysis.RiemannHilbert.ContourAffineCycles

/-! Finite shared-edge cancellation for arbitrary represented sample names. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

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

def gridScalarValue (x : Scalar) : ScalarAlgebra.Value := ComplexRawQuotient.ofRaw x.val x.property

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
theorem gridScalarSum_bound (n : Nat) (f : Nat → Scalar) (E : Rat) (_hE : 0≤E)
    (ht : ∀ j, j<n → Small (f j).val E) :
    Small (gridScalarSum n f).val ((n:Rat)*E) := by
  induction n with
  | zero =>
    change Small zero (0*E)
    rw [Rat.zero_mul]
    exact Small.zero Rat.le_refl
  | succ n ih =>
    have hb := LocalODE.small_add (ih (fun j hj => ht j (by omega))) (ht n (by omega))
    have he : (n:Rat)*E+E=((n+1:Nat):Rat)*E := by
      rw [Rat.natCast_add]
      change _=((n:Rat)+1)*E
      grind only
    rw [he] at hb
    exact hb

theorem gridScalarDoubleSum_bound (m n : Nat) (f : Nat → Nat → Scalar)
    (E : Rat) (hE : 0≤E) (ht : ∀ j k, j<m → k<n → Small (f j k).val E) :
    Small (gridScalarSum m (fun j => gridScalarSum n (f j))).val ((m:Rat)*((n:Rat)*E)) :=
  gridScalarSum_bound m _ _ (Rat.mul_nonneg Rat.natCast_nonneg hE)
    (fun j hj => gridScalarSum_bound n (f j) E hE (fun k hk => ht j k hj hk))

end ComputableAnalysis.RiemannHilbert.RectangularContour
