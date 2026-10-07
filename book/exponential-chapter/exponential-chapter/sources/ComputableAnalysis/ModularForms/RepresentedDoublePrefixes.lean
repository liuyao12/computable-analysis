import ComputableAnalysis.RiemannHilbert.GeometricSeries

/-! Exact interchange of finite double prefixes of actual represented complex terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

private theorem prefix_zero (M : Nat) :
    FiniteProducts.partialSum (fun _ => (0:ScalarAlgebra.Value)) M=0 := by
  induction M with
  | zero => rfl
  | succ M ih => rw [FiniteProducts.partialSum,ih]; exact ComplexRawQuotient.add_zero _

private theorem prefix_transpose (f : Nat → Nat → ScalarAlgebra.Value) (N M : Nat) :
    FiniteProducts.partialSum (fun n => FiniteProducts.partialSum (f n) M) N=
      FiniteProducts.partialSum (fun m => FiniteProducts.partialSum (fun n => f n m) N) M := by
  induction N with
  | zero => exact (prefix_zero M).symm
  | succ N ih =>
    have he : (fun m => FiniteProducts.partialSum (fun n => f n m) (N+1))=
        (fun m => FiniteProducts.partialSum (fun n => f n m) N+f N m) := by
      funext m
      rfl
    rw [he,FiniteProducts.prefix_add]
    change FiniteProducts.partialSum (fun n => FiniteProducts.partialSum (f n) M) N+
      FiniteProducts.partialSum (f N) M=_
    rw [ih]

/-- Finite row and column assembly computes the same represented value. -/
theorem representedDoublePrefix_transpose (t : Nat → Nat → ComplexRaw)
    (ht : ∀ n m, (t n m).Valid) (N M : Nat) :
    (ScalarSeries.block (fun n => ScalarSeries.block (t n) 0 M) 0 N).Equiv
      (ScalarSeries.block (fun m => ScalarSeries.block (fun n => t n m) 0 N) 0 M) := by
  have hv n := ScalarSeries.block_valid (t n) (ht n) 0 M
  have hw m := ScalarSeries.block_valid (fun n => t n m) (fun n => ht n m) 0 N
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ScalarSeries.block_valid _ hv 0 N)
    (hright := ScalarSeries.block_valid _ hw 0 M)
  rw [ScalarSeries.prefix_image _ hv,ScalarSeries.prefix_image _ hw]
  have hl : (fun n => ComplexRawQuotient.ofRaw (ScalarSeries.block (t n) 0 M) (hv n))=
      (fun n => FiniteProducts.partialSum (fun m => ComplexRawQuotient.ofRaw (t n m) (ht n m)) M) := by
    funext n
    exact ScalarSeries.prefix_image (t n) (ht n) M
  have hr : (fun m => ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => t n m) 0 N) (hw m))=
      (fun m => FiniteProducts.partialSum (fun n => ComplexRawQuotient.ofRaw (t n m) (ht n m)) N) := by
    funext m
    exact ScalarSeries.prefix_image (fun n => t n m) (fun n => ht n m) N
  rw [hl,hr]
  exact prefix_transpose _ N M

/-- Literal shift of the block evaluator; no convergence or value quotient is needed. -/
theorem representedBlock_shift (t : Nat → ComplexRaw) (A N : Nat) :
    ScalarSeries.block t A N=ScalarSeries.block (fun n => t (A+n)) 0 N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [ScalarSeries.block.eq_2,ScalarSeries.block.eq_2,ih,Nat.zero_add]

end ComputableAnalysis.ModularForms
