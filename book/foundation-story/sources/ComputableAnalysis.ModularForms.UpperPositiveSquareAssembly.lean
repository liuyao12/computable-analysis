import ComputableAnalysis.ModularForms.UpperEvenLatticeRows

/-! Finite even-weight lattice squares as a horizontal row and doubled positive rows. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory QuadraticOrder163

/-- Actual positive-height finite rows, at fixed horizontal cutoff. -/
def upperLatticePositiveRowsPrefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => (upperLatticeFiniteRow z hz k M ((n+1:Nat):Int)).val) 0 N

theorem upperLatticePositiveRowsPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) : (upperLatticePositiveRowsPrefix z hz k M N).Valid :=
  ScalarSeries.block_valid _ (fun n => (upperLatticeFiniteRow z hz k M ((n+1:Nat):Int)).property) 0 N

private def rowClass (z : Scalar) (hz : InUpperHalfPlane z.val) (k M : Nat)
    (y : Int) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (upperLatticeFiniteRow z hz k M y).val
    (upperLatticeFiniteRow z hz k M y).property

private def positiveClass (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (upperLatticePositiveRowsPrefix z hz k M N)
    (upperLatticePositiveRowsPrefix_valid z hz k M N)

private theorem positiveClass_succ (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) : positiveClass z hz k M (N+1)=
      positiveClass z hz k M N+rowClass z hz k M ((N+1:Nat):Int) := by
  change positiveClass z hz k M N+rowClass z hz k M ((0+N+1:Nat):Int)=_
  rw [Nat.zero_add]

private theorem scale_two (x : ScalarAlgebra.Value) :
    ComplexRawQuotient.scaleRat 2 x=x+x := by
  have h := ComplexRawQuotient.add_scaleRat (1:Rat) (1:Rat) x
  simp only [ComplexRawQuotient.scaleRat_one] at h
  have hr : (1:Rat)+1=2 := by decide +kernel
  rw [hr] at h
  exact h.symm

private theorem evenRow_symmetric (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) :
    symmetricLatticeSum (rowClass z hz (2*k) M) N=
      rowClass z hz (2*k) M 0+ComplexRawQuotient.scaleRat 2 (positiveClass z hz (2*k) M N) := by
  induction N with
  | zero =>
    change rowClass z hz (2*k) M 0=
      rowClass z hz (2*k) M 0+ComplexRawQuotient.scaleRat 2 0
    have hzero := ComplexRawQuotient.scaleRat_zero (2:Rat)
    have hadd := ComplexRawQuotient.add_zero (rowClass z hz (2*k) M 0)
    exact (congrArg (fun v => rowClass z hz (2*k) M 0+v) hzero).trans hadd |>.symm
  | succ N ih =>
    have hneg : rowClass z hz (2*k) M (-((N+1:Nat):Int))=
        rowClass z hz (2*k) M ((N+1:Nat):Int) :=
      ComplexRawQuotient.ofRaw_eq_ofRaw (upperLatticeFiniteRow_even_neg z hz k M ((N+1:Nat):Int))
    rw [symmetricLatticeSum.eq_2,positiveClass_succ,ih,hneg,
      ComplexRawQuotient.scaleRat_add]
    simp only [scale_two]
    grind only

/-- Actual finite row assembly with independent horizontal and vertical cutoffs. -/
def upperLatticeFiniteRowsSum (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) : ComplexRaw :=
  LocalODE.sum ((latticeCoordinates N).map (fun y => (upperLatticeFiniteRow z hz k M y).val))

theorem upperLatticeFiniteRowsSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) : (upperLatticeFiniteRowsSum z hz k M N).Valid := by
  apply LocalODE.sum_valid
  intro zz hzz
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hzz
  exact (upperLatticeFiniteRow z hz k M y).property

theorem upperLatticeFiniteRowsSum_even_positiveRows (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k M N : Nat) :
    (upperLatticeFiniteRowsSum z hz (2*k) M N).Equiv
      (ComplexRaw.add (upperLatticeFiniteRow z hz (2*k) M 0).val
        (scaleRat 2 (upperLatticePositiveRowsPrefix z hz (2*k) M N))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := upperLatticeFiniteRowsSum_valid z hz (2*k) M N)
    (hright := add_valid (upperLatticeFiniteRow z hz (2*k) M 0).property
      (scaleRat_valid (r := (2:Rat)) (upperLatticePositiveRowsPrefix_valid z hz (2*k) M N)))
  change ComplexRawQuotient.ofRaw
    (LocalODE.sum ((latticeCoordinates N).map (fun y => (upperLatticeFiniteRow z hz (2*k) M y).val))) _=
      rowClass z hz (2*k) M 0+ComplexRawQuotient.scaleRat 2 (positiveClass z hz (2*k) M N)
  rw [representedSum_latticeCoordinates]
  exact evenRow_symmetric z hz k M N

/-- Exact decomposition of the actual rectangular sum, for every even weight. -/
theorem upperLatticeRectangleSum_even_positiveRows (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k N : Nat) :
    (upperLatticeRectangleSum z hz (2*k) N).Equiv
      (ComplexRaw.add (upperLatticeFiniteRow z hz (2*k) N 0).val
        (scaleRat 2 (upperLatticePositiveRowsPrefix z hz (2*k) N N))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := upperLatticeRectangleSum_valid z hz (2*k) N)
    (hright := add_valid (upperLatticeFiniteRow z hz (2*k) N 0).property
      (scaleRat_valid (r := (2:Rat)) (upperLatticePositiveRowsPrefix_valid z hz (2*k) N N)))
  change ComplexRawQuotient.ofRaw
    (LocalODE.sum ((latticeCoordinates N).map (fun y => (upperLatticeFiniteRow z hz (2*k) N y).val))) _=
      rowClass z hz (2*k) N 0+ComplexRawQuotient.scaleRat 2 (positiveClass z hz (2*k) N N)
  rw [representedSum_latticeCoordinates]
  exact evenRow_symmetric z hz k N N

theorem upperWeightFourLatticeSum_close_positiveRows (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperWeightFourLatticeSum z hz)
      (ComplexRaw.add (upperLatticeFiniteRow z hz 4 (N+1) 0).val
        (scaleRat 2 (upperLatticePositiveRowsPrefix z hz 4 (N+1) (N+1)))))
      (upperWeightFourTailRate z hz N) :=
  Small.congr
    (sub_valid (upperWeightFourLatticeSum_valid z hz) (upperLatticeRectangleSum_valid z hz 4 (N+1)))
    (sub_valid (upperWeightFourLatticeSum_valid z hz)
      (add_valid (upperLatticeFiniteRow z hz 4 (N+1) 0).property
        (scaleRat_valid (upperLatticePositiveRowsPrefix_valid z hz 4 (N+1) (N+1)))))
    (FunctionTheory.sub_congr (equiv_refl _ (upperWeightFourLatticeSum_valid z hz))
      (upperLatticeRectangleSum_even_positiveRows z hz 2 (N+1)))
    (upperWeightFourLatticeSum_close_rows z hz N)

theorem upperWeightSixLatticeSum_close_positiveRows (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperWeightSixLatticeSum z hz)
      (ComplexRaw.add (upperLatticeFiniteRow z hz 6 (N+1) 0).val
        (scaleRat 2 (upperLatticePositiveRowsPrefix z hz 6 (N+1) (N+1)))))
      (upperWeightSixTailRate z hz N) :=
  Small.congr
    (sub_valid (upperWeightSixLatticeSum_valid z hz) (upperLatticeRectangleSum_valid z hz 6 (N+1)))
    (sub_valid (upperWeightSixLatticeSum_valid z hz)
      (add_valid (upperLatticeFiniteRow z hz 6 (N+1) 0).property
        (scaleRat_valid (upperLatticePositiveRowsPrefix_valid z hz 6 (N+1) (N+1)))))
    (FunctionTheory.sub_congr (equiv_refl _ (upperWeightSixLatticeSum_valid z hz))
      (upperLatticeRectangleSum_even_positiveRows z hz 3 (N+1)))
    (upperWeightSixLatticeSum_close_rows z hz N)

end ComputableAnalysis.ModularForms
