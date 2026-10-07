import ComputableAnalysis.ModularForms.LatticeRectangleRows
import ComputableAnalysis.ModularForms.RepresentedSumRows
import ComputableAnalysis.ModularForms.UpperFiniteHolomorphic
import ComputableAnalysis.ModularForms.UpperSquarePrefixAgreement

/-! Exact row assembly of finite lattice squares, with certified lattice-sum tails. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory QuadraticOrder163

/-- The actual sum of nonzero lattice terms in a finite horizontal row. -/
def upperLatticeFiniteRow (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k N : Nat) (y : Int) : Scalar :=
  (upperFiniteMap k (latticeRowPoints N y)).eval z hz

/-- Assemble the finite square by its actual finite row values. -/
def upperLatticeRectangleSum (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k N : Nat) : ComplexRaw :=
  LocalODE.sum ((latticeCoordinates N).map (fun y => (upperLatticeFiniteRow z hz k N y).val))

theorem upperLatticeRectangleSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k N : Nat) : (upperLatticeRectangleSum z hz k N).Valid := by
  apply LocalODE.sum_valid
  intro zz hzz
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hzz
  exact (upperLatticeFiniteRow z hz k N y).property

private theorem pointSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (us : List QuadraticOrder163) :
    (LocalODE.sum (us.map (upperPointPower z hz k))).Valid := by
  apply LocalODE.sum_valid
  intro zz hzz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
  exact upperPointPower_valid z hz k u

/-- Finite row assembly agrees with the actual finite square-shell construction. -/
theorem upperLatticeRectangleSum_square (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k N : Nat) :
    (upperLatticeRectangleSum z hz k N).Equiv
      (LocalODE.sum ((squarePoints N).map (upperPointPower z hz k))) := by
  exact equiv_trans (upperLatticeRectangleSum_valid z hz k N)
    (pointSum_valid z hz k (latticeRectanglePoints N))
    (pointSum_valid z hz k (squarePoints N))
    (equiv_symm (representedSum_rows (upperPointPower z hz k)
      (upperPointPower_valid z hz k) (latticeRowPoints N) (latticeCoordinates N)))
    (representedSum_reindex (upperPointPower z hz k) (upperPointPower_valid z hz k)
      (latticeRectanglePoints_square_perm N))

theorem upperLatticeRectangleSum_weightFour_prefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    (upperLatticeRectangleSum z hz 4 (N+1)).Equiv (upperWeightFourPrefix z hz N) :=
  equiv_trans (upperLatticeRectangleSum_valid z hz 4 (N+1))
    (pointSum_valid z hz 4 (squarePoints (N+1)))
    (upperWeightFourPrefix_valid z hz N)
    (upperLatticeRectangleSum_square z hz 4 (N+1))
    (upperSquareWeightFour_prefix_equiv z hz N)

theorem upperLatticeRectangleSum_weightSix_prefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    (upperLatticeRectangleSum z hz 6 (N+1)).Equiv (upperWeightSixPrefix z hz N) :=
  equiv_trans (upperLatticeRectangleSum_valid z hz 6 (N+1))
    (pointSum_valid z hz 6 (squarePoints (N+1)))
    (upperWeightSixPrefix_valid z hz N)
    (upperLatticeRectangleSum_square z hz 6 (N+1))
    (upperSquareWeightSix_prefix_equiv z hz N)

/-- The constructed weight-four lattice sum has the same certified row approximants. -/
theorem upperWeightFourLatticeSum_close_rows (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperWeightFourLatticeSum z hz) (upperLatticeRectangleSum z hz 4 (N+1)))
      (upperWeightFourTailRate z hz N) :=
  Small.congr
    (sub_valid (upperWeightFourLatticeSum_valid z hz) (upperWeightFourPrefix_valid z hz N))
    (sub_valid (upperWeightFourLatticeSum_valid z hz) (upperLatticeRectangleSum_valid z hz 4 (N+1)))
    (FunctionTheory.sub_congr (equiv_refl _ (upperWeightFourLatticeSum_valid z hz))
      (equiv_symm (upperLatticeRectangleSum_weightFour_prefix z hz N)))
    (upperWeightFourLatticeSum_close_prefix z hz N)

theorem upperWeightSixLatticeSum_close_rows (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperWeightSixLatticeSum z hz) (upperLatticeRectangleSum z hz 6 (N+1)))
      (upperWeightSixTailRate z hz N) :=
  Small.congr
    (sub_valid (upperWeightSixLatticeSum_valid z hz) (upperWeightSixPrefix_valid z hz N))
    (sub_valid (upperWeightSixLatticeSum_valid z hz) (upperLatticeRectangleSum_valid z hz 6 (N+1)))
    (FunctionTheory.sub_congr (equiv_refl _ (upperWeightSixLatticeSum_valid z hz))
      (equiv_symm (upperLatticeRectangleSum_weightSix_prefix z hz N)))
    (upperWeightSixLatticeSum_close_prefix z hz N)

end ComputableAnalysis.ModularForms
