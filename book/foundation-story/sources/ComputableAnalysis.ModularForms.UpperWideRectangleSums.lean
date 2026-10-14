import ComputableAnalysis.ModularForms.LatticeWideRectangles
import ComputableAnalysis.ModularForms.UpperPositiveSquareAssembly
import ComputableAnalysis.ModularForms.UpperFilteredPointBounds
import ComputableAnalysis.ModularForms.RepresentedFilteredDifference
import ComputableAnalysis.ModularForms.LatticeBasisCauchy163

/-! Actual wide-rectangle approximations of the lattice sums, uniformly in horizontal width. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory QuadraticOrder163

private theorem pointSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (us : List QuadraticOrder163) :
    (LocalODE.sum (us.map (upperPointPower z hz k))).Valid := by
  apply LocalODE.sum_valid
  intro zz hzz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
  exact upperPointPower_valid z hz k u

def upperWideRectangleSum (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) : ComplexRaw :=
  LocalODE.sum ((latticeWideRectanglePoints M N).map (upperPointPower z hz k))

theorem upperWideRectangleSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) : (upperWideRectangleSum z hz k M N).Valid :=
  pointSum_valid z hz k _

/-- The selected square-point evaluator agrees with independently assembled rows. -/
theorem upperWideRectangleSum_rows (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k M N : Nat) (hNM : N≤M) :
    (upperWideRectangleSum z hz k M N).Equiv (upperLatticeFiniteRowsSum z hz k M N) :=
  equiv_trans (upperWideRectangleSum_valid z hz k M N)
    (pointSum_valid z hz k ((latticeCoordinates N).flatMap (latticeRowPoints M)))
    (upperLatticeFiniteRowsSum_valid z hz k M N)
    (representedSum_reindex (upperPointPower z hz k) (upperPointPower_valid z hz k)
      (latticeWideRectanglePoints_rows_perm M N hNM))
    (representedSum_rows (upperPointPower z hz k) (upperPointPower_valid z hz k)
      (latticeRowPoints M) (latticeCoordinates N))

theorem upperWideRectangleSum_weightFour_gap (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M N : Nat) (hN : 0<N) :
    Small (sub (LocalODE.sum ((squarePoints M).map (upperPointPower z hz 4)))
      (upperWideRectangleSum z hz 4 M N))
      (upperWeightFourTailConstant z hz*reciprocalSquare N) := by
  have he := representedSum_filter_difference (upperPointPower z hz 4)
    (upperPointPower_valid z hz 4) (wideRectangleKeep N) (squarePoints M)
  have hb := upperFiniteSubsetWeightFour_small z hz N M hN
    ((squarePoints M).filter (fun u => !wideRectangleKeep N u))
    (List.Pairwise.filter _ (squarePoints_nodup M)) (wideRectangle_discarded_annulus M N)
  exact Small.congr (pointSum_valid z hz 4 _)
    (sub_valid (pointSum_valid z hz 4 _) (upperWideRectangleSum_valid z hz 4 M N))
    (equiv_symm he) hb

theorem upperWideRectangleSum_weightSix_gap (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M N : Nat) (hN : 0<N) :
    Small (sub (LocalODE.sum ((squarePoints M).map (upperPointPower z hz 6)))
      (upperWideRectangleSum z hz 6 M N))
      (upperWeightSixTailConstant z hz*reciprocalSquare N) := by
  have he := representedSum_filter_difference (upperPointPower z hz 6)
    (upperPointPower_valid z hz 6) (wideRectangleKeep N) (squarePoints M)
  have hb := upperFiniteSubsetWeightSix_small z hz N M hN
    ((squarePoints M).filter (fun u => !wideRectangleKeep N u))
    (List.Pairwise.filter _ (squarePoints_nodup M)) (wideRectangle_discarded_annulus M N)
  exact Small.congr (pointSum_valid z hz 6 _)
    (sub_valid (pointSum_valid z hz 6 _) (upperWideRectangleSum_valid z hz 6 M N))
    (equiv_symm he) hb

private theorem small_triangle (F p q : ComplexRaw) (hF : F.Valid) (hp : p.Valid) (hq : q.Valid)
    (a b : Rat) (h1 : Small (sub F p) a) (h2 : Small (sub p q) b) :
    Small (sub F q) (a+b) := by
  have he : (add (sub F p) (sub p q)).Equiv (sub F q) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid hF hp) (sub_valid hp hq)) (hright := sub_valid hF hq)
    change (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)+
      (ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq)=
      ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw q hq
    grind only
  exact Small.congr (add_valid (sub_valid hF hp) (sub_valid hp hq))
    (sub_valid hF hq) he (LocalODE.small_add h1 h2)

/-- The full lattice sum is uniformly close to every sufficiently wide rectangle. -/
theorem upperWeightFourLatticeSum_close_wideRectangle (z : Scalar)
    (hz : InUpperHalfPlane z.val) (L N : Nat) (hN : 0<N) (hNM : N≤L+1) :
    Small (sub (upperWeightFourLatticeSum z hz) (upperWideRectangleSum z hz 4 (L+1) N))
      (2*upperWeightFourTailConstant z hz*reciprocalSquare N) := by
  have hC : 0≤upperWeightFourTailConstant z hz := by
    unfold upperWeightFourTailConstant
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))
  have hc := Small.congr
    (sub_valid (upperWeightFourLatticeSum_valid z hz) (upperWeightFourPrefix_valid z hz L))
    (sub_valid (upperWeightFourLatticeSum_valid z hz) (pointSum_valid z hz 4 (squarePoints (L+1))))
    (FunctionTheory.sub_congr (equiv_refl _ (upperWeightFourLatticeSum_valid z hz))
      (equiv_symm (upperSquareWeightFour_prefix_equiv z hz L)))
    (upperWeightFourLatticeSum_close_prefix z hz L)
  have h := small_triangle _ _ _ (upperWeightFourLatticeSum_valid z hz)
    (pointSum_valid z hz 4 (squarePoints (L+1))) (upperWideRectangleSum_valid z hz 4 (L+1) N) _ _
    (hc.mono (Rat.mul_le_mul_of_nonneg_left (reciprocalSquare_antitone N (L+1) hN hNM) hC))
    (upperWideRectangleSum_weightFour_gap z hz (L+1) N hN)
  have he : upperWeightFourTailConstant z hz*reciprocalSquare N+
      upperWeightFourTailConstant z hz*reciprocalSquare N=
      2*upperWeightFourTailConstant z hz*reciprocalSquare N := by grind only
  rw [he] at h
  exact h

theorem upperWeightSixLatticeSum_close_wideRectangle (z : Scalar)
    (hz : InUpperHalfPlane z.val) (L N : Nat) (hN : 0<N) (hNM : N≤L+1) :
    Small (sub (upperWeightSixLatticeSum z hz) (upperWideRectangleSum z hz 6 (L+1) N))
      (2*upperWeightSixTailConstant z hz*reciprocalSquare N) := by
  have hC : 0≤upperWeightSixTailConstant z hz := by
    unfold upperWeightSixTailConstant
    exact Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) (latticeReciprocalConstant_nonnegative z hz)))
  have hc := Small.congr
    (sub_valid (upperWeightSixLatticeSum_valid z hz) (upperWeightSixPrefix_valid z hz L))
    (sub_valid (upperWeightSixLatticeSum_valid z hz) (pointSum_valid z hz 6 (squarePoints (L+1))))
    (FunctionTheory.sub_congr (equiv_refl _ (upperWeightSixLatticeSum_valid z hz))
      (equiv_symm (upperSquareWeightSix_prefix_equiv z hz L)))
    (upperWeightSixLatticeSum_close_prefix z hz L)
  have h := small_triangle _ _ _ (upperWeightSixLatticeSum_valid z hz)
    (pointSum_valid z hz 6 (squarePoints (L+1))) (upperWideRectangleSum_valid z hz 6 (L+1) N) _ _
    (hc.mono (Rat.mul_le_mul_of_nonneg_left (reciprocalSquare_antitone N (L+1) hN hNM) hC))
    (upperWideRectangleSum_weightSix_gap z hz (L+1) N hN)
  have he : upperWeightSixTailConstant z hz*reciprocalSquare N+
      upperWeightSixTailConstant z hz*reciprocalSquare N=
      2*upperWeightSixTailConstant z hz*reciprocalSquare N := by grind only
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
