import ComputableAnalysis.ModularForms.UpperWideRectangleSums
import ComputableAnalysis.ModularForms.FiniteSumDifference

/-! Constructed horizontal lattice rows with uniform inverse-square truncation errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory QuadraticOrder163

private theorem rowPointSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (w : Nat) (us : List QuadraticOrder163) :
    (LocalODE.sum (us.map (upperPointPower z hz w))).Valid := by
  apply LocalODE.sum_valid
  intro zz hzz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
  exact upperPointPower_valid z hz w u

private theorem row_missing_bounds (M N : Nat) (u : QuadraticOrder163)
    (hu : u ∈ (latticeRowPoints M 0).filter (fun u => !decide (u ∈ latticeRowPoints N 0))) :
    u≠QuadraticOrder163.zero ∧ N<shellRadius u ∧ shellRadius u≤N+M := by
  obtain ⟨hm,hn⟩ := List.mem_filter.mp hu
  have hb := (mem_latticeRowPoints u M 0).mp hm
  have hnot : u ∉ latticeRowPoints N 0 := by
    intro he
    simp [he] at hn
  have hr : shellRadius u≤M := by
    apply (shellRadius_le_iff u M).mpr
    exact ⟨hb.2.2.1,hb.2.2.2,by omega,by omega⟩
  have hout : N<shellRadius u := by
    apply Classical.byContradiction
    intro he
    have hc := (shellRadius_le_iff u N).mp (show shellRadius u≤N by omega)
    exact hnot ((mem_latticeRowPoints u N 0).mpr ⟨hb.1,hb.2.1,hc.1,hc.2.1⟩)
  exact ⟨hb.1,hout,by omega⟩

private theorem row_reverse_missing_empty (M N : Nat) (hNM : N≤M) :
    (latticeRowPoints N 0).filter (fun u => !decide (u ∈ latticeRowPoints M 0))=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro u hu
  have hb := (mem_latticeRowPoints u N 0).mp hu
  have hm : u ∈ latticeRowPoints M 0 :=
    (mem_latticeRowPoints u M 0).mpr ⟨hb.1,hb.2.1,by omega,by omega⟩
  simp [hm]

theorem upperHorizontalWeightFour_finite_difference (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M N : Nat) (hN : 0<N) (hNM : N≤M) :
    Small (sub (upperLatticeFiniteRow z hz 4 M 0).val (upperLatticeFiniteRow z hz 4 N 0).val)
      (upperWeightFourTailConstant z hz*reciprocalSquare N) := by
  have he := representedSum_difference (upperPointPower z hz 4) (upperPointPower_valid z hz 4)
    (latticeRowPoints M 0) (latticeRowPoints N 0)
    (latticeRowPoints_nodup M 0) (latticeRowPoints_nodup N 0)
  have hA := upperFiniteSubsetWeightFour_small z hz N M hN
    ((latticeRowPoints M 0).filter (fun u => !decide (u ∈ latticeRowPoints N 0)))
    (List.Pairwise.filter _ (latticeRowPoints_nodup M 0)) (row_missing_bounds M N)
  have hB : Small (LocalODE.sum (((latticeRowPoints N 0).filter
      (fun u => !decide (u ∈ latticeRowPoints M 0))).map (upperPointPower z hz 4))) 0 := by
    rw [row_reverse_missing_empty M N hNM]
    exact Small.zero (by decide +kernel)
  have hb := SeriesLimitLaws.small_sub hA hB
  rw [Rat.add_zero] at hb
  exact Small.congr (sub_valid (rowPointSum_valid z hz 4 _) (rowPointSum_valid z hz 4 _))
    (sub_valid (upperLatticeFiniteRow z hz 4 M 0).property (upperLatticeFiniteRow z hz 4 N 0).property)
    (equiv_symm he) hb

theorem upperHorizontalWeightSix_finite_difference (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M N : Nat) (hN : 0<N) (hNM : N≤M) :
    Small (sub (upperLatticeFiniteRow z hz 6 M 0).val (upperLatticeFiniteRow z hz 6 N 0).val)
      (upperWeightSixTailConstant z hz*reciprocalSquare N) := by
  have he := representedSum_difference (upperPointPower z hz 6) (upperPointPower_valid z hz 6)
    (latticeRowPoints M 0) (latticeRowPoints N 0)
    (latticeRowPoints_nodup M 0) (latticeRowPoints_nodup N 0)
  have hA := upperFiniteSubsetWeightSix_small z hz N M hN
    ((latticeRowPoints M 0).filter (fun u => !decide (u ∈ latticeRowPoints N 0)))
    (List.Pairwise.filter _ (latticeRowPoints_nodup M 0)) (row_missing_bounds M N)
  have hB : Small (LocalODE.sum (((latticeRowPoints N 0).filter
      (fun u => !decide (u ∈ latticeRowPoints M 0))).map (upperPointPower z hz 6))) 0 := by
    rw [row_reverse_missing_empty M N hNM]
    exact Small.zero (by decide +kernel)
  have hb := SeriesLimitLaws.small_sub hA hB
  rw [Rat.add_zero] at hb
  exact Small.congr (sub_valid (rowPointSum_valid z hz 6 _) (rowPointSum_valid z hz 6 _))
    (sub_valid (upperLatticeFiniteRow z hz 6 M 0).property (upperLatticeFiniteRow z hz 6 N 0).property)
    (equiv_symm he) hb

/-- The actual sum of the horizontal row, omitting the origin. -/
def upperHorizontalWeightFourSum (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => (upperLatticeFiniteRow z hz 4 (N+1) 0).val)
    (fun N => (upperLatticeFiniteRow z hz 4 (N+1) 0).property) (upperWeightFourTailRate z hz)

def upperHorizontalWeightSixSum (z : Scalar) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => (upperLatticeFiniteRow z hz 6 (N+1) 0).val)
    (fun N => (upperLatticeFiniteRow z hz 6 (N+1) 0).property) (upperWeightSixTailRate z hz)

theorem upperHorizontalWeightFourSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperHorizontalWeightFourSum z hz).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (upperWeightFourTailRate_shrinks z hz)
    (fun k n hkn => upperHorizontalWeightFour_finite_difference z hz (n+1) (k+1) (by omega) (by omega))

theorem upperHorizontalWeightSixSum_valid (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (upperHorizontalWeightSixSum z hz).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (upperWeightSixTailRate_shrinks z hz)
    (fun k n hkn => upperHorizontalWeightSix_finite_difference z hz (n+1) (k+1) (by omega) (by omega))

theorem upperHorizontalWeightFourSum_close_prefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperHorizontalWeightFourSum z hz) (upperLatticeFiniteRow z hz 4 (N+1) 0).val)
      (upperWeightFourTailRate z hz N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (fun k n hkn => upperHorizontalWeightFour_finite_difference z hz (n+1) (k+1) (by omega) (by omega)) N

theorem upperHorizontalWeightSixSum_close_prefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    Small (sub (upperHorizontalWeightSixSum z hz) (upperLatticeFiniteRow z hz 6 (N+1) 0).val)
      (upperWeightSixTailRate z hz N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (fun k n hkn => upperHorizontalWeightSix_finite_difference z hz (n+1) (k+1) (by omega) (by omega)) N

end ComputableAnalysis.ModularForms
