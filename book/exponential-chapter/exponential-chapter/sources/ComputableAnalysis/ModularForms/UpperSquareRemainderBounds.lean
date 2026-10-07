import ComputableAnalysis.ModularForms.UpperRemainderShellBounds
import ComputableAnalysis.ModularForms.ReciprocalCubePrefixBound
import ComputableAnalysis.ModularForms.RepresentedSumAppend
import ComputableAnalysis.ModularForms.UpperDerivativeCenterIndependence

/-! Uniform quadratic bounds for the actual finite square-map remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions QuadraticOrder163

private theorem remList_valid (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (us : List QuadraticOrder163) :
    ∀ t ∈ us.map (upperPointRemainder a ha z hz k), t.Valid := by
  intro t ht
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
  exact upperPointRemainder_valid a ha z hz k u

private theorem squareRemainderSum_bound (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (B : Rat) (hB : 0≤B)
    (hs : ∀ r, 0<r → Small (LocalODE.sum ((shellPoints r).map (upperPointRemainder a ha z hz k)))
      (B*reciprocalCube r)) (N : Nat) :
    Small (LocalODE.sum ((squarePoints N).map (upperPointRemainder a ha z hz k)))
      (B*reciprocalCubePrefix N) := by
  induction N with
  | zero =>
    change Small ComplexRaw.zero (B*0)
    rw [Rat.mul_zero]
    exact Small.zero (by decide)
  | succ N ih =>
    have hb := LocalODE.small_add ih (hs (N+1) (by omega))
    have he : B*reciprocalCubePrefix N+B*reciprocalCube (N+1)=B*reciprocalCubePrefix (N+1) := by
      rw [reciprocalCubePrefix]
      grind
    rw [he] at hb
    rw [squarePoints_succ,List.map_append]
    exact Small.congr
      (add_valid (LocalODE.sum_valid _ (remList_valid a ha z hz k _))
        (LocalODE.sum_valid _ (remList_valid a ha z hz k _)))
      (LocalODE.sum_valid _ (by
        intro t ht
        rcases List.mem_append.mp ht with h|h
        · exact remList_valid a ha z hz k _ t h
        · exact remList_valid a ha z hz k _ t h))
      (equiv_symm (representedSum_append _ _ (remList_valid a ha z hz k _) (remList_valid a ha z hz k _))) hb

theorem upperFiniteSquare_weightFour_remainder_region_bound
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (upperFiniteMap 4 (squarePoints N)) a ha
      ((upperFiniteMap_holomorphic 4 (squarePoints N)).derivative a ha) z hz)
      (16*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 4*H*H) := by
  let B := 8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 4*H*H
  have hC := powerRemainderCoefficient_nonnegative _
    (latticeRegionReciprocalConstant_nonnegative R U eta hR hU heta) 4
  have hB : 0≤B := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hH) hH
  have hb := squareRemainderSum_bound a ha z hz 4 B hB (by
    intro r hr
    have h := upperFiniteShell_weightFour_remainder_small a z ha hz R U eta A Z hR hU heta
      hregionA hheightA hregionZ hheightZ H hH hza r hr
    have he : 8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 4*reciprocalCube r*H*H=
        B*reciprocalCube r := by dsimp [B]; grind
    rw [he] at h
    exact Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
      (LocalODE.sum_valid _ (remList_valid a ha z hz 4 _))
      (upperFiniteMap_remainder_sum a ha z hz 4 (shellPoints r)) h) N
  have hm := Rat.mul_le_mul_of_nonneg_left (reciprocalCubePrefix_le_two N) hB
  have he : B*2=16*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 4*H*H := by
    dsimp [B]; grind
  rw [he] at hm
  exact Small.congr (LocalODE.sum_valid _ (remList_valid a ha z hz 4 _))
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (upperFiniteMap_remainder_sum a ha z hz 4 (squarePoints N))) (hb.mono hm)

theorem upperFiniteSquare_weightSix_remainder_region_bound
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (upperFiniteMap 6 (squarePoints N)) a ha
      ((upperFiniteMap_holomorphic 6 (squarePoints N)).derivative a ha) z hz)
      (16*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 6*H*H) := by
  let B := 8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 6*H*H
  have hC := powerRemainderCoefficient_nonnegative _
    (latticeRegionReciprocalConstant_nonnegative R U eta hR hU heta) 6
  have hB : 0≤B := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hH) hH
  have hb := squareRemainderSum_bound a ha z hz 6 B hB (by
    intro r hr
    have h := upperFiniteShell_weightSix_remainder_small a z ha hz R U eta A Z hR hU heta
      hregionA hheightA hregionZ hheightZ H hH hza r hr
    have he : 8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 6*reciprocalCube r*H*H=
        B*reciprocalCube r := by dsimp [B]; grind
    rw [he] at h
    exact Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
      (LocalODE.sum_valid _ (remList_valid a ha z hz 6 _))
      (upperFiniteMap_remainder_sum a ha z hz 6 (shellPoints r)) h) N
  have hm := Rat.mul_le_mul_of_nonneg_left (reciprocalCubePrefix_le_two N) hB
  have he : B*2=16*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 6*H*H := by
    dsimp [B]; grind
  rw [he] at hm
  exact Small.congr (LocalODE.sum_valid _ (remList_valid a ha z hz 6 _))
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (upperFiniteMap_remainder_sum a ha z hz 6 (squarePoints N))) (hb.mono hm)

def localWeightFourRemainderConstant (a : Scalar) (ha : InUpperHalfPlane a.val) : Rat :=
  16*powerRemainderCoefficient (latticeRegionReciprocalConstant
    (neighborhoodRegionWidth a ha) (neighborhoodRegionWidth a ha) (neighborhoodRegionMargin a ha)) 4

theorem localWeightFourRemainderConstant_nonnegative (a : Scalar) (ha : InUpperHalfPlane a.val) :
    0≤localWeightFourRemainderConstant a ha :=
  Rat.mul_nonneg (by decide) (powerRemainderCoefficient_nonnegative _
    (latticeRegionReciprocalConstant_nonnegative _ _ _ (neighborhoodRegionWidth_nonnegative a ha)
      (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionMargin_positive a ha)) 4)

theorem upperFiniteSquare_weightFour_remainder_local_bound
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (upperFiniteMap 4 (squarePoints N)) a ha
      ((upperFiniteMap_holomorphic 4 (squarePoints N)).derivative a ha) z hz)
      (localWeightFourRemainderConstant a ha*H*H) := by
  obtain ⟨A,hA,hAH⟩ := upperCommonRegion a ha a (upperSelf_near a ha)
  obtain ⟨Z,hZ,hZH⟩ := upperCommonRegion a ha z hs
  exact upperFiniteSquare_weightFour_remainder_region_bound a z ha hz _ _ _ A Z
    (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
    (neighborhoodRegionMargin_positive a ha) hA hAH hZ hZH H hH hza N

def localWeightSixRemainderConstant (a : Scalar) (ha : InUpperHalfPlane a.val) : Rat :=
  16*powerRemainderCoefficient (latticeRegionReciprocalConstant
    (neighborhoodRegionWidth a ha) (neighborhoodRegionWidth a ha) (neighborhoodRegionMargin a ha)) 6

theorem localWeightSixRemainderConstant_nonnegative (a : Scalar) (ha : InUpperHalfPlane a.val) :
    0≤localWeightSixRemainderConstant a ha :=
  Rat.mul_nonneg (by decide) (powerRemainderCoefficient_nonnegative _
    (latticeRegionReciprocalConstant_nonnegative _ _ _ (neighborhoodRegionWidth_nonnegative a ha)
      (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionMargin_positive a ha)) 6)

theorem upperFiniteSquare_weightSix_remainder_local_bound
    (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (upperFiniteMap 6 (squarePoints N)) a ha
      ((upperFiniteMap_holomorphic 6 (squarePoints N)).derivative a ha) z hz)
      (localWeightSixRemainderConstant a ha*H*H) := by
  obtain ⟨A,hA,hAH⟩ := upperCommonRegion a ha a (upperSelf_near a ha)
  obtain ⟨Z,hZ,hZH⟩ := upperCommonRegion a ha z hs
  exact upperFiniteSquare_weightSix_remainder_region_bound a z ha hz _ _ _ A Z
    (neighborhoodRegionWidth_nonnegative a ha) (neighborhoodRegionWidth_nonnegative a ha)
    (neighborhoodRegionMargin_positive a ha) hA hAH hZ hZH H hH hza N

end ComputableAnalysis.ModularForms
