import ComputableAnalysis.ModularForms.UpperPointRegionalRemainder
import ComputableAnalysis.ModularForms.CMWeightFourTailRate163

/-! Summed regional bounds for the actual finite shell-map remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions QuadraticOrder163

private theorem pointRemainderSum_small (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (us : List QuadraticOrder163)
    (B : Rat) (hB : 0≤B) (hb : ∀ u ∈ us, Small (upperPointRemainder a ha z hz k u) B) :
    Small (LocalODE.sum (us.map (upperPointRemainder a ha z hz k))) ((us.length:Rat)*B) := by
  induction us with
  | nil =>
    change Small ComplexRaw.zero ((0:Rat)*B)
    rw [Rat.zero_mul]
    exact Small.zero (by decide)
  | cons u us ih =>
    have hhead := hb u (by simp)
    have htail := ih (fun v hv => hb v (by simp [hv]))
    have hs := LocalODE.small_add hhead htail
    have he : B+(us.length:Rat)*B=((u::us).length:Rat)*B := by
      simp only [List.length_cons,Rat.natCast_add]
      grind
    rw [he] at hs
    exact hs

theorem upperFiniteShell_remainder_region_bound
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H)
    (r : Nat) (hr : 0<r) (k : Nat) :
    Small (DomainFunctions.remainder (upperFiniteMap k (shellPoints r)) a ha
      ((upperFiniteMap_holomorphic k (shellPoints r)).derivative a ha) z hz)
      (((8*r:Nat):Rat)*(powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) k*
        ((r:Rat)⁻¹)^k*H*H)) := by
  have hp : (0:Rat)<(r:Rat) := by exact_mod_cast hr
  have hC := latticeRegionReciprocalConstant_nonnegative R U eta hR hU heta
  have hB : 0≤powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) k*((r:Rat)⁻¹)^k*H*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (powerRemainderCoefficient_nonnegative _ hC k)
      (Rat.pow_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hp)))) hH) hH
  have hs := pointRemainderSum_small a ha z hz k (shellPoints r) _ hB (by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    have h := upperPointRemainder_region_bound a z ha hz R U eta A Z hR hU heta
      hregionA hheightA hregionZ hheightZ H hH hza (shellPoint r i) (shellPoint_nonzero r hr i) k
    rw [shellRadius_shellPoint] at h
    exact h)
  have hlen : (shellPoints r).length=8*r := by simp [shellPoints]
  rw [hlen] at hs
  have hv : (LocalODE.sum ((shellPoints r).map (upperPointRemainder a ha z hz k))).Valid := by
    apply LocalODE.sum_valid
    intro t ht
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
    exact upperPointRemainder_valid a ha z hz k u
  exact Small.congr hv (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (upperFiniteMap_remainder_sum a ha z hz k (shellPoints r))) hs

theorem upperFiniteShell_weightFour_remainder_small
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H)
    (r : Nat) (hr : 0<r) :
    Small (DomainFunctions.remainder (upperFiniteMap 4 (shellPoints r)) a ha
      ((upperFiniteMap_holomorphic 4 (shellPoints r)).derivative a ha) z hz)
      (8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 4*reciprocalCube r*H*H) := by
  have h := upperFiniteShell_remainder_region_bound a z ha hz R U eta A Z hR hU heta
    hregionA hheightA hregionZ hheightZ H hH hza r hr 4
  have hp : (0:Rat)<(r:Rat) := by exact_mod_cast hr
  have hc := Rat.mul_inv_cancel (r:Rat) (Rat.ne_of_gt hp)
  have hc3 := Rat.mul_inv_cancel ((r:Rat)*(r:Rat)*(r:Rat))
    (Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hp))
  have he : (((8*r:Nat):Rat)*(powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 4*
      ((r:Rat)⁻¹)^4*H*H))=
      8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 4*reciprocalCube r*H*H := by
    unfold reciprocalCube
    rw [Rat.natCast_mul]
    simp only [Rat.pow_succ,Rat.pow_zero]
    grind only
  rw [he] at h
  exact h

theorem upperFiniteShell_weightSix_remainder_small
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H)
    (r : Nat) (hr : 0<r) :
    Small (DomainFunctions.remainder (upperFiniteMap 6 (shellPoints r)) a ha
      ((upperFiniteMap_holomorphic 6 (shellPoints r)).derivative a ha) z hz)
      (8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 6*reciprocalCube r*H*H) := by
  have h := upperFiniteShell_remainder_region_bound a z ha hz R U eta A Z hR hU heta
    hregionA hheightA hregionZ hheightZ H hH hza r hr 6
  apply h.mono
  let v : Rat := r
  have hp : 0<v := by dsimp [v]; exact_mod_cast hr
  have h1 : (1:Rat)≤v := by dsimp [v]; exact_mod_cast hr
  have hc := Rat.mul_inv_cancel v (Rat.ne_of_gt hp)
  have hc3 := Rat.mul_inv_cancel (v*v*v) (Rat.ne_of_gt (Rat.mul_pos (Rat.mul_pos hp hp) hp))
  have h2 : 1≤v*v := by
    have hm := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt hp)
    grind
  have h3 : v≤v*v*v := by
    have hm := Rat.mul_le_mul_of_nonneg_left h2 (Rat.le_of_lt hp)
    grind
  have hC := powerRemainderCoefficient_nonnegative (latticeRegionReciprocalConstant R U eta)
    (latticeRegionReciprocalConstant_nonnegative R U eta hR hU heta) 6
  have hK : 0≤8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 6*H*H :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) hH) hH
  unfold reciprocalCube
  rw [Rat.natCast_mul]
  apply Rat.le_of_mul_le_mul_right (c := v*v*v*v*v*v)
  · calc
      _ = (8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 6*H*H)*v := by
        simp only [Rat.pow_succ,Rat.pow_zero]
        grind only
      _ ≤ (8*powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) 6*H*H)*(v*v*v) :=
        Rat.mul_le_mul_of_nonneg_left h3 hK
      _ = _ := by grind only
  · exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos hp hp) hp) hp) hp) hp

end ComputableAnalysis.ModularForms
