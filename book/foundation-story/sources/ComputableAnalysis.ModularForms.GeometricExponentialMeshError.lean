import ComputableAnalysis.ModularForms.GeometricExponentialPrefixBound
import ComputableAnalysis.ModularForms.GeometricEulerFactorStability
import ComputableAnalysis.ModularForms.GeometricRotationEulerConvergence
import ComputableAnalysis.ComplexInterval

/-! Iterated actual exponential-product comparison with the rational Euler mesh. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def geometricExponentialErrorScale : Rat :=
  8*exponentialQuadraticConstant geometricFactorRadius*geometricExponentialPrefixBound

theorem geometricExponentialErrorScale_nonnegative : 0 ≤ geometricExponentialErrorScale :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide)
    (exponentialQuadraticConstant_nonnegative geometricFactorRadius))
    geometricExponentialPrefixBound_nonnegative

private theorem meshStep_le_one (N : Nat) : geometricMeshStep N ≤ 1 := by
  have hc := geometricMeshStep_identity N
  have hn : (1:Rat) ≤ ((N+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos N
  have hm := Rat.mul_le_mul_of_nonneg_right hn (Rat.le_of_lt (geometricMeshStep_positive N))
  grind only

private theorem meshFactor_step (N k : Nat) :
    (mul (geometricEulerFactor ((k:Rat)*geometricMeshStep N) (geometricMeshStep N)).val
      (ofQComplex (geometricEulerMesh N k))).Equiv (ofQComplex (geometricEulerMesh N (k+1))) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  change (QBox.mul (QBox.point ⟨1,geometricMeshStep N*
    (2/(1+((k:Rat)*geometricMeshStep N)*((k:Rat)*geometricMeshStep N)))⟩)
    (QBox.point (geometricEulerMesh N k))).Overlaps
    (QBox.point (geometricEulerMesh N (k+1)))
  rw [QBox.mul_point,geometricEulerFactor_step]
  change (QBox.point (geometricEulerMesh N (k+1))).Overlaps
    (QBox.point (geometricEulerMesh N (k+1)))
  exact ⟨⟨Rat.le_refl,Rat.le_refl⟩,⟨Rat.le_refl,Rat.le_refl⟩⟩

theorem geometricExponentialProduct_mesh_error (N k : Nat) (hk : k ≤ N+1) :
    Small (sub (geometricExponentialProduct N k) (ofQComplex (geometricEulerMesh N k)))
      (geometricExponentialErrorScale*geometricEulerMeshError N k) := by
  induction k with
  | zero =>
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m <;>
      simp [geometricExponentialProduct,geometricEulerMesh,geometricEulerMeshError,
        sub,add,neg,ofQComplex,QBox.add,QBox.neg,QBox.point,QComplex.add,QComplex.neg,QComplex.one,
        realPart,imagPart,RealRaw.ofRat] <;> grind only
  | succ k ih =>
    have hkn : k ≤ N+1 := by omega
    have hE := Rat.mul_nonneg geometricExponentialErrorScale_nonnegative
      (geometricEulerMeshError_nonnegative N k)
    have hb := geometricExponentialProduct_error_step ((k:Rat)*geometricMeshStep N)
      (geometricMeshStep N) (geometricExponentialErrorScale*geometricEulerMeshError N k)
      geometricExponentialPrefixBound (geometricExponentialProduct N k)
      (ofQComplex (geometricEulerMesh N k)) (geometricExponentialProduct_valid N k)
      (ofQComplex_valid _) (Rat.le_of_lt (geometricMeshStep_positive N)) (meshStep_le_one N)
      hE geometricExponentialPrefixBound_nonnegative (ih hkn)
      (geometricExponentialProduct_small N k hkn)
    have he := FunctionTheory.sub_congr
      (equiv_refl _ (geometricExponentialProduct_valid N (k+1))) (meshFactor_step N k)
    have hv := Small.congr
      (sub_valid (geometricExponentialProduct_valid N (k+1))
        (mul_valid (geometricEulerFactor _ _).property (ofQComplex_valid _)))
      (sub_valid (geometricExponentialProduct_valid N (k+1)) (ofQComplex_valid _)) he hb
    apply hv.mono
    have hh := Rat.le_of_lt (geometricMeshStep_positive N)
    have hs := Rat.mul_nonneg (Rat.mul_nonneg geometricExponentialErrorScale_nonnegative hh) hh
    simp only [geometricEulerMeshError]
    unfold geometricExponentialErrorScale at *
    grind only

def geometricExponentialEndpointRate (N : Nat) : Rat :=
  geometricExponentialErrorScale*geometricEulerEndpointRate N

theorem geometricExponentialEndpointRate_shrinks : ShrinksToZero geometricExponentialEndpointRate :=
  SeriesLimitLaws.shrinks_scale _ geometricEulerEndpointRate_shrinks
    geometricExponentialErrorScale geometricExponentialErrorScale_nonnegative

theorem geometricExponentialProduct_endpoint_error (N : Nat) :
    Small (sub (geometricExponentialProduct (geometricConvergenceMesh N) (geometricConvergenceMesh N+1))
      (ofQComplex (geometricEulerMesh (geometricConvergenceMesh N) (geometricConvergenceMesh N+1))))
      (geometricExponentialEndpointRate N) := by
  have hb := geometricExponentialProduct_mesh_error (geometricConvergenceMesh N)
    (geometricConvergenceMesh N+1) (Nat.le_refl _)
  apply hb.mono
  have ha := geometricEulerMesh_amplification_bound N
  have hh := Rat.le_of_lt (geometricMeshStep_positive (geometricConvergenceMesh N))
  have hm := Rat.mul_le_mul_of_nonneg_left
    (show (1+2*geometricMeshStep (geometricConvergenceMesh N))^(geometricConvergenceMesh N+1)-1 ≤ 15 by
      grind only) (Rat.mul_nonneg (show (0:Rat)≤6 by decide) hh)
  have hr : geometricEulerMeshError (geometricConvergenceMesh N) (geometricConvergenceMesh N+1) ≤
      geometricEulerEndpointRate N := by
    rw [geometricEulerMeshError_closed]
    unfold geometricEulerEndpointRate
    grind only
  exact Rat.mul_le_mul_of_nonneg_left hr geometricExponentialErrorScale_nonnegative

end ComputableAnalysis.ModularForms
