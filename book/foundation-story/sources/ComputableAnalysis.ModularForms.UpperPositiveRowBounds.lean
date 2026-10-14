import ComputableAnalysis.ModularForms.UpperPositiveRowsLimits
import ComputableAnalysis.ModularForms.UpperFilteredPointBounds

/-! Uniform inverse-square bounds for actual positive lattice rows beyond the first. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory QuadraticOrder163

private theorem row_annulus_bounds (M n : Nat) (u : QuadraticOrder163)
    (hu : u ∈ latticeRowPoints M ((n+2:Nat):Int)) :
    u≠QuadraticOrder163.zero ∧ n+1<shellRadius u ∧ shellRadius u≤(n+1)+max M (n+2) := by
  have hb := (mem_latticeRowPoints u M ((n+2:Nat):Int)).mp hu
  have hr := shellRadius_bounds u
  have hmax : shellRadius u≤max M (n+2) := by
    apply (shellRadius_le_iff u (max M (n+2))).mpr
    have hm := Nat.le_max_left M (n+2)
    have hn := Nat.le_max_right M (n+2)
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  exact ⟨hb.1,by omega,by omega⟩

/-- Every finite truncation of a row above height one has a uniform lattice tail bound. -/
theorem upperLatticeFiniteRow_weightFour_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M n : Nat) :
    Small (upperLatticeFiniteRow z hz 4 M ((n+2:Nat):Int)).val
      (upperWeightFourTailConstant z hz*reciprocalSquare (n+1)) :=
  upperFiniteSubsetWeightFour_small z hz (n+1) (max M (n+2)) (by omega)
    (latticeRowPoints M ((n+2:Nat):Int)) (latticeRowPoints_nodup M _)
    (row_annulus_bounds M n)

theorem upperLatticeFiniteRow_weightSix_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M n : Nat) :
    Small (upperLatticeFiniteRow z hz 6 M ((n+2:Nat):Int)).val
      (upperWeightSixTailConstant z hz*reciprocalSquare (n+1)) :=
  upperFiniteSubsetWeightSix_small z hz (n+1) (max M (n+2)) (by omega)
    (latticeRowPoints M ((n+2:Nat):Int)) (latticeRowPoints_nodup M _)
    (row_annulus_bounds M n)

/-- The uniform finite-row bound survives the justified horizontal limit. -/
theorem upperPositiveLatticeRowSum_weightFour_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (n : Nat) :
    Small (upperPositiveLatticeRowSum z hz 4 (by omega) (n+1)).val
      (upperWeightFourTailConstant z hz*reciprocalSquare (n+1)) := by
  let B := pairedDerivativeCutoff (integerScaleScalar z ((n+1+1:Nat):Int))
  let p := fun P => (upperLatticeFiniteRow z hz 4 (4*B+(P+1)) ((n+2:Nat):Int)).val
  have hp P : (p P).Valid := (upperLatticeFiniteRow z hz 4 _ _).property
  apply SeriesLimitLaws.small_of_prefix_bound _
    (upperPositiveLatticeRowSum z hz 4 (by omega) (n+1)).property p hp _
    (fun P => (((2*32^4:Nat):Rat)*(((P+1:Nat):Rat))⁻¹))
    (pairedReciprocalTail_shrinks (2*32^4))
  · intro P
    have h := upperLatticeFiniteRow_positive_canonical_close z hz 4 B (by omega) (n+1)
      (pairedDerivativeCutoff_small _) P
    have hi : n+1+1=n+2 := by omega
    simpa only [hi] using h
  · intro P
    exact upperLatticeFiniteRow_weightFour_bound z hz _ n

theorem upperPositiveLatticeRowSum_weightSix_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (n : Nat) :
    Small (upperPositiveLatticeRowSum z hz 6 (by omega) (n+1)).val
      (upperWeightSixTailConstant z hz*reciprocalSquare (n+1)) := by
  let B := pairedDerivativeCutoff (integerScaleScalar z ((n+1+1:Nat):Int))
  let p := fun P => (upperLatticeFiniteRow z hz 6 (4*B+(P+1)) ((n+2:Nat):Int)).val
  have hp P : (p P).Valid := (upperLatticeFiniteRow z hz 6 _ _).property
  apply SeriesLimitLaws.small_of_prefix_bound _
    (upperPositiveLatticeRowSum z hz 6 (by omega) (n+1)).property p hp _
    (fun P => (((2*32^6:Nat):Rat)*(((P+1:Nat):Rat))⁻¹))
    (pairedReciprocalTail_shrinks (2*32^6))
  · intro P
    have h := upperLatticeFiniteRow_positive_canonical_close z hz 6 B (by omega) (n+1)
      (pairedDerivativeCutoff_small _) P
    have hi : n+1+1=n+2 := by omega
    simpa only [hi] using h
  · intro P
    exact upperLatticeFiniteRow_weightSix_bound z hz _ n

end ComputableAnalysis.ModularForms
