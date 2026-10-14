import ComputableAnalysis.ModularForms.PairedDivisionQuarticExpansion

/-! Actual reciprocal-square expansion for the cubic division derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem reciprocalSquare_nonneg (n : Nat) : 0≤reciprocalSquare (n+1) := by
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  unfold reciprocalSquare
  exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hn hn))

private theorem centerReciprocal_precise_small (n : Nat) :
    Small (pairedCenterReciprocal n).val (reciprocalSquare (n+1)) := by
  have h := reciprocalSquare_nonneg n
  refine ⟨?_,?_,?_,?_⟩
  · intro a b
    change -reciprocalSquare (n+1)≤reciprocalSquare (n+1)
    grind only
  · intro a b
    exact Rat.le_refl
  · intro a b
    change -reciprocalSquare (n+1)≤0
    grind only
  · intro a b
    exact h

private def difference (x y : Scalar) : Scalar := ⟨sub x.val y.val,sub_valid x.property y.property⟩

def pairedInverseSquareQuadraticResidual (z : Scalar) (hz : LocalODE.interior (1/4) z) (n : Nat) : Scalar :=
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let c := pairedCenterReciprocal n
  let c2 := scalarProduct c c
  let c3 := scalarProduct c c2
  difference (difference (scalarProduct i i) c2)
    ⟨scaleRat 2 (scalarProduct c3 (scalarProduct z z)).val,scaleRat_valid (scalarProduct c3 (scalarProduct z z)).property⟩

private theorem square_algebra (I C Z : ScalarAlgebra.Value) :
    (I*I-C*C)-ComplexRawQuotient.scaleRat 2 ((C*(C*C))*(Z*Z))=
      ((I+C)+(C*C)*(Z*Z))*((I-C)-(C*C)*(Z*Z))+
        (C*(C*(C*C)))*((Z*Z)*(Z*Z)) := by
  have h := ScalarAlgebra.scale_natural 2 ((C*(C*C))*(Z*Z))
  change ComplexRawQuotient.scaleRat 2 ((C*(C*C))*(Z*Z))=(2:ScalarAlgebra.Value)*((C*(C*C))*(Z*Z)) at h
  rw [h]
  grind only

/-- The actual reciprocal-square residual has a summable quartic bound. -/
theorem pairedInverseSquare_quadratic_remainder_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (pairedInverseSquareQuadraticResidual z hz n).val
      (2944*R*R*R*R*reciprocalSquare (n+1)) := by
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let c := pairedCenterReciprocal n
  let c2 := scalarProduct c c
  let c3 := scalarProduct c c2
  let c4 := scalarProduct c c3
  let z2 := scalarProduct z z
  let z4 := scalarProduct z2 z2
  let e := scalarSum (scalarSum i c) (scalarProduct c2 z2)
  let j := difference (difference i c) (scalarProduct c2 z2)
  let rem := scalarSum (scalarProduct e j) (scalarProduct c4 z4)
  have hc2 : Small c2.val 2 := by
    have h := Small.mul c.property c.property (show (0:Rat)≤1 by decide +kernel)
      (show (0:Rat)≤1 by decide +kernel) (pairedCenterReciprocal_small n) (pairedCenterReciprocal_small n)
    rw [show (2:Rat)*1*1=2 by decide +kernel] at h
    exact h
  have hc3 : Small c3.val 4 := by
    have h := Small.mul c.property c2.property (show (0:Rat)≤1 by decide +kernel)
      (show (0:Rat)≤2 by decide +kernel) (pairedCenterReciprocal_small n) hc2
    rw [show (2:Rat)*1*2=4 by decide +kernel] at h
    exact h
  have hc4 : Small c4.val (8*reciprocalSquare (n+1)) := by
    have h := Small.mul c.property c3.property (reciprocalSquare_nonneg n)
      (show (0:Rat)≤4 by decide +kernel) (centerReciprocal_precise_small n) hc3
    have he : 2*reciprocalSquare (n+1)*4=8*reciprocalSquare (n+1) := by grind only
    rw [he] at h
    exact h
  have hi : Small i.val 4 := by
    apply (pairedSmallDiskLiteralInverse_bound z (LocalODE.interior_bound _ z hz) n).mono
    have h := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
    rw [show reciprocalSquare 1=1 by decide +kernel] at h
    grind only
  have hz2fixed := Small.mul z.property z.property (show (0:Rat)≤1/4 by decide +kernel)
    (show (0:Rat)≤1/4 by decide +kernel) (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ z hz)
  have hjterm := Small.mul c2.property z2.property (show (0:Rat)≤2 by decide +kernel)
    (show (0:Rat)≤2*(1/4)*(1/4) by decide +kernel) hc2 hz2fixed
  have hj := SeriesLimitLaws.small_sub (SeriesLimitLaws.small_sub hi (pairedCenterReciprocal_small n)) hjterm
  have hj' : Small j.val (11/2) := by
    have he : (4:Rat)+1+2*2*(2*(1/4)*(1/4))=11/2 := by decide +kernel
    rw [he] at hj
    exact hj
  have he : Small e.val (256*R*R*R*R*reciprocalSquare (n+1)) :=
    pairedSmallDiskLiteralInverse_center_remainder_bound z hz n R hR hs
  have hR2 : 0≤2*R*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR
  have hR4 : 0≤2*(2*R*R)*(2*R*R) := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR2) hR2
  have hz2 : Small z2.val (2*R*R) := Small.mul z.property z.property hR hR hs hs
  have hz4 : Small z4.val (2*(2*R*R)*(2*R*R)) := Small.mul z2.property z2.property hR2 hR2 hz2 hz2
  have hR4c : 0≤256*R*R*R*R*reciprocalSquare (n+1) := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR) hR) hR)
    (reciprocalSquare_nonneg n)
  have hprod := Small.mul e.property j.property hR4c (show (0:Rat)≤11/2 by decide +kernel) he hj'
  have hlast := Small.mul c4.property z4.property
    (Rat.mul_nonneg (by decide +kernel) (reciprocalSquare_nonneg n)) hR4 hc4 hz4
  have hb := LocalODE.small_add hprod hlast
  have hrate : 2*(256*R*R*R*R*reciprocalSquare (n+1))*(11/2)+
      2*(8*reciprocalSquare (n+1))*(2*(2*R*R)*(2*R*R))=
      2944*R*R*R*R*reciprocalSquare (n+1) := by grind only
  rw [hrate] at hb
  have heq : rem.val.Equiv (pairedInverseSquareQuadraticResidual z hz n).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := rem.property)
      (hright := (pairedInverseSquareQuadraticResidual z hz n).property)
    let I := ComplexRawQuotient.ofRaw i.val i.property
    let C := ComplexRawQuotient.ofRaw c.val c.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change ((I+C)+(C*C)*(Z*Z))*((I-C)-(C*C)*(Z*Z))+
        (C*(C*(C*C)))*((Z*Z)*(Z*Z))=
      (I*I-C*C)-ComplexRawQuotient.scaleRat 2 ((C*(C*C))*(Z*Z))
    exact (square_algebra I C Z).symm
  exact Small.congr rem.property (pairedInverseSquareQuadraticResidual z hz n).property heq hb

end ComputableAnalysis.ModularForms
