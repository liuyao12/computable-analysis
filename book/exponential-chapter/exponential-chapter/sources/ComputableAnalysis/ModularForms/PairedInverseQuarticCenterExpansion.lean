import ComputableAnalysis.ModularForms.PairedDivisionQuadraticPiNormalization

/-! Exact quartic center expansion of actual paired reciprocals. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem quartic_algebra (Z T C I : ScalarAlgebra.Value)
    (hi : (Z*Z-T)*I=1) (hc : T*C=1) :
    ((I+C)+(C*C)*(Z*Z))+(C*(C*C))*((Z*Z)*(Z*Z))=
      ((C*(C*C))*(((Z*Z)*(Z*Z))*(Z*Z)))*I := by
  have h1 : I+C=C*(Z*Z)*I := by grind only
  have h2 : (I+C)+(C*C)*(Z*Z)=(C*C)*((Z*Z)*(Z*Z))*I := by
    have h := congrArg (fun x => C*(Z*Z)*x) h1
    grind only
  have h3 := congrArg (fun x => (C*C)*((Z*Z)*(Z*Z))*x) h1
  grind only

def pairedInverseQuarticCenterResidual (z : Scalar) (hz : LocalODE.interior (1/4) z) (n : Nat) : Scalar :=
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let c := pairedCenterReciprocal n
  let z2 := scalarProduct z z
  let z4 := scalarProduct z2 z2
  let c2 := scalarProduct c c
  let c3 := scalarProduct c c2
  scalarSum (scalarSum (scalarSum i c) (scalarProduct c2 z2)) (scalarProduct c3 z4)

def pairedInverseSexticCenterRemainder (z : Scalar) (hz : LocalODE.interior (1/4) z) (n : Nat) : Scalar :=
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let c := pairedCenterReciprocal n
  let z2 := scalarProduct z z
  let z4 := scalarProduct z2 z2
  let z6 := scalarProduct z4 z2
  let c3 := scalarProduct c (scalarProduct c c)
  scalarProduct (scalarProduct c3 z6) i

/-- The actual reciprocal has an exact quartic center polynomial with a sextic remainder. -/
theorem pairedSmallDiskLiteralInverse_quartic_center_expansion (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) :
    (pairedInverseQuarticCenterResidual z hz n).val.Equiv
      (pairedInverseSexticCenterRemainder z hz n).val := by
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let t := pairedIntegerSquare (n+1)
  let c := pairedCenterReciprocal n
  have hi := RepresentedReciprocal.mul_inverse (pairedLiteralDenominator z t)
    ((pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ z hz)) n)
  have hc := rationalRealProduct_equiv t (reciprocalSquare (n+1))
  have he : t*reciprocalSquare (n+1)=1 := by
    dsimp [t]
    unfold pairedIntegerSquare reciprocalSquare
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (pairedIntegerSquare_pos (n+1) (by omega)))
  rw [he] at hc
  have hI := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (pairedLiteralDenominator z t).property i.property) (hright := ofQComplex_valid _) hi
  have hC := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (ofQComplex_valid _) c.property) (hright := ofQComplex_valid _) hc
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedInverseQuarticCenterResidual z hz n).property)
    (hright := (pairedInverseSexticCenterRemainder z hz n).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let T := ComplexRawQuotient.ofQComplex ⟨t,0⟩
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let I := ComplexRawQuotient.ofRaw i.val i.property
  change (Z*Z-T)*I=1 at hI
  change T*C=1 at hC
  change ((I+C)+(C*C)*(Z*Z))+(C*(C*C))*((Z*Z)*(Z*Z))=
    ((C*(C*C))*(((Z*Z)*(Z*Z))*(Z*Z)))*I
  exact quartic_algebra Z T C I hI hC

/-- A summable inverse-square majorant for the sextic remainder. -/
theorem pairedSmallDiskLiteralInverse_quartic_center_remainder_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (pairedInverseQuarticCenterResidual z hz n).val
      (2048*R*R*R*R*R*R*reciprocalSquare (n+1)) := by
  let c := pairedCenterReciprocal n
  let c2 := scalarProduct c c
  let c3 := scalarProduct c c2
  let z2 := scalarProduct z z
  let z4 := scalarProduct z2 z2
  let z6 := scalarProduct z4 z2
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  have htwo : (0:Rat)≤2 := by decide +kernel
  have hfour : (0:Rat)≤4 := by decide +kernel
  have hone : (0:Rat)≤1 := by decide +kernel
  have hc2 : Small c2.val (2*1*1) := Small.mul c.property c.property hone hone
    (pairedCenterReciprocal_small n) (pairedCenterReciprocal_small n)
  have hc3 : Small c3.val (2*1*(2*1*1)) := Small.mul c.property c2.property hone
    (by decide +kernel) (pairedCenterReciprocal_small n) hc2
  have hz2 : Small z2.val (2*R*R) := Small.mul z.property z.property hR hR hs hs
  have hR2 : 0≤2*R*R := Rat.mul_nonneg (Rat.mul_nonneg htwo hR) hR
  have hz4 : Small z4.val (2*(2*R*R)*(2*R*R)) :=
    Small.mul z2.property z2.property hR2 hR2 hz2 hz2
  have hR4 : 0≤2*(2*R*R)*(2*R*R) := Rat.mul_nonneg (Rat.mul_nonneg htwo hR2) hR2
  have hz6 : Small z6.val (2*(2*(2*R*R)*(2*R*R))*(2*R*R)) :=
    Small.mul z4.property z2.property hR4 hR2 hz4 hz2
  have hR6 : 0≤2*(2*(2*R*R)*(2*R*R))*(2*R*R) :=
    Rat.mul_nonneg (Rat.mul_nonneg htwo hR4) hR2
  have hcz := Small.mul c3.property z6.property (show (0:Rat)≤2*1*(2*1*1) by decide +kernel)
    hR6 hc3 hz6
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have h0 : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hn hn))
  have hb := Small.mul (scalarProduct c3 z6).property i.property
    (Rat.mul_nonneg (Rat.mul_nonneg htwo (show (0:Rat)≤2*1*(2*1*1) by decide +kernel)) hR6)
    (Rat.mul_nonneg hfour h0) hcz
    (pairedSmallDiskLiteralInverse_bound z (LocalODE.interior_bound _ z hz) n)
  have he : 2*(2*(2*1*(2*1*1))*(2*(2*(2*R*R)*(2*R*R))*(2*R*R)))*(4*reciprocalSquare (n+1))=
      2048*R*R*R*R*R*R*reciprocalSquare (n+1) := by grind only
  rw [he] at hb
  exact Small.congr (pairedInverseSexticCenterRemainder z hz n).property
    (pairedInverseQuarticCenterResidual z hz n).property
    (equiv_symm (pairedSmallDiskLiteralInverse_quartic_center_expansion z hz n)) hb

end ComputableAnalysis.ModularForms
