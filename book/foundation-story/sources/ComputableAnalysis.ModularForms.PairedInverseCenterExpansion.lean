import ComputableAnalysis.ModularForms.PairedDivisionSecondDerivativeCenter

/-! Exact quadratic center expansion of actual paired reciprocals, with a fourth-order remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem expansion_algebra (Z T C I : ScalarAlgebra.Value)
    (hi : (Z*Z-T)*I=1) (hc : T*C=1) :
    I+C+(C*C)*(Z*Z)=(C*C)*((Z*Z)*(Z*Z))*I := by
  have hfirst : I+C=C*(Z*Z)*I := by grind only
  have hsecond : C*(Z*Z)*(I+C)=(C*C)*((Z*Z)*(Z*Z))*I := by rw [hfirst]; grind only
  grind only

def pairedCenterReciprocal (n : Nat) : Scalar :=
  ⟨ofQComplex ⟨reciprocalSquare (n+1),0⟩,ofQComplex_valid _⟩

/-- The actual reciprocal agrees exactly with its quadratic center polynomial
plus a supplied fourth-order remainder. -/
theorem pairedSmallDiskLiteralInverse_center_expansion (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) :
    (add (add ((pairedSmallDiskLiteralInverseMap n).eval z hz).val (pairedCenterReciprocal n).val)
      (mul (mul (pairedCenterReciprocal n).val (pairedCenterReciprocal n).val) (mul z.val z.val))).Equiv
    (mul (mul (mul (pairedCenterReciprocal n).val (pairedCenterReciprocal n).val)
      (mul (mul z.val z.val) (mul z.val z.val))) ((pairedSmallDiskLiteralInverseMap n).eval z hz).val) := by
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
    (hleft := add_valid (add_valid i.property c.property)
      (mul_valid (mul_valid c.property c.property) (mul_valid z.property z.property)))
    (hright := mul_valid (mul_valid (mul_valid c.property c.property)
      (mul_valid (mul_valid z.property z.property) (mul_valid z.property z.property))) i.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let T := ComplexRawQuotient.ofQComplex ⟨t,0⟩
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let I := ComplexRawQuotient.ofRaw i.val i.property
  change (Z*Z-T)*I=1 at hI
  change T*C=1 at hC
  change I+C+(C*C)*(Z*Z)=(C*C)*((Z*Z)*(Z*Z))*I
  exact expansion_algebra Z T C I hI hC

theorem pairedCenterReciprocal_small (n : Nat) : Small (pairedCenterReciprocal n).val 1 := by
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have h0 : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hn hn))
  have h1 : reciprocalSquare (n+1)≤1 := by
    have h := reciprocalSquare_antitone 1 (n+1) (by omega) (by omega)
    simpa only [show reciprocalSquare 1=1 by decide +kernel] using h
  refine ⟨?_,?_,?_,?_⟩
  · intro a b
    change -1≤reciprocalSquare (n+1)
    grind only
  · intro a b
    exact h1
  · intro a b
    change (-1:Rat)≤0
    decide +kernel
  · intro a b
    change (0:Rat)≤1
    decide +kernel

/-- A summable inverse-square majorant for the actual fourth-order remainder. -/
theorem pairedSmallDiskLiteralInverse_center_remainder_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (add (add ((pairedSmallDiskLiteralInverseMap n).eval z hz).val (pairedCenterReciprocal n).val)
      (mul (mul (pairedCenterReciprocal n).val (pairedCenterReciprocal n).val) (mul z.val z.val)))
      (256*R*R*R*R*reciprocalSquare (n+1)) := by
  let c := pairedCenterReciprocal n
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have h0 : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hn hn))
  have hc := Small.mul c.property c.property (show (0:Rat)≤1 by decide +kernel) (show (0:Rat)≤1 by decide +kernel)
    (pairedCenterReciprocal_small n) (pairedCenterReciprocal_small n)
  have hz2 := Small.mul z.property z.property hR hR hs hs
  have hR2 : 0≤2*R*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR
  have hz4 := Small.mul (mul_valid z.property z.property) (mul_valid z.property z.property) hR2 hR2 hz2 hz2
  have hR4 : 0≤2*(2*R*R)*(2*R*R) := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR2) hR2
  have hcz := Small.mul (mul_valid c.property c.property)
    (mul_valid (mul_valid z.property z.property) (mul_valid z.property z.property))
    (show (0:Rat)≤2*1*1 by decide +kernel) hR4 hc hz4
  have hb := Small.mul
    (mul_valid (mul_valid c.property c.property)
      (mul_valid (mul_valid z.property z.property) (mul_valid z.property z.property))) i.property
    (Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide +kernel) (show (0:Rat)≤2*1*1 by decide +kernel)) hR4)
    (Rat.mul_nonneg (show (0:Rat)≤4 by decide +kernel) h0) hcz
    (pairedSmallDiskLiteralInverse_bound z (LocalODE.interior_bound _ z hz) n)
  have he : 2*(2*(2*1*1)*(2*(2*R*R)*(2*R*R)))*(4*reciprocalSquare (n+1))=
      256*R*R*R*R*reciprocalSquare (n+1) := by grind only
  rw [he] at hb
  exact Small.congr
    (mul_valid (mul_valid (mul_valid c.property c.property)
      (mul_valid (mul_valid z.property z.property) (mul_valid z.property z.property))) i.property)
    (add_valid (add_valid i.property c.property)
      (mul_valid (mul_valid c.property c.property) (mul_valid z.property z.property)))
    (equiv_symm (pairedSmallDiskLiteralInverse_center_expansion z hz n)) hb

end ComputableAnalysis.ModularForms
