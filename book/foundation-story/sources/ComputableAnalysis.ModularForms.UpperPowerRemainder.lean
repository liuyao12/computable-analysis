import ComputableAnalysis.ModularForms.UpperReciprocalRemainder

/-! Exact product recurrence for the certified inverse-power remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert DomainFunctions

def latticePowerRemainder (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (k : Nat) : ComplexRaw :=
  DomainFunctions.remainder (latticePowerMap u hu k) a ha
    ((latticePowerMap_holomorphic u hu k).derivative a ha) z hz

theorem latticePowerRemainder_valid (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (k : Nat) :
    (latticePowerRemainder u hu a z ha hz k).Valid := DomainFunctions.remainder_valid _ _ _ _ _ _

theorem latticePowerRemainder_zero (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (latticePowerRemainder u hu a z ha hz 0).Equiv zero := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := latticePowerRemainder_valid u hu a z ha hz 0) (hright := ofQComplex_valid _)
  change (1 + -1) + -(0*(ComplexRawQuotient.ofRaw z.val z.property +
    -ComplexRawQuotient.ofRaw a.val a.property)) = 0
  grind only

theorem latticePowerRemainder_succ (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (k : Nat) :
    (latticePowerRemainder u hu a z ha hz (k+1)).Equiv
      (add (add (mul (latticePowerRemainder u hu a z ha hz k) (latticeInverse a ha u hu).val)
        (mul (LocalODE.power (latticeInverse a ha u hu).val k)
          (DomainFunctions.remainder (latticeReciprocalMap u hu) a ha
            ((latticeReciprocalMap_holomorphic u hu).derivative a ha) z hz)))
        (mul (sub (LocalODE.power (latticeInverse z hz u hu).val k)
          (LocalODE.power (latticeInverse a ha u hu).val k))
          (sub (latticeInverse z hz u hu).val (latticeInverse a ha u hu).val))) := by
  exact product_remainder (latticePowerMap u hu k) (latticeReciprocalMap u hu) (fun _ hz => hz)
    a ha ((latticePowerMap_holomorphic u hu k).derivative a ha)
    ((latticeReciprocalMap_holomorphic u hu).derivative a ha) z hz

theorem latticePower_difference_succ (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero)
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) (k : Nat) :
    (sub (LocalODE.power (latticeInverse z hz u hu).val (k+1))
      (LocalODE.power (latticeInverse a ha u hu).val (k+1))).Equiv
      (add (mul (sub (LocalODE.power (latticeInverse z hz u hu).val k)
        (LocalODE.power (latticeInverse a ha u hu).val k)) (latticeInverse z hz u hu).val)
        (mul (LocalODE.power (latticeInverse a ha u hu).val k)
          (sub (latticeInverse z hz u hu).val (latticeInverse a ha u hu).val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (LocalODE.power_valid _ (latticeInverse z hz u hu).property (k+1))
      (LocalODE.power_valid _ (latticeInverse a ha u hu).property (k+1)))
    (hright := add_valid
      (mul_valid (sub_valid (LocalODE.power_valid _ (latticeInverse z hz u hu).property k)
        (LocalODE.power_valid _ (latticeInverse a ha u hu).property k)) (latticeInverse z hz u hu).property)
      (mul_valid (LocalODE.power_valid _ (latticeInverse a ha u hu).property k)
        (sub_valid (latticeInverse z hz u hu).property (latticeInverse a ha u hu).property)))
  let R := ComplexRawQuotient.ofRaw (latticeInverse a ha u hu).val (latticeInverse a ha u hu).property
  let S := ComplexRawQuotient.ofRaw (latticeInverse z hz u hu).val (latticeInverse z hz u hu).property
  change ComplexRawQuotient.ofRaw (LocalODE.power (latticeInverse z hz u hu).val k)
      (LocalODE.power_valid _ (latticeInverse z hz u hu).property k)*S +
    -(ComplexRawQuotient.ofRaw (LocalODE.power (latticeInverse a ha u hu).val k)
      (LocalODE.power_valid _ (latticeInverse a ha u hu).property k)*R) =
    (ComplexRawQuotient.ofRaw (LocalODE.power (latticeInverse z hz u hu).val k)
      (LocalODE.power_valid _ (latticeInverse z hz u hu).property k) +
      -ComplexRawQuotient.ofRaw (LocalODE.power (latticeInverse a ha u hu).val k)
        (LocalODE.power_valid _ (latticeInverse a ha u hu).property k))*S +
    ComplexRawQuotient.ofRaw (LocalODE.power (latticeInverse a ha u hu).val k)
      (LocalODE.power_valid _ (latticeInverse a ha u hu).property k)*(S + -R)
  rw [ScalarAlgebra.ofRaw_power _ (latticeInverse z hz u hu).property k,
    ScalarAlgebra.ofRaw_power _ (latticeInverse a ha u hu).property k]
  change S^k*S + -(R^k*R) = (S^k + -R^k)*S+R^k*(S + -R)
  grind only

end ComputableAnalysis.ModularForms
