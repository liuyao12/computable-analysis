import ComputableAnalysis.ModularForms.PairedIntegerPeriodicity

/-! Holomorphic pole normalization at every integer, with residue one. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def entireIntegerShiftMap (k : Int) : DomainFunctions.Map where
  domain _ := True
  eval z _ := integerShiftScalar z k
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ he := integerAffine_equiv 1 k he

def entireIntegerShiftMap_holomorphic (k : Int) : DomainFunctions.Holomorphic (entireIntegerShiftMap k) := by
  let hf := DomainFunctions.affine_holomorphic (rationalInteger k) (rationalInteger 1)
  apply hf.transfer (entireIntegerShiftMap k) (fun _ _ => trivial) ⟨(fun _ _ => unitError),(fun _ _ _ _ => trivial)⟩
  intro z hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((DomainFunctions.affine (rationalInteger k) (rationalInteger 1)).eval z trivial).property)
    (hright := (integerShiftScalar z k).property)
  change ComplexRawQuotient.ofQComplex ⟨(k:Rat),0⟩+
    ComplexRawQuotient.ofQComplex ⟨(1:Rat),0⟩*ComplexRawQuotient.ofRaw z.val z.property =
    ComplexRawQuotient.ofRaw (integerAffine 1 k z.val) _
  rw [integerAffine_class,integer_constant]
  have ho : ComplexRawQuotient.ofQComplex ⟨(1:Rat),0⟩ = ((1:Int):ComplexRawQuotient.Value) := by
    simpa only [Rat.intCast_one] using integer_constant (1:Int)
  rw [ho]
  grind only

def pairedIntegerPoleExtensionMap (k : Int) : DomainFunctions.Map :=
  compose pairedPoleExtensionMap (entireIntegerShiftMap (-k))

def pairedIntegerPoleExtensionMap_holomorphic (k : Int) :
    DomainFunctions.Holomorphic (pairedIntegerPoleExtensionMap k) :=
  pairedPoleExtensionMap_holomorphic.compose (entireIntegerShiftMap_holomorphic (-k))

theorem pairedIntegerPoleExtensionMap_upper (k : Int) (z : Scalar)
    (hz : (pairedIntegerPoleExtensionMap k).domain z) (hupper : InUpperHalfPlane z.val) :
    ((pairedIntegerPoleExtensionMap k).eval z hz).val.Equiv
      (mul (integerShiftScalar z (-k)).val (upperPairedPartialFractionValue z hupper)) := by
  have hw := integerShiftScalar_upper z hupper (-k)
  have h := pairedPoleExtensionMap_upper (integerShiftScalar z (-k)) (compose_outer_mem hz) hw
  have he := mul_equiv (integerShiftScalar z (-k)).property (integerShiftScalar z (-k)).property
    (upperPairedPartialFractionValue_valid _ hw) (upperPairedPartialFractionValue_valid z hupper)
    (equiv_refl _ (integerShiftScalar z (-k)).property)
    (upperPairedPartialFractionValue_period_int z hupper (-k))
  exact equiv_trans ((pairedIntegerPoleExtensionMap k).eval z hz).property
    (mul_valid (integerShiftScalar z (-k)).property (upperPairedPartialFractionValue_valid _ hw))
    (mul_valid (integerShiftScalar z (-k)).property (upperPairedPartialFractionValue_valid z hupper)) h he

theorem integerShiftScalar_at_integer (k : Int) (z : Scalar)
    (hz : z.val.Equiv (rationalInteger k).val) :
    (integerShiftScalar z (-k)).val.Equiv zero := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := (rationalInteger k).property) hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerShiftScalar z (-k)).property) (hright := ofQComplex_valid _)
  change ComplexRawQuotient.ofRaw (integerAffine 1 (-k) z.val) _ = 0
  rw [integerAffine_class]
  change ComplexRawQuotient.ofRaw z.val z.property = ComplexRawQuotient.ofQComplex ⟨(k:Rat),0⟩ at he
  rw [integer_constant] at he
  rw [he]
  grind only

theorem pairedIntegerPoleExtensionMap_at_integer (k : Int) (z : Scalar)
    (hz : (pairedIntegerPoleExtensionMap k).domain z)
    (he : z.val.Equiv (rationalInteger k).val) :
    ((pairedIntegerPoleExtensionMap k).eval z hz).val.Equiv (ofQComplex QComplex.one) :=
  pairedPoleExtensionMap_zero (integerShiftScalar z (-k)) (compose_outer_mem hz)
    (integerShiftScalar_at_integer k z he)

end ComputableAnalysis.ModularForms
