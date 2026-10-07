import ComputableAnalysis.ModularForms.PairedIntegerPoleExtension

/-! Actual holomorphic Laurent charts on punctured neighborhoods of every integer. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedPuncturedDomain (z : Scalar) : Prop := pairedRegularPartMap.domain z ∧ NonzeroBoxSearch.Nonzero z

def pairedPuncturedOpenData : ScalarTopology.OpenData pairedPuncturedDomain where
  invariant z w he := by
    exact and_congr (pairedRegularPartMap.domain_congr z w he) (NonzeroBoxSearch.nonzero_congr z w he)
  radius z hz := minRadius (pairedRegularPartMap_holomorphic.openDomain.radius z hz.1)
    (ReciprocalHolomorphic.holomorphic.openDomain.radius z hz.2)
  inside a ha z hd :=
    ⟨pairedRegularPartMap_holomorphic.openDomain.inside a ha.1 z (hd.mono (minRadius_left _ _)),
      ReciprocalHolomorphic.holomorphic.openDomain.inside a ha.2 z (hd.mono (minRadius_right _ _))⟩

def pairedPuncturedReciprocalMap : DomainFunctions.Map :=
  onDomain ReciprocalHolomorphic.function pairedPuncturedOpenData.invariant (fun _ h => h.2)

def pairedPuncturedRegularMap : DomainFunctions.Map :=
  onDomain pairedRegularPartMap pairedPuncturedOpenData.invariant (fun _ h => h.1)

def pairedZeroLaurentMap : DomainFunctions.Map :=
  sumOn pairedPuncturedReciprocalMap pairedPuncturedRegularMap
    (fun (z : Scalar) (hz : pairedPuncturedDomain z) => hz)

def pairedZeroLaurentMap_holomorphic : DomainFunctions.Holomorphic pairedZeroLaurentMap :=
  (ReciprocalHolomorphic.holomorphic.onDomain pairedPuncturedOpenData (fun _ h => h.2)).sumOn
    (pairedRegularPartMap_holomorphic.onDomain pairedPuncturedOpenData (fun _ h => h.1))
    (fun (z : Scalar) (hz : pairedPuncturedDomain z) => hz)

theorem pairedZeroLaurentMap_upper (z : Scalar) (hz : pairedZeroLaurentMap.domain z)
    (hupper : InUpperHalfPlane z.val) :
    (pairedZeroLaurentMap.eval z hz).val.Equiv (upperPairedPartialFractionValue z hupper) := by
  exact equiv_refl _ (pairedZeroLaurentMap.eval z hz).property

def pairedIntegerLaurentMap (k : Int) : DomainFunctions.Map :=
  compose pairedZeroLaurentMap (entireIntegerShiftMap (-k))

def pairedIntegerLaurentMap_holomorphic (k : Int) : DomainFunctions.Holomorphic (pairedIntegerLaurentMap k) :=
  pairedZeroLaurentMap_holomorphic.compose (entireIntegerShiftMap_holomorphic (-k))

theorem pairedIntegerLaurentMap_upper (k : Int) (z : Scalar)
    (hz : (pairedIntegerLaurentMap k).domain z) (hupper : InUpperHalfPlane z.val) :
    ((pairedIntegerLaurentMap k).eval z hz).val.Equiv (upperPairedPartialFractionValue z hupper) :=
  equiv_trans ((pairedIntegerLaurentMap k).eval z hz).property
    (upperPairedPartialFractionValue_valid _ (integerShiftScalar_upper z hupper (-k)))
    (upperPairedPartialFractionValue_valid z hupper)
    (pairedZeroLaurentMap_upper _ (compose_outer_mem hz) (integerShiftScalar_upper z hupper (-k)))
    (upperPairedPartialFractionValue_period_int z hupper (-k))

theorem pairedZeroLaurentMap_normalized (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    (mul z.val (pairedZeroLaurentMap.eval z hz).val).Equiv (pairedPoleExtensionMap.eval z hz.1).val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (RepresentedReciprocal.inverse z hz.2).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse z hz.2)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid z.property (pairedZeroLaurentMap.eval z hz).property)
    (hright := (pairedPoleExtensionMap.eval z hz.1).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse z hz.2).val (RepresentedReciprocal.inverse z hz.2).property
  let S := ComplexRawQuotient.ofRaw (pairedRegularPartMap.eval z hz.1).val (pairedRegularPartMap.eval z hz.1).property
  change Z*I=1 at hi
  change Z*(I+S)=1+Z*S
  grind only

end ComputableAnalysis.ModularForms
