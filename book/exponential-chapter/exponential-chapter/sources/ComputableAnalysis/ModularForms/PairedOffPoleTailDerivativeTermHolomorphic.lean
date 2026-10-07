import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeContinuity

/-! Actual literal tail derivative functions are holomorphic on the full cutoff disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailInverseMap (B n : Nat) : DomainFunctions.Map where
  domain := (pairedOffPoleTailMap B).domain
  eval := pairedOffPoleTailInverse B n
  domain_congr := (pairedOffPoleTailMap B).domain_congr
  eval_congr z w hz hw he := RepresentedReciprocal.inverse_congr _ _ _ _
    ((pairedLiteralDenominatorMap (pairedIntegerSquare (pairedTailShift B n))).eval_congr
      z w trivial trivial he)

def pairedOffPoleTailInverseMap_holomorphic (B n : Nat) : Holomorphic (pairedOffPoleTailInverseMap B n) := by
  let hf := ReciprocalHolomorphic.holomorphic.compose
    (pairedLiteralDenominatorMap_holomorphic (pairedIntegerSquare (pairedTailShift B n)))
  apply hf.transfer (pairedOffPoleTailInverseMap B n)
    (fun z hz => ⟨trivial,pairedIntegerDenominator_nonzero z (B:Rat) (pairedTailShift B n)
      Rat.natCast_nonneg (LocalODE.interior_bound _ z hz)
      (by unfold pairedTailShift; omega) (pairedTailShift_large B n)⟩)
    ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
  intro z hz
  exact equiv_refl _ ((pairedOffPoleTailInverseMap B n).eval z hz).property

def pairedOffPoleTailDerivativeTermMap (B n : Nat) : DomainFunctions.Map where
  domain := (pairedOffPoleTailMap B).domain
  eval := pairedOffPoleTailDerivativeTerm B n
  domain_congr := (pairedOffPoleTailMap B).domain_congr
  eval_congr z w hz hw he := pairedOffPoleTailDerivativeTerm_congr B n z w hz hw he

def pairedOffPoleTailDerivativeTermMap_holomorphic (B n : Nat) :
    Holomorphic (pairedOffPoleTailDerivativeTermMap B n) := by
  let hi := pairedOffPoleTailInverseMap_holomorphic B n
  let htwo := affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex ⟨2,0⟩,ofQComplex_valid _⟩
  let hzz := htwo.productOn htwo (fun _ _ => trivial)
  let hisq := hi.productOn hi (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
  let hprod := hisq.productOn hzz (fun _ _ => trivial)
  let twoMap := affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex ⟨2,0⟩,ofQComplex_valid _⟩
  let invMap := pairedOffPoleTailInverseMap B n
  let sqMap := productOn invMap invMap (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
  let prodMap := productOn sqMap (productOn twoMap twoMap (fun _ _ => trivial)) (fun _ _ => trivial)
  let f := sumOn (sumOn invMap invMap (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz))
    (negate prodMap) (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
  let hf : Holomorphic f := (hi.sumOn hi (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)).sumOn
    hprod.negate (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
  apply hf.transfer (pairedOffPoleTailDerivativeTermMap B n)
    (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
    ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
  intro z hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (f.eval z hz).property)
    (hright := (pairedOffPoleTailDerivativeTerm B n z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (pairedOffPoleTailInverse B n z hz).val
    (pairedOffPoleTailInverse B n z hz).property
  let A := ComplexRawQuotient.ofQComplex ⟨(2:Rat),0⟩
  change (I+I)+ -((I*I)*((0+A*Z)*(0+A*Z)))=(I+I)-((Z+Z)*(Z+Z))*(I*I)
  have htwo : A=((2:Int):ComplexRawQuotient.Value) := by
    simpa only [show ((2:Int):Rat)=2 by decide +kernel] using integer_constant (2:Int)
  rw [htwo]
  grind only

def pairedOffPoleTailDerivativePrefixMap_holomorphic (B N : Nat) : Holomorphic (pairedOffPoleTailDerivativePrefixMap B N) := by
  induction N with
  | zero =>
    let h := affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨zero,ofQComplex_valid _⟩
    apply h.transfer (pairedOffPoleTailDerivativePrefixMap B 0) (fun _ _ => trivial)
      ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
    intro z hz
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((affine ⟨zero,ofQComplex_valid _⟩ ⟨zero,ofQComplex_valid _⟩).eval z trivial).property)
      (hright := ((pairedOffPoleTailDerivativePrefixMap B 0).eval z hz).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change 0+0*Z=0
    grind only
  | succ N ih =>
    let hf := ih.sumOn (pairedOffPoleTailDerivativeTermMap_holomorphic B N) (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
    apply hf.transfer (pairedOffPoleTailDerivativePrefixMap B (N+1)) (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
      ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
    intro z hz
    simp only [pairedOffPoleTailDerivativePrefixMap,sumOn,scalarSum,ScalarSeries.block.eq_2,Nat.zero_add]
    exact equiv_refl _ (add_valid
      (ScalarSeries.block_valid _ (fun n => ((pairedOffPoleTailDerivativeTermMap B n).eval z hz).property) 0 N)
      ((pairedOffPoleTailDerivativeTermMap B N).eval z hz).property)

end ComputableAnalysis.ModularForms
