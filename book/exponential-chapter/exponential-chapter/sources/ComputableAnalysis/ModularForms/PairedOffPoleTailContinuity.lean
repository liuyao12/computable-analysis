import ComputableAnalysis.ModularForms.PairedOffPoleAssembly
import ComputableAnalysis.ModularForms.PairedRegularDivisionTermHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainUniformLimitContinuity

/-! Actual reciprocal tail continuity on its full interior domain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedOffPoleTailTermMap (B n : Nat) : DomainFunctions.Map where
  domain := LocalODE.interior (B:Rat)
  eval z hz := pairedTailTerm z B (LocalODE.interior_bound _ z hz) n
  domain_congr := (pairedOffPoleTailMap B).domain_congr
  eval_congr z w hz hw he := pairedTailTerm_congr z w B
    (LocalODE.interior_bound _ z hz) (LocalODE.interior_bound _ w hw) he n

def pairedOffPoleTailTermMap_holomorphic (B n : Nat) : Holomorphic (pairedOffPoleTailTermMap B n) := by
  let k := pairedTailShift B n
  let t := pairedIntegerSquare k
  let hi := ReciprocalHolomorphic.holomorphic.compose (pairedLiteralDenominatorMap_holomorphic t)
  let inv : DomainFunctions.Map := {
    domain := LocalODE.interior (B:Rat)
    eval z hz := RepresentedReciprocal.inverse (pairedLiteralDenominator z t)
      (pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg
        (LocalODE.interior_bound _ z hz) (by dsimp [k,pairedTailShift]; omega) (pairedTailShift_large B n))
    domain_congr := (pairedOffPoleTailMap B).domain_congr
    eval_congr z w hz hw he := RepresentedReciprocal.inverse_congr _ _ _ _
      ((pairedLiteralDenominatorMap t).eval_congr z w trivial trivial he) }
  have hinv : Holomorphic inv := by
    apply hi.transfer inv
      (fun z hz => ⟨trivial,pairedIntegerDenominator_nonzero z (B:Rat) k Rat.natCast_nonneg
        (LocalODE.interior_bound _ z hz) (by dsimp [k,pairedTailShift]; omega) (pairedTailShift_large B n)⟩)
      ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
    intro z hz
    exact equiv_refl _ (inv.eval z hz).property
  let num := affine ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex ⟨2,0⟩,ofQComplex_valid _⟩
  let hn := affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨ofQComplex ⟨2,0⟩,ofQComplex_valid _⟩
  let hf := hinv.productOn hn (fun _ _ => trivial)
  apply hf.transfer (pairedOffPoleTailTermMap B n) (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
    ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
  intro z hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((productOn inv num (fun _ _ => trivial)).eval z hz).property)
    (hright := ((pairedOffPoleTailTermMap B n).eval z hz).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw (inv.eval z hz).val (inv.eval z hz).property
  change I*(0+ComplexRawQuotient.ofQComplex ⟨2,0⟩*Z)=(Z+Z)*I
  have htwo : ComplexRawQuotient.ofQComplex ⟨(2:Rat),0⟩=((2:Int):ComplexRawQuotient.Value) := by
    simpa only [show ((2:Int):Rat)=2 by decide +kernel] using integer_constant (2:Int)
  rw [htwo]
  grind only

def pairedOffPoleTailPrefixMap (B N : Nat) : DomainFunctions.Map where
  domain := (pairedOffPoleTailMap B).domain
  eval z hz := ⟨ScalarSeries.block (fun n => ((pairedOffPoleTailTermMap B n).eval z hz).val) 0 N,
    ScalarSeries.block_valid _ (fun n => ((pairedOffPoleTailTermMap B n).eval z hz).property) 0 N⟩
  domain_congr := (pairedOffPoleTailMap B).domain_congr
  eval_congr z w hz hw he := ScalarSeries.block_congr _ _
    (fun n => (pairedOffPoleTailTermMap B n).eval_congr z w hz hw he) 0 N

def pairedOffPoleTailPrefixMap_holomorphic (B N : Nat) : Holomorphic (pairedOffPoleTailPrefixMap B N) := by
  induction N with
  | zero =>
    let h := affine_holomorphic ⟨zero,ofQComplex_valid _⟩ ⟨zero,ofQComplex_valid _⟩
    apply h.transfer (pairedOffPoleTailPrefixMap B 0) (fun _ _ => trivial)
      ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
    intro z hz
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((affine ⟨zero,ofQComplex_valid _⟩ ⟨zero,ofQComplex_valid _⟩).eval z trivial).property)
      (hright := ((pairedOffPoleTailPrefixMap B 0).eval z hz).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change 0+0*Z=0
    grind only
  | succ N ih =>
    let hf := ih.sumOn (pairedOffPoleTailTermMap_holomorphic B N) (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
    apply hf.transfer (pairedOffPoleTailPrefixMap B (N+1)) (fun (z : Scalar) (hz : LocalODE.interior (B:Rat) z) => hz)
      ⟨LocalODE.interiorRadius (B:Rat),LocalODE.interiorRadius_inside (B:Rat)⟩
    intro z hz
    simp only [pairedOffPoleTailPrefixMap,sumOn,scalarSum,ScalarSeries.block.eq_2,Nat.zero_add]
    exact equiv_refl _ (add_valid
      (ScalarSeries.block_valid _ (fun n => ((pairedOffPoleTailTermMap B n).eval z hz).property) 0 N)
      ((pairedOffPoleTailTermMap B N).eval z hz).property)

noncomputable def pairedOffPoleTailMap_continuous (B : Nat) :
    ContinuousOn (pairedOffPoleTailMap B).domain (pairedOffPoleTailMap B).eval := by
  apply continuousOn_of_uniform_prefixes _
    (fun N z hz => (pairedOffPoleTailPrefixMap B (N+1)).eval z hz)
    _ (fun N => ((16*B:Nat):Rat)*((N+1:Nat):Rat)⁻¹) (pairedReciprocalTail_shrinks (16*B))
  · intro N z hz
    exact pairedTailValue_close z B (LocalODE.interior_bound _ z hz) N
  · intro N
    exact (pairedOffPoleTailPrefixMap_holomorphic B (N+1)).continuous

end ComputableAnalysis.ModularForms
