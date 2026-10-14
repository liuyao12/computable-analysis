import ComputableAnalysis.ModularForms.PairedRiccatiUniformLocalVariation

/-! Adding justified local variation estimates along a finite represented chain. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def positiveChainLength (H : Nat → QPos) : Nat → Rat
  | 0 => 0
  | K+1 => positiveChainLength H K+(H K).val

theorem representedDifference_split (x y z : Scalar) :
    (add (sub x.val y.val) (sub y.val z.val)).Equiv (sub x.val z.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (sub_valid x.property y.property) (sub_valid y.property z.property))
    (hright := sub_valid x.property z.property)
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change (X-Y)+(Y-Z)=X-Z
  grind only

theorem pairedEntireRiccatiMap_finite_chain_variation (p : Nat → Scalar) (H : Nat → QPos)
    (K : Nat)
    (hr : ∀ n, n<K → (H n).val≤
      ((pairedEntireRiccatiMap_holomorphic.atPoint (p n) trivial).delta unitError).val)
    (hd : ∀ n, n<K → Small (sub (p (n+1)).val (p n).val) (H n).val) :
    Small (sub (pairedEntireRiccatiMap.eval (p K) trivial).val
      (pairedEntireRiccatiMap.eval (p 0) trivial).val) (2854864385*positiveChainLength H K) := by
  induction K with
  | zero =>
    have he : zero.Equiv (sub (pairedEntireRiccatiMap.eval (p 0) trivial).val
        (pairedEntireRiccatiMap.eval (p 0) trivial).val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ofQComplex_valid _) (hright := sub_valid
          (pairedEntireRiccatiMap.eval (p 0) trivial).property (pairedEntireRiccatiMap.eval (p 0) trivial).property)
      let X := ComplexRawQuotient.ofRaw (pairedEntireRiccatiMap.eval (p 0) trivial).val
        (pairedEntireRiccatiMap.eval (p 0) trivial).property
      change 0=X-X
      grind only
    exact Small.congr (ofQComplex_valid _)
      (sub_valid (pairedEntireRiccatiMap.eval (p 0) trivial).property
        (pairedEntireRiccatiMap.eval (p 0) trivial).property) he (Small.zero (by simp only [positiveChainLength,Rat.mul_zero]; decide +kernel))
  | succ K ih =>
    have hk := ih (fun n hn => hr n (by omega)) (fun n hn => hd n (by omega))
    have hstep := pairedEntireRiccatiMap_uniform_local_variation (p K) (p (K+1)) (H K)
      (hr K (by omega)) (hd K (by omega))
    have hs := LocalODE.small_add hstep hk
    have he := representedDifference_split (pairedEntireRiccatiMap.eval (p (K+1)) trivial)
      (pairedEntireRiccatiMap.eval (p K) trivial) (pairedEntireRiccatiMap.eval (p 0) trivial)
    exact (Small.congr
      (add_valid (sub_valid (pairedEntireRiccatiMap.eval (p (K+1)) trivial).property
        (pairedEntireRiccatiMap.eval (p K) trivial).property)
        (sub_valid (pairedEntireRiccatiMap.eval (p K) trivial).property
          (pairedEntireRiccatiMap.eval (p 0) trivial).property))
      (sub_valid (pairedEntireRiccatiMap.eval (p (K+1)) trivial).property
        (pairedEntireRiccatiMap.eval (p 0) trivial).property) he hs).mono
      (by change 2854864385*(H K).val+2854864385*positiveChainLength H K≤
        2854864385*(positiveChainLength H K+(H K).val); grind only)

end ComputableAnalysis.ModularForms
