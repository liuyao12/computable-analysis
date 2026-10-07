import ComputableAnalysis.ModularForms.IntegerPowerRemainderTail

/-! Constructed next-power derivative tails and comparison with actual finite derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def integerPowerDerivativeTailPrefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => ((pairedIntegerPowerMap_holomorphic k (4*B+n)).derivative z hz).val) 0 N

theorem integerPowerDerivativeTailPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B N : Nat) : (integerPowerDerivativeTailPrefix z hz k B N).Valid :=
  ScalarSeries.block_valid _ (fun n => ((pairedIntegerPowerMap_holomorphic k (4*B+n)).derivative z hz).property) 0 N

theorem integerPowerDerivativeTailPrefix_agreement (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B N : Nat) :
    (integerPowerDerivativeTailPrefix z hz k B N).Equiv
      (neg (scaleRat (k:Rat) (ScalarSeries.block
        (fun n => (pairedIntegerPowerTailTerm z hz (k+1) B n).val) 0 N))) := by
  let t := fun n => (pairedIntegerPowerTailTerm z hz (k+1) B n).val
  have vt n : (t n).Valid := (pairedIntegerPowerTailTerm z hz (k+1) B n).property
  have h1 := ScalarSeries.block_congr _ _
    (fun n => pairedIntegerPowerMap_derivative z hz k (4*B+n)) 0 N
  have h2 := reciprocalSquare_block_neg (fun n => scaleRat (k:Rat) (t n))
    (fun n => scaleRat_valid (r := (k:Rat)) (vt n)) N
  have h3 := neg_equiv (representedBlock_scale t vt (k:Rat) 0 N)
  exact equiv_trans (integerPowerDerivativeTailPrefix_valid z hz k B N)
    (ScalarSeries.block_valid _ (fun n => neg_valid (scaleRat_valid (r := (k:Rat)) (vt n))) 0 N)
    (neg_valid (scaleRat_valid (r := (k:Rat)) (ScalarSeries.block_valid t vt 0 N))) h1
    (equiv_trans (ScalarSeries.block_valid _ (fun n => neg_valid (scaleRat_valid (r := (k:Rat)) (vt n))) 0 N)
      (neg_valid (ScalarSeries.block_valid _ (fun n => scaleRat_valid (r := (k:Rat)) (vt n)) 0 N))
      (neg_valid (scaleRat_valid (r := (k:Rat)) (ScalarSeries.block_valid t vt 0 N))) h2 h3)

def integerPowerDerivativeTailValue (z : Scalar) (hz : InUpperHalfPlane z.val) (k B : Nat) : ComplexRaw :=
  neg (scaleRat (k:Rat) (pairedIntegerPowerTailValue z hz (k+1) B))

theorem integerPowerDerivativeTailValue_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) :
    (integerPowerDerivativeTailValue z hz k B).Valid :=
  neg_valid (scaleRat_valid (r := (k:Rat)) (pairedIntegerPowerTailValue_valid z hz (k+1) B (by omega) hB))

private theorem neg_difference (x p : Scalar) :
    (neg (sub x.val p.val)).Equiv (sub (neg x.val) (neg p.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := neg_valid (sub_valid x.property p.property))
    (hright := sub_valid (neg_valid x.property) (neg_valid p.property))
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let P := ComplexRawQuotient.ofRaw p.val p.property
  change -(X-P)= -X- -P
  generalize X=u,P=v
  grind only

theorem integerPowerDerivativeTailValue_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (integerPowerDerivativeTailValue z hz k B)
      (integerPowerDerivativeTailPrefix z hz k B (N+1)))
      ((k:Rat)*(((2*32^(k+1):Nat):Rat)*(((N+1:Nat):Rat))⁻¹)) := by
  let s : Scalar := ⟨pairedIntegerPowerTailValue z hz (k+1) B,
    pairedIntegerPowerTailValue_valid z hz (k+1) B (by omega) hB⟩
  let p : Scalar := ⟨ScalarSeries.block (fun n => (pairedIntegerPowerTailTerm z hz (k+1) B n).val) 0 (N+1),
    ScalarSeries.block_valid _ (fun n => (pairedIntegerPowerTailTerm z hz (k+1) B n).property) 0 (N+1)⟩
  let ss : Scalar := ⟨scaleRat (k:Rat) s.val,scaleRat_valid s.property⟩
  let pp : Scalar := ⟨scaleRat (k:Rat) p.val,scaleRat_valid p.property⟩
  have h := SeriesLimitLaws.small_neg (represented_prefix_scale_close s p (k:Rat) _ Rat.natCast_nonneg
    (pairedIntegerPowerTailValue_close z hz (k+1) B (by omega) hB N))
  have he2 := FunctionTheory.sub_congr (equiv_refl _ (neg_valid ss.property))
    (equiv_symm (integerPowerDerivativeTailPrefix_agreement z hz k B (N+1)))
  exact Small.congr (neg_valid (sub_valid ss.property pp.property))
    (sub_valid (integerPowerDerivativeTailValue_valid z hz k B hk hB)
      (integerPowerDerivativeTailPrefix_valid z hz k B (N+1)))
    (equiv_trans (neg_valid (sub_valid ss.property pp.property))
      (sub_valid (neg_valid ss.property) (neg_valid pp.property))
      (sub_valid (integerPowerDerivativeTailValue_valid z hz k B hk hB)
        (integerPowerDerivativeTailPrefix_valid z hz k B (N+1))) (neg_difference ss pp) he2) h

end ComputableAnalysis.ModularForms
