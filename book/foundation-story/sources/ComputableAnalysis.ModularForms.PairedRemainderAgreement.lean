import ComputableAnalysis.ModularForms.PairedRemainderLimit

/-! Schedule and representation agreement for the actual reciprocal-tail remainder limit. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedTailRemainderRate_nonnegative (H : Rat) (hH : 0≤H) (N : Nat) :
    0≤pairedTailRemainderRate H N := by
  have hp : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
  exact Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hp))) hH) hH

theorem pairedTailRemainderTerm_congr (B : Nat) (a b z w : Scalar)
    (ha : InUpperHalfPlane a.val) (hb : InUpperHalfPlane b.val)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (hab : a.val.Equiv b.val) (hzw : z.val.Equiv w.val) (n : Nat) :
    (pairedTailRemainderTerm B a z ha hz n).Equiv (pairedTailRemainderTerm B b w hb hw n) :=
  FunctionTheory.sub_congr
    (FunctionTheory.sub_congr
      ((pairedReciprocalTermMap (4*B+n)).eval_congr z w hz hw hzw)
      ((pairedReciprocalTermMap (4*B+n)).eval_congr a b ha hb hab))
    (mul_equiv (upperPairedReciprocalDerivative a ha (pairedTailShift B n)).property
      (upperPairedReciprocalDerivative b hb (pairedTailShift B n)).property
      (sub_valid z.property a.property) (sub_valid w.property b.property)
      (upperPairedReciprocalDerivative_congr a b ha hb hab (pairedTailShift B n))
      (FunctionTheory.sub_congr hzw hab))

theorem pairedTailRemainderValue_agreement (B : Nat) (a b z w : Scalar)
    (ha : InUpperHalfPlane a.val) (hb : InUpperHalfPlane b.val)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (hA : Small a.val (B:Rat)) (hB : Small b.val (B:Rat))
    (hZ : Small z.val (B:Rat)) (hW : Small w.val (B:Rat))
    (H K : Rat) (hH : 0≤H) (hK : 0≤K)
    (hdH : Small (sub z.val a.val) H) (hdK : Small (sub w.val b.val) K)
    (hab : a.val.Equiv b.val) (hzw : z.val.Equiv w.val) :
    (pairedTailRemainderValue B a z ha hz H).Equiv (pairedTailRemainderValue B b w hb hw K) :=
  RepresentedCauchySum.value_congr _ _ _ _ _ _
    (pairedTailRemainderRate_shrinks H) (pairedTailRemainderRate_shrinks K)
    (pairedTailRemainderRate_nonnegative H hH) (pairedTailRemainderRate_nonnegative K hK)
    (pairedTailRemainderPrefix_cauchy B a z ha hz hA hZ H hH hdH)
    (pairedTailRemainderPrefix_cauchy B b w hb hw hB hW K hK hdK)
    (fun N => ScalarSeries.block_congr _ _ (pairedTailRemainderTerm_congr B a b z w ha hb hz hw hab hzw) 0 (N+1))

def pairedTailDisplacementBound (a z : Scalar) : Nat :=
  pairedInternalBound ⟨sub z.val a.val,sub_valid z.property a.property⟩

theorem pairedTailDisplacementBound_small (a z : Scalar) :
    Small (sub z.val a.val) ((pairedTailDisplacementBound a z):Rat) :=
  pairedInternalBound_small ⟨sub z.val a.val,sub_valid z.property a.property⟩

def pairedTailRemainder (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) : ComplexRaw :=
  pairedTailRemainderValue B a z ha hz ((pairedTailDisplacementBound a z):Rat)

theorem pairedTailRemainder_valid (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat)) :
    (pairedTailRemainder B a z ha hz).Valid :=
  pairedTailRemainderValue_valid B a z ha hz hA hZ _ Rat.natCast_nonneg
    (pairedTailDisplacementBound_small a z)

theorem pairedTailRemainder_agrees (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedTailRemainder B a z ha hz).Equiv (pairedTailRemainderValue B a z ha hz H) :=
  pairedTailRemainderValue_agreement B a a z z ha ha hz hz hA hA hZ hZ
    _ H Rat.natCast_nonneg hH (pairedTailDisplacementBound_small a z) hd
    (equiv_refl _ a.property) (equiv_refl _ z.property)

theorem pairedTailRemainder_bound (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedTailRemainder B a z ha hz) (1048576*H*H) :=
  Small.congr (pairedTailRemainderValue_valid B a z ha hz hA hZ H hH hd)
    (pairedTailRemainder_valid B a z ha hz hA hZ)
    (equiv_symm (pairedTailRemainder_agrees B a z ha hz hA hZ H hH hd))
    (pairedTailRemainderValue_bound B a z ha hz hA hZ H hH hd)

theorem pairedTailRemainder_congr (B : Nat) (a b z w : Scalar)
    (ha : InUpperHalfPlane a.val) (hb : InUpperHalfPlane b.val)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (hA : Small a.val (B:Rat)) (hB : Small b.val (B:Rat))
    (hZ : Small z.val (B:Rat)) (hW : Small w.val (B:Rat))
    (hab : a.val.Equiv b.val) (hzw : z.val.Equiv w.val) :
    (pairedTailRemainder B a z ha hz).Equiv (pairedTailRemainder B b w hb hw) :=
  pairedTailRemainderValue_agreement B a b z w ha hb hz hw hA hB hZ hW
    _ _ Rat.natCast_nonneg Rat.natCast_nonneg
    (pairedTailDisplacementBound_small a z) (pairedTailDisplacementBound_small b w) hab hzw

theorem pairedTailRemainder_close (B : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (hA : Small a.val (B:Rat)) (hZ : Small z.val (B:Rat))
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedTailRemainder B a z ha hz)
      (ScalarSeries.block (pairedTailRemainderTerm B a z ha hz) 0 (N+1)))
      (pairedTailRemainderRate H N) := by
  have vp := ScalarSeries.block_valid _ (pairedTailRemainderTerm_valid B a z ha hz) 0 (N+1)
  exact Small.congr (sub_valid (pairedTailRemainderValue_valid B a z ha hz hA hZ H hH hd) vp)
    (sub_valid (pairedTailRemainder_valid B a z ha hz hA hZ) vp)
    (FunctionTheory.sub_congr (equiv_symm (pairedTailRemainder_agrees B a z ha hz hA hZ H hH hd))
      (equiv_refl _ vp)) (pairedTailRemainderValue_close B a z ha hz hA hZ H hH hd N)

end ComputableAnalysis.ModularForms
