import ComputableAnalysis.ModularForms.PairedSmallDiskRemainderLimit

/-! Schedule and representation agreement for the actual reciprocal-tail remainder limit. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedSmallDiskRemainderRate_nonnegative (H : Rat) (hH : 0≤H) (N : Nat) :
    0≤pairedSmallDiskRemainderRate H N := by
  have hp : (0:Rat)<((N+1:Nat):Rat) := by exact_mod_cast (show 0<N+1 by omega)
  exact Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hp))) hH) hH

theorem pairedSmallDiskRemainderTerm_congr (a b z w : Scalar)
    (ha : LocalODE.interior (1/4) a) (hb : LocalODE.interior (1/4) b)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (hab : a.val.Equiv b.val) (hzw : z.val.Equiv w.val) (n : Nat) :
    (pairedSmallDiskRemainderTerm a z ha hz n).Equiv (pairedSmallDiskRemainderTerm b w hb hw n) :=
  FunctionTheory.sub_congr
    (FunctionTheory.sub_congr
      ((pairedSmallDiskTermMap n).eval_congr z w hz hw hzw)
      ((pairedSmallDiskTermMap n).eval_congr a b ha hb hab))
    (mul_equiv (pairedSmallDiskDerivativeTerm a (LocalODE.interior_bound _ a ha) n).property
      (pairedSmallDiskDerivativeTerm b (LocalODE.interior_bound _ b hb) n).property
      (sub_valid z.property a.property) (sub_valid w.property b.property)
      (pairedSmallDiskDerivativeTerm_congr a b (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ b hb) hab n)
      (FunctionTheory.sub_congr hzw hab))

theorem pairedSmallDiskRemainderValue_agreement (a b z w : Scalar)
    (ha : LocalODE.interior (1/4) a) (hb : LocalODE.interior (1/4) b)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (H K : Rat) (hH : 0≤H) (hK : 0≤K)
    (hdH : Small (sub z.val a.val) H) (hdK : Small (sub w.val b.val) K)
    (hab : a.val.Equiv b.val) (hzw : z.val.Equiv w.val) :
    (pairedSmallDiskRemainderValue a z ha hz H).Equiv (pairedSmallDiskRemainderValue b w hb hw K) :=
  RepresentedCauchySum.value_congr _ _ _ _ _ _
    (pairedSmallDiskRemainderRate_shrinks H) (pairedSmallDiskRemainderRate_shrinks K)
    (pairedSmallDiskRemainderRate_nonnegative H hH) (pairedSmallDiskRemainderRate_nonnegative K hK)
    (pairedSmallDiskRemainderPrefix_cauchy a z ha hz H hH hdH)
    (pairedSmallDiskRemainderPrefix_cauchy b w hb hw K hK hdK)
    (fun N => ScalarSeries.block_congr _ _ (pairedSmallDiskRemainderTerm_congr a b z w ha hb hz hw hab hzw) 0 (N+1))

def pairedSmallDiskDisplacementBound (a z : Scalar) : Nat :=
  pairedInternalBound ⟨sub z.val a.val,sub_valid z.property a.property⟩

theorem pairedSmallDiskDisplacementBound_small (a z : Scalar) :
    Small (sub z.val a.val) ((pairedSmallDiskDisplacementBound a z):Rat) :=
  pairedInternalBound_small ⟨sub z.val a.val,sub_valid z.property a.property⟩

def pairedSmallDiskRemainder (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) : ComplexRaw :=
  pairedSmallDiskRemainderValue a z ha hz ((pairedSmallDiskDisplacementBound a z):Rat)

theorem pairedSmallDiskRemainder_valid (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z) :
    (pairedSmallDiskRemainder a z ha hz).Valid :=
  pairedSmallDiskRemainderValue_valid a z ha hz _ Rat.natCast_nonneg
    (pairedSmallDiskDisplacementBound_small a z)

theorem pairedSmallDiskRemainder_agrees (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    (pairedSmallDiskRemainder a z ha hz).Equiv (pairedSmallDiskRemainderValue a z ha hz H) :=
  pairedSmallDiskRemainderValue_agreement a a z z ha ha hz hz
    _ H Rat.natCast_nonneg hH (pairedSmallDiskDisplacementBound_small a z) hd
    (equiv_refl _ a.property) (equiv_refl _ z.property)

theorem pairedSmallDiskRemainder_bound (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (pairedSmallDiskRemainder a z ha hz) (262144*H*H) :=
  Small.congr (pairedSmallDiskRemainderValue_valid a z ha hz H hH hd)
    (pairedSmallDiskRemainder_valid a z ha hz)
    (equiv_symm (pairedSmallDiskRemainder_agrees a z ha hz H hH hd))
    (pairedSmallDiskRemainderValue_bound a z ha hz H hH hd)

theorem pairedSmallDiskRemainder_congr (a b z w : Scalar)
    (ha : LocalODE.interior (1/4) a) (hb : LocalODE.interior (1/4) b)
    (hz : LocalODE.interior (1/4) z) (hw : LocalODE.interior (1/4) w)
    (hab : a.val.Equiv b.val) (hzw : z.val.Equiv w.val) :
    (pairedSmallDiskRemainder a z ha hz).Equiv (pairedSmallDiskRemainder b w hb hw) :=
  pairedSmallDiskRemainderValue_agreement a b z w ha hb hz hw
    _ _ Rat.natCast_nonneg Rat.natCast_nonneg
    (pairedSmallDiskDisplacementBound_small a z) (pairedSmallDiskDisplacementBound_small b w) hab hzw

theorem pairedSmallDiskRemainder_close (a z : Scalar)
    (ha : LocalODE.interior (1/4) a) (hz : LocalODE.interior (1/4) z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (pairedSmallDiskRemainder a z ha hz)
      (ScalarSeries.block (pairedSmallDiskRemainderTerm a z ha hz) 0 (N+1)))
      (pairedSmallDiskRemainderRate H N) := by
  have vp := ScalarSeries.block_valid _ (pairedSmallDiskRemainderTerm_valid a z ha hz) 0 (N+1)
  exact Small.congr (sub_valid (pairedSmallDiskRemainderValue_valid a z ha hz H hH hd) vp)
    (sub_valid (pairedSmallDiskRemainder_valid a z ha hz) vp)
    (FunctionTheory.sub_congr (equiv_symm (pairedSmallDiskRemainder_agrees a z ha hz H hH hd))
      (equiv_refl _ vp)) (pairedSmallDiskRemainderValue_close a z ha hz H hH hd N)

end ComputableAnalysis.ModularForms
