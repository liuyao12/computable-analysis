import ComputableAnalysis.ModularForms.LambertWeightBound
import ComputableAnalysis.ModularForms.NomeGeometricSeries

/-! Executable weighted nome powers, explicit geometric errors, and finite telescoping. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def weightedNomePower (z : Scalar) (n : Nat) : ComplexRaw :=
  scaleRat ((n+1:Nat):Rat) (LocalODE.power z.val (n+1))

theorem weightedNomePower_valid (z : Scalar) (n : Nat) : (weightedNomePower z n).Valid :=
  scaleRat_valid (LocalODE.power_valid _ z.property (n+1))

theorem weightedNomePower_bound (z : Scalar) (r : Rat) (hr : 0≤r)
    (hz : Small z.val r) (n : Nat) :
    Small (weightedNomePower z n) (2*(2*r)*(4*r)^n) := by
  have h := LocalODE.small_scale (c := ((n+1:Nat):Rat)) Rat.natCast_nonneg
    (LocalODE.power_small z.val z.property r hr hz (n+1))
  apply h.mono
  have hn := lambertIndex_bound n
  have hp := Rat.pow_nonneg (n := n) (Rat.mul_nonneg (by decide : (0:Rat)≤2) hr)
  have hm := Rat.mul_le_mul_of_nonneg_right hn
    (Rat.pow_nonneg (a := 2*r) (n := n+1) (Rat.mul_nonneg (by decide) hr))
  rw [Rat.pow_succ] at hm
  have he : (4*r)^n=(2:Rat)^n*(2*r)^n := by
    rw [show 4*r=2*(2*r) by grind only,LocalODE.rational_mul_pow]
  rw [he,Rat.pow_succ]
  have hb := Rat.mul_nonneg (Rat.pow_nonneg (n := n) (by decide : (0:Rat)≤2)) hp
  have hc := Rat.mul_nonneg hb (Rat.mul_nonneg (by decide : (0:Rat)≤2) hr)
  grind only

def weightedNomePrefix (z : Scalar) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (weightedNomePower z) 0 N

theorem weightedNomePrefix_valid (z : Scalar) (N : Nat) : (weightedNomePrefix z N).Valid :=
  ScalarSeries.block_valid _ (weightedNomePower_valid z) 0 N

def weightedNomeSum (z : Scalar) (r : Rat) : ComplexRaw :=
  ScalarSeries.value (weightedNomePower z) (weightedNomePower_valid z) (2*r) (4*r)

theorem weightedNomeSum_valid (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) : (weightedNomeSum z r).Valid :=
  ScalarSeries.value_valid _ _ (2*r) (4*r) (Rat.mul_nonneg (by decide) hr)
    (Rat.mul_nonneg (by decide) hr) hlocal (weightedNomePower_bound z r hr hz)

theorem weightedNomeSum_close (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (N : Nat) :
    Small (sub (weightedNomeSum z r) (weightedNomePrefix z N)) (4*(2*r)*(4*r)^N) :=
  ScalarSeries.value_close _ _ (2*r) (4*r) (Rat.mul_nonneg (by decide) hr)
    (Rat.mul_nonneg (by decide) hr) hlocal (weightedNomePower_bound z r hr hz) N

theorem weightedNomePrefix_telescoping (z : Scalar) (N : Nat) :
    (mul (sub (ofQComplex QComplex.one) z.val) (weightedNomePrefix z N)).Equiv
      (sub (ScalarSeries.block (LocalODE.power z.val) 1 N)
        (scaleRat (N:Rat) (LocalODE.power z.val (N+1)))) := by
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  have h (n : Nat) :
      (1-Z)*ComplexRawQuotient.ofRaw (weightedNomePrefix z n) (weightedNomePrefix_valid z n)=
      ComplexRawQuotient.ofRaw (ScalarSeries.block (LocalODE.power z.val) 1 n)
        (ScalarSeries.block_valid _ (LocalODE.power_valid _ z.property) 1 n) -
        (n:ScalarAlgebra.Value)*Z^(n+1) := by
    induction n with
    | zero => change (1-Z)*0=0-0*Z^1; grind only
    | succ n ih =>
      simp only [weightedNomePrefix,ScalarSeries.block.eq_2,Nat.zero_add]
      change (1-Z)*(ComplexRawQuotient.ofRaw (weightedNomePrefix z n) (weightedNomePrefix_valid z n)+
        ComplexRawQuotient.scaleRat ((n+1:Nat):Rat)
          (ComplexRawQuotient.ofRaw (LocalODE.power z.val (n+1)) (LocalODE.power_valid _ z.property (n+1)))) =
        ComplexRawQuotient.ofRaw (ScalarSeries.block (LocalODE.power z.val) 1 n)
          (ScalarSeries.block_valid _ (LocalODE.power_valid _ z.property) 1 n)+
        ComplexRawQuotient.ofRaw (LocalODE.power z.val (1+n)) (LocalODE.power_valid _ z.property (1+n))-
        ((n+1:Nat):ScalarAlgebra.Value)*Z^(n+1+1)
      rw [ScalarAlgebra.scale_natural,ScalarAlgebra.ofRaw_power _ z.property,ScalarAlgebra.ofRaw_power _ z.property]
      rw [show 1+n=n+1 by omega]
      grind only
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) (weightedNomePrefix_valid z N))
    (hright := sub_valid (ScalarSeries.block_valid _ (LocalODE.power_valid _ z.property) 1 N)
      (scaleRat_valid (LocalODE.power_valid _ z.property (N+1))))
  change (1-Z)*ComplexRawQuotient.ofRaw (weightedNomePrefix z N) (weightedNomePrefix_valid z N)=
    ComplexRawQuotient.ofRaw (ScalarSeries.block (LocalODE.power z.val) 1 N)
      (ScalarSeries.block_valid _ (LocalODE.power_valid _ z.property) 1 N)-
      ComplexRawQuotient.scaleRat (N:Rat)
        (ComplexRawQuotient.ofRaw (LocalODE.power z.val (N+1)) (LocalODE.power_valid _ z.property (N+1)))
  rw [ScalarAlgebra.scale_natural,ScalarAlgebra.ofRaw_power _ z.property]
  exact h N

end ComputableAnalysis.ModularForms
