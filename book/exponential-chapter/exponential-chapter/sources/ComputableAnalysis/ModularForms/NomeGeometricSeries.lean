import ComputableAnalysis.RiemannHilbert.GeometricSeries
import ComputableAnalysis.ModularForms.CMNomeDecay163

/-! Literal convergent geometric powers on a supplied represented nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def nomeGeometricPrefix (z : Scalar) (N : Nat) : ComplexRaw :=
  ScalarSeries.block (LocalODE.power z.val) 0 N

theorem nomeGeometricPrefix_valid (z : Scalar) (N : Nat) : (nomeGeometricPrefix z N).Valid :=
  ScalarSeries.block_valid _ (LocalODE.power_valid _ z.property) 0 N

private theorem geometricTerm_bound (z : Scalar) (r : Rat) (hr : 0≤r) (hz : Small z.val r) (n : Nat) :
    Small (LocalODE.power z.val n) (2*1*(2*r)^n) := by
  apply (LocalODE.power_small z.val z.property r hr hz n).mono
  have hp := Rat.pow_nonneg (n := n) (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hr)
  grind only

def nomeGeometricSum (z : Scalar) (r : Rat) : ComplexRaw :=
  ScalarSeries.value (LocalODE.power z.val) (LocalODE.power_valid _ z.property) 1 (2*r)

theorem nomeGeometricSum_valid (z : Scalar) (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (hz : Small z.val r) : (nomeGeometricSum z r).Valid :=
  ScalarSeries.value_valid _ _ 1 (2*r) (by decide) (Rat.mul_nonneg (by decide) hr) hlocal
    (geometricTerm_bound z r hr hz)

theorem nomeGeometricSum_close (z : Scalar) (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (hz : Small z.val r) (N : Nat) :
    Small (sub (nomeGeometricSum z r) (nomeGeometricPrefix z N)) (4*(2*r)^N) := by
  have h := ScalarSeries.value_close (LocalODE.power z.val) (LocalODE.power_valid _ z.property) 1 (2*r) (by decide) (Rat.mul_nonneg (by decide) hr) hlocal
    (geometricTerm_bound z r hr hz) N
  rw [show (4:Rat)*1=4 by decide +kernel] at h
  exact h

theorem nomeGeometricTail_shrinks (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) :
    ShrinksToZero (fun N => 4*(2*r)^N) := by
  have h := LocalODE.tail_bound_shrinks 1 (2*r) (by decide) (Rat.mul_nonneg (by decide) hr) hlocal
  simpa only [Rat.mul_one] using h

theorem nomeGeometricPrefix_telescoping (z : Scalar) (N : Nat) :
    (mul (sub (ofQComplex QComplex.one) z.val) (nomeGeometricPrefix z N)).Equiv
      (sub (ofQComplex QComplex.one) (LocalODE.power z.val N)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) (nomeGeometricPrefix_valid z N))
    (hright := sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ z.property N))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  have h (n : Nat) :
      (1-Z)*ComplexRawQuotient.ofRaw (nomeGeometricPrefix z n) (nomeGeometricPrefix_valid z n)=1-Z^n := by
    induction n with
    | zero => change (1-Z)*0=1-1; grind only
    | succ n ih =>
      simp only [nomeGeometricPrefix,ScalarSeries.block.eq_2,Nat.zero_add]
      change (1-Z)*(ComplexRawQuotient.ofRaw (nomeGeometricPrefix z n) (nomeGeometricPrefix_valid z n)+
        ComplexRawQuotient.ofRaw (LocalODE.power z.val n) (LocalODE.power_valid _ z.property n))=1-Z^(n+1)
      rw [ScalarAlgebra.ofRaw_power _ z.property n]
      grind only
  change (1-Z)*ComplexRawQuotient.ofRaw (nomeGeometricPrefix z N) (nomeGeometricPrefix_valid z N)=
    1-ComplexRawQuotient.ofRaw (LocalODE.power z.val N) (LocalODE.power_valid _ z.property N)
  rw [ScalarAlgebra.ofRaw_power _ z.property N]
  exact h N

end ComputableAnalysis.ModularForms
