import ComputableAnalysis.ModularForms.LatticePartialFractionNome
import ComputableAnalysis.ModularForms.CMNomeDecay163

/-! A convergent Fourier formula for the actual lattice kernel wherever
the supplied nome has the checked geometric-series bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def latticeFourierCoefficient : Scalar :=
  ⟨neg (mul latticeImaginaryUnit.val latticeFrequency.val),
    neg_valid (mul_valid latticeImaginaryUnit.property latticeFrequency.property)⟩

def latticeFourierPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) : ComplexRaw :=
  mul latticeFourierCoefficient.val (cotangentNomePrefix (nome.eval z hz) N)

theorem latticeFourierPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (N : Nat) :
    (latticeFourierPrefix z hz N).Valid :=
  mul_valid latticeFourierCoefficient.property (cotangentNomePrefix_valid _ N)

theorem latticePartialFraction_fourier (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (hq : Small (nome.eval z hz).val r) :
    (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (mul latticeFourierCoefficient.val (cotangentNomeKernel (nome.eval z hz) r)) := by
  let p := pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)
  let k := upperNomeCotangentMap.eval z hz
  have hk := cotangentRationalMap_series_agreement (nome.eval z hz) r hr hlocal hq
    ((cotangentRationalMap_domain _).mpr (nome_upper_denominator_nonzero z hz))
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := p.property)
    (hright := neg_valid (mul_valid latticeImaginaryUnit.property (mul_valid latticeFrequency.property k.property)))
    (latticePartialFraction_nome_formula z hz)
  have he : p.val.Equiv (mul latticeFourierCoefficient.val k.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := p.property)
      (hright := mul_valid latticeFourierCoefficient.property k.property)
    let P := gridScalarValue p
    let K := gridScalarValue k
    let I := gridScalarValue latticeImaginaryUnit
    let A := gridScalarValue latticeFrequency
    change P= -(I*(A*K)) at hp
    change P= -(I*A)*K
    grind only
  exact equiv_trans p.property (mul_valid latticeFourierCoefficient.property k.property)
    (mul_valid latticeFourierCoefficient.property (cotangentNomeKernel_valid _ r hr hlocal hq)) he
    (mul_equiv latticeFourierCoefficient.property latticeFourierCoefficient.property k.property
      (cotangentNomeKernel_valid _ r hr hlocal hq)
      (equiv_refl _ latticeFourierCoefficient.property) hk)

theorem latticeFourierPrefix_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (hq : Small (nome.eval z hz).val r) (N : Nat) :
    Small (sub (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).val
      (latticeFourierPrefix z hz N))
      (16*(scalarBound latticeFourierCoefficient)*(2*r)^(N+1)) := by
  let p := pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)
  let k := cotangentNomeKernel (nome.eval z hz) r
  let b := cotangentNomePrefix (nome.eval z hz) N
  have vk := cotangentNomeKernel_valid _ r hr hlocal hq
  have vb := cotangentNomePrefix_valid (nome.eval z hz) N
  have ht := cotangentNomePrefix_close (nome.eval z hz) r hr hlocal hq N
  have hE : 0≤8*(2*r)^(N+1) := Rat.mul_nonneg (by decide +kernel)
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hr))
  have hs := Small.mul latticeFourierCoefficient.property (sub_valid vk vb)
    (Rat.le_of_lt (scalarBound_pos latticeFourierCoefficient)) hE
    (scalar_small latticeFourierCoefficient) ht
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := p.property)
    (hright := mul_valid latticeFourierCoefficient.property vk)
    (latticePartialFraction_fourier z hz r hr hlocal hq)
  have he : (mul latticeFourierCoefficient.val (sub k b)).Equiv
      (sub p.val (latticeFourierPrefix z hz N)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid latticeFourierCoefficient.property (sub_valid vk vb))
      (hright := sub_valid p.property (latticeFourierPrefix_valid z hz N))
    let C := gridScalarValue latticeFourierCoefficient
    let K := ComplexRawQuotient.ofRaw k vk
    let B := ComplexRawQuotient.ofRaw b vb
    let P := gridScalarValue p
    change P=C*K at hp
    change C*(K-B)=P-C*B
    rw [hp]
    grind only
  have hc : 2*scalarBound latticeFourierCoefficient*(8*(2*r)^(N+1))=
      16*scalarBound latticeFourierCoefficient*(2*r)^(N+1) := by grind only
  rw [hc] at hs
  exact Small.congr (mul_valid latticeFourierCoefficient.property (sub_valid vk vb))
    (sub_valid p.property (latticeFourierPrefix_valid z hz N)) he hs

theorem latticeFourierPrefix_cm163_close (N : Nat) :
    Small (sub (pairedGlobalOffPoleAssemblyMap.eval cmScalar163
      (pairedGlobalOffPole_upper_mem cmScalar163 cmPoint163_upper)).val
      (latticeFourierPrefix cmScalar163 cmPoint163_upper N))
      (16*scalarBound latticeFourierCoefficient*((1:Rat)/8388608)^(N+1)) := by
  have h := latticeFourierPrefix_close cmScalar163 cmPoint163_upper (1/16777216)
    (by decide +kernel) (by decide +kernel) nome_cm163_small_power N
  have he : (2:Rat)*(1/16777216)=(1:Rat)/8388608 := by decide +kernel
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
