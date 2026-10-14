import ComputableAnalysis.ModularForms.TauEulerFactorRemainder

/-! Exact analytic power-map remainder decomposition and quantitative bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The actual power-map remainder splits into an outer monomial remainder
and the actual base-map remainder multiplied by the outer slope. -/
theorem tauMapPower_remainder_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a z : Scalar) (ha : f.domain a) (hz : f.domain z) (n : Nat) :
    (DomainFunctions.remainder (tauMapPower f (n+1)) a ha
      ((tauMapPower_holomorphic f hf (n+1)).derivative a ha) z hz).Equiv
      (add (LocalODE.monomialRemainder (f.eval a ha).val (f.eval z hz).val (n+1))
        (mul (LocalODE.monomialSlope (f.eval a ha).val (n+1))
          (DomainFunctions.remainder f a ha (hf.derivative a ha) z hz))) := by
  let A := f.eval a ha
  let Z := f.eval z hz
  let D := hf.derivative a ha
  let DP := (tauMapPower_holomorphic f hf (n+1)).derivative a ha
  let S := LocalODE.monomialSlope A.val (n+1)
  let M := LocalODE.monomialRemainder A.val Z.val (n+1)
  have hS := LocalODE.monomialSlope_valid A.val A.property (n+1)
  have hM := LocalODE.monomialRemainder_valid A.val Z.val A.property Z.property (n+1)
  have hp := LocalODE.power_valid A.val A.property n
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := DP.property)
    (hright := scaleRat_valid (mul_valid hp D.property)) (tauMapPower_derivative f hf a ha n)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := hS)
    (hright := scaleRat_valid hp) (LocalODE.monomialSlope_formula A.val A.property n)
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let dp := ComplexRawQuotient.ofRaw DP.val DP.property
  let s := ComplexRawQuotient.ofRaw S hS
  let p := ComplexRawQuotient.ofRaw (LocalODE.power A.val n) hp
  change dp=ComplexRawQuotient.scaleRat ((n+1:Nat):Rat) (p*d) at hd
  change s=ComplexRawQuotient.scaleRat ((n+1:Nat):Rat) p at hs
  rw [ComplexRawQuotient.scaleRat_mul,←hs] at hd
  have hm := LocalODE.monomial_decomposition A.val Z.val A.property Z.property (n+1)
  let ap := ComplexRawQuotient.ofRaw (LocalODE.power A.val (n+1)) (LocalODE.power_valid _ A.property _)
  let zp := ComplexRawQuotient.ofRaw (LocalODE.power Z.val (n+1)) (LocalODE.power_valid _ Z.property _)
  let av := ComplexRawQuotient.ofRaw A.val A.property
  let zv := ComplexRawQuotient.ofRaw Z.val Z.property
  let m := ComplexRawQuotient.ofRaw M hM
  let h := ComplexRawQuotient.ofRaw (sub z.val a.val) (sub_valid z.property a.property)
  change zp=ap+s*(zv-av)+m at hm
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid (tauMapPower f (n+1)) a ha DP z hz)
    (hright := add_valid hM (mul_valid hS (DomainFunctions.remainder_valid f a ha D z hz)))
  change (zp-ap)-dp*h=m+s*((zv-av)-d*h)
  rw [hm,hd]
  grind only

/-- A power-map analytic remainder bound from actual base values,
base variation and base remainder evidence. -/
theorem tauMapPower_quadratic_remainder_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a z : Scalar) (ha : f.domain a) (hz : f.domain z) (R L E : Rat)
    (hR : 0≤R) (hL : 0≤L) (hE : 0≤E)
    (haR : Small (f.eval a ha).val R) (hzR : Small (f.eval z hz).val R)
    (hvariation : Small (sub (f.eval z hz).val (f.eval a ha).val) L)
    (hbase : Small (DomainFunctions.remainder f a ha (hf.derivative a ha) z hz) E) (n : Nat) :
    Small (DomainFunctions.remainder (tauMapPower f (n+2)) a ha
      ((tauMapPower_holomorphic f hf (n+2)).derivative a ha) z hz)
      (2*((n+2:Nat):Rat)*((n+1:Nat):Rat)*(2*R)^n*L^2+
        2*(((n+2:Nat):Rat)*(2*R)^(n+1))*E) := by
  let A := f.eval a ha
  let Z := f.eval z hz
  have hs := LocalODE.monomialSlope_small A.val A.property R hR haR (n+1)
  have hm := LocalODE.monomialRemainder_bound A.val Z.val A.property Z.property R L
    hR hL haR hzR hvariation n
  have hb : 0≤((n+2:Nat):Rat)*(2*R)^(n+1) := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hR))
  have hp := Small.mul (LocalODE.monomialSlope_valid A.val A.property (n+2))
    (DomainFunctions.remainder_valid f a ha (hf.derivative a ha) z hz) hb hE hs hbase
  exact Small.congr
    (add_valid (LocalODE.monomialRemainder_valid A.val Z.val A.property Z.property (n+2))
      (mul_valid (LocalODE.monomialSlope_valid A.val A.property (n+2))
        (DomainFunctions.remainder_valid f a ha (hf.derivative a ha) z hz)))
    (DomainFunctions.remainder_valid (tauMapPower f (n+2)) a ha
      ((tauMapPower_holomorphic f hf (n+2)).derivative a ha) z hz)
    (equiv_symm (tauMapPower_remainder_identity f hf a z ha hz (n+1)))
    (LocalODE.small_add hm hp)

end ComputableAnalysis.ModularForms
