import ComputableAnalysis.ModularForms.TauFiniteProductEvaluation
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws

/-! Quantitative bounds for the actual degree-24 Euler factors. -/
set_option maxHeartbeats 800000
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private theorem power_deviation_identity (x : Scalar) (n : Nat) :
    (sub (LocalODE.power (sub one x.val) (n+1)) one).Equiv
      (sub (sub (sub (LocalODE.power (sub one x.val) n) one) x.val)
        (mul (sub (LocalODE.power (sub one x.val) n) one) x.val)) := by
  have ho : one.Valid := ofQComplex_valid _
  have hw := sub_valid ho x.property
  have hp := LocalODE.power_valid _ hw n
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (LocalODE.power_valid _ hw _) ho)
    (hright := sub_valid (sub_valid (sub_valid hp ho) x.property)
      (mul_valid (sub_valid hp ho) x.property))
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let W := ComplexRawQuotient.ofRaw (sub one x.val) hw
  have hwEq : W=1-X := by
    change ComplexRawQuotient.ofRaw (add one (neg x.val)) _ = _
    rw [ComplexRawQuotient.ofRaw_add _ _ ho (neg_valid x.property),
      ComplexRawQuotient.ofRaw_neg _ x.property]
    rfl
  change ComplexRawQuotient.ofRaw (LocalODE.power (sub one x.val) (n+1)) (LocalODE.power_valid _ hw (n+1)) - 1 =
    (ComplexRawQuotient.ofRaw (LocalODE.power (sub one x.val) n) hp - 1) - X -
      (ComplexRawQuotient.ofRaw (LocalODE.power (sub one x.val) n) hp - 1)*X
  rw [ScalarAlgebra.ofRaw_power _ hw (n+1),ScalarAlgebra.ofRaw_power _ hw n]
  change W^(n+1)-1=(W^n-1)-X-(W^n-1)*X
  rw [hwEq]
  grind only

/-- A uniform linear deviation estimate for the first 24 powers of a small factor. -/
theorem eulerFactor_power_deviation_bound (x : Scalar) (s : Rat) (hs : 0≤s)
    (hsMax : s≤(1:Rat)/128) (hx : Small x.val s) (n : Nat) (hn : n≤24) :
    Small (sub (LocalODE.power (sub one x.val) n) one) (2*(n:Rat)*s) := by
  have ho : one.Valid := ofQComplex_valid _
  have hw := sub_valid ho x.property
  induction n with
  | zero =>
    have he : (sub one one).Equiv zero := add_neg_equiv one ho
    exact Small.congr (ofQComplex_valid _) (sub_valid ho ho) (equiv_symm he)
      (Small.zero (by change (0:Rat)≤2*0*s; rw [Rat.mul_zero,Rat.zero_mul]; exact Rat.le_refl))
  | succ n ih =>
    have hn24 : n≤24 := by omega
    have hdev := ih hn24
    have hB : 0≤2*(n:Rat)*s := Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) hs
    have hmul := Small.mul (sub_valid (LocalODE.power_valid _ hw n) ho) x.property hB hs hdev hx
    have hsum := SeriesLimitLaws.small_sub (SeriesLimitLaws.small_sub hdev hx) hmul
    have he := power_deviation_identity x n
    have hresult := Small.congr
      (sub_valid (sub_valid (sub_valid (LocalODE.power_valid _ hw n) ho) x.property)
        (mul_valid (sub_valid (LocalODE.power_valid _ hw n) ho) x.property))
      (sub_valid (LocalODE.power_valid _ hw (n+1)) ho) (equiv_symm he) hsum
    apply hresult.mono
    have hcast : (n:Rat)≤24 := Rat.natCast_le_natCast.mpr hn24
    rw [Rat.natCast_add,show ((1:Nat):Rat)=1 by rfl]
    have hcoef : 4*(n:Rat)*s≤1 := by
      have hh := Rat.mul_le_mul_of_nonneg_right hcast hs
      have hh4 := Rat.mul_le_mul_of_nonneg_left hh (show (0:Rat)≤4 by decide +kernel)
      have h96 := Rat.mul_le_mul_of_nonneg_left hsMax (show (0:Rat)≤96 by decide +kernel)
      have h96le : 96*s≤1 := Rat.le_trans h96 (by decide +kernel)
      grind only
    have hlast := Rat.mul_le_mul_of_nonneg_right hcoef hs
    grind only

theorem tauEulerGeometricPower_le_first (t : Rat) (ht : 0≤t) (ht1 : t≤1) (n : Nat) :
    t^(n+1)≤t := by
  induction n with
  | zero => simpa only [Nat.zero_add,Rat.pow_one] using (Rat.le_refl : t≤t)
  | succ n ih =>
    rw [Rat.pow_succ]
    have hpow := (Rat.pow_nonneg ht : 0≤t^(n+1))
    have hh : t^(n+1)*t≤t^(n+1) := by
      simpa only [Rat.mul_one] using Rat.mul_le_mul_of_nonneg_left ht1 hpow
    exact Rat.le_trans hh ih

/-- The Euler-factor powers have a geometric deviation estimate. -/
theorem tauEulerFactor_power_deviation_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/512) (hq : Small q.val r) (m n : Nat) (hn : n≤24) :
    Small (sub (LocalODE.power (sub one (LocalODE.power q.val (m+1))) n) one)
      (2*(n:Rat)*(2*r)^(m+1)) := by
  let x : Scalar := ⟨LocalODE.power q.val (m+1),LocalODE.power_valid _ q.property _⟩
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤2 by decide +kernel)
  have ht1 : 2*r≤1 := Rat.le_trans hmax (by decide +kernel)
  have hs : 0≤(2*r)^(m+1) := Rat.pow_nonneg ht
  have hsMax : (2*r)^(m+1)≤(1:Rat)/128 :=
    Rat.le_trans (tauEulerGeometricPower_le_first (2*r) ht ht1 m)
      (Rat.le_trans hmax (by decide +kernel))
  exact eulerFactor_power_deviation_bound x ((2*r)^(m+1)) hs hsMax
    (LocalODE.power_small _ q.property r hr hq (m+1)) n hn

/-- The literal degree-24 Euler factor is geometrically close to one. -/
theorem tauEulerFactor_deviation_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/512) (hq : Small q.val r) (m : Nat) :
    Small (sub (LocalODE.power (sub one (LocalODE.power q.val (m+1))) 24) one)
      (48*(2*r)^(m+1)) := by
  have h := tauEulerFactor_power_deviation_bound q r hr hrMax hq m 24 (by decide +kernel)
  rw [show (2:Rat)*((24:Nat):Rat)=48 by decide +kernel] at h
  exact h

end ComputableAnalysis.ModularForms
