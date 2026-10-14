import ComputableAnalysis.ModularForms.LatticeDiscriminantNormalizedFourier

/-! Certified leading terms of the actual weighted Lambert series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem rational_one_power (k : Nat) : (1:Rat)^k=1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Rat.pow_succ,ih,Rat.mul_one]

/-- The first actual Lambert factor differs from its nome by a quadratic error. -/
theorem nomeLambertPower_zero_linear_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hq : Small q.val r) :
    Small (sub (nomeLambertPower q r 0) q.val) (32*r*r) := by
  let l : Scalar := ⟨nomeLambertPower q r 0,nomeLambertPower_valid q r hr hlocal hq 0⟩
  have hl : Small l.val (16*r) := by
    have h := nomeLambertPower_bound q r hr hlocal hq 0
    rw [Rat.pow_succ,Rat.pow_zero] at h
    have he : 8*(1*(2*r))=16*r := by grind only
    rw [he] at h
    exact h
  have hb := Small.mul q.property l.property hr (Rat.mul_nonneg (by decide +kernel) hr) hq hl
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ q.property 1)) l.property)
    (hright := LocalODE.power_valid _ q.property 1)
    (nomeLambertPower_multiplication q r hr hlocal hq 0)
  have he : (mul q.val l.val).Equiv (sub l.val q.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid q.property l.property) (hright := sub_valid l.property q.property)
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    let L := ComplexRawQuotient.ofRaw l.val l.property
    change (1-ComplexRawQuotient.ofRaw (LocalODE.power q.val 1) (LocalODE.power_valid _ q.property 1))*L=
      ComplexRawQuotient.ofRaw (LocalODE.power q.val 1) (LocalODE.power_valid _ q.property 1) at hi
    rw [ScalarAlgebra.ofRaw_power _ q.property] at hi
    change (1-Q^1)*L=Q^1 at hi
    have hp : Q^1=Q := by grind only
    rw [hp] at hi
    change Q*L=L-Q
    generalize Q=X,L=Y at hi ⊢
    grind only
  have h := Small.congr (mul_valid q.property l.property) (sub_valid l.property q.property) he hb
  rw [show 2*r*(16*r)=32*r*r by grind only] at h
  exact h

/-- Every constructed weighted Lambert sum begins with its actual nome,
with a quantitative quadratic remainder. -/
theorem weightedLambertSum_linear_bound (q : Scalar) (r : Rat) (k : Nat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hq : Small q.val r)
    (hseries : weightedLambertRatio r k≤(1:Rat)/2) :
    Small (sub (weightedLambertSum q r k hr hlocal hq) q.val)
      ((64*(2:Rat)^k+32)*r*r) := by
  let w : Scalar := ⟨weightedLambertSum q r k hr hlocal hq,weightedLambertSum_valid q r k hr hlocal hq hseries⟩
  let l : Scalar := ⟨nomeLambertPower q r 0,nomeLambertPower_valid q r hr hlocal hq 0⟩
  let p : Scalar := ⟨ScalarSeries.block (weightedLambertTerm q r k) 0 1,
    ScalarSeries.block_valid _ (weightedLambertTerm_valid q r k hr hlocal hq) 0 1⟩
  have hp : p.val.Equiv l.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := p.property) (hright := l.property)
    rw [ScalarSeries.prefix_image _ (weightedLambertTerm_valid q r k hr hlocal hq)]
    change (0+ComplexRawQuotient.scaleRat (((1:Nat):Rat)^k) (ComplexRawQuotient.ofRaw l.val l.property))=
      ComplexRawQuotient.ofRaw l.val l.property
    rw [show ((1:Nat):Rat)=1 by decide +kernel,rational_one_power,ComplexRawQuotient.scaleRat_one]
    grind only
  have ht := weightedLambertSum_close q r k hr hlocal hq hseries 1
  have hwl := Small.congr (sub_valid w.property p.property) (sub_valid w.property l.property)
    (FunctionTheory.sub_congr (equiv_refl w.val w.property) hp) ht
  have hsum := LocalODE.small_add hwl (nomeLambertPower_zero_linear_bound q r hr hlocal hq)
  have he : (add (sub w.val l.val) (sub l.val q.val)).Equiv (sub w.val q.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid w.property l.property) (sub_valid l.property q.property))
      (hright := sub_valid w.property q.property)
    let W := ComplexRawQuotient.ofRaw w.val w.property
    let L := ComplexRawQuotient.ofRaw l.val l.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change (W-L)+(L-Q)=W-Q
    grind only
  have h := Small.congr (add_valid (sub_valid w.property l.property) (sub_valid l.property q.property))
    (sub_valid w.property q.property) he hsum
  have hrate : 4*(8*r)*(weightedLambertRatio r k)^1+32*r*r=(64*(2:Rat)^k+32)*r*r := by
    unfold weightedLambertRatio
    rw [Rat.pow_succ,Rat.pow_zero]
    grind only
  rw [hrate] at h
  exact h

end ComputableAnalysis.ModularForms
