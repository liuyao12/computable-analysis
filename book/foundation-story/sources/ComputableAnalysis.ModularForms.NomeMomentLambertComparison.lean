import ComputableAnalysis.ModularForms.LambertRectangleBounds

/-! Exact comparison of the constructed outer nome moments and weighted Lambert sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem small_triangle (F p q : ComplexRaw) (hF : F.Valid) (hp : p.Valid) (hq : q.Valid)
    (a b : Rat) (h1 : Small (sub F p) a) (h2 : Small (sub p q) b) :
    Small (sub F q) (a+b) := by
  have he : (add (sub F p) (sub p q)).Equiv (sub F q) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid hF hp) (sub_valid hp hq)) (hright := sub_valid hF hq)
    change (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)+
      (ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq)=
      ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw q hq
    grind only
  exact Small.congr (add_valid (sub_valid hF hp) (sub_valid hp hq))
    (sub_valid hF hq) he (LocalODE.small_add h1 h2)

private theorem small_reverse (p q : ComplexRaw) (hp : p.Valid) (hq : q.Valid)
    (B : Rat) (h : Small (sub p q) B) : Small (sub q p) B := by
  have he : (neg (sub p q)).Equiv (sub q p) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid hp hq)) (hright := sub_valid hq hp)
    change -(ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq)=
      ComplexRawQuotient.ofRaw q hq-ComplexRawQuotient.ofRaw p hp
    grind only
  exact Small.congr (neg_valid (sub_valid hp hq)) (sub_valid hq hp) he (SeriesLimitLaws.small_neg h)

/-- The actual Lambert value approximates the actual finite outer moment prefix. -/
theorem weightedLambertSum_close_nomeMomentOuterPrefix (z : Scalar) (r : Rat) (k : Nat)
    (hr : 0≤r) (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) (N : Nat) :
    Small (sub (weightedLambertSum z r k hr (nomeMomentGuard_lambertLocal r k hr hlocal) hz)
      (ScalarSeries.block (nomeMomentOuterTerm z r k) 0 N)) (4*(8*r*(4*r)^N)) := by
  let G := weightedLambertSum z r k hr (nomeMomentGuard_lambertLocal r k hr hlocal) hz
  let p := ScalarSeries.block (nomeMomentOuterTerm z r k) 0 N
  let B := 4*(8*r*(4*r)^N)
  let ew := fun M : Nat => 4*(8*r)*(weightedLambertRatio r k)^M
  let em := fun M : Nat => (N:Rat)*(8*r*(4*r*(2:Rat)^k)^M)
  have vG : G.Valid := weightedLambertSum_valid z r k hr
    (nomeMomentGuard_lambertLocal r k hr hlocal) hz (nomeMomentGuard_lambertRatio r k hr hlocal)
  have vp : p.Valid := ScalarSeries.block_valid _ (nomeMomentOuterTerm_valid z r k hr hlocal hz) 0 N
  have he := RepresentedCauchySum.sum_shrinks ew em
    (weightedLambertSum_tail_shrinks r k hr (nomeMomentGuard_lambertRatio r k hr hlocal))
    (nomeMomentRectangleTail_shrinks r k N hr hlocal)
  apply SeriesLimitLaws.small_closed (sub G p) B (fun M => ew M+em M) he
  intro M
  let w := ScalarSeries.block (weightedLambertTerm z r k) 0 M
  let c := ScalarSeries.block (weightedLambertRectangleTerm z k N) 0 M
  let d := ScalarSeries.block (fun n => polynomialNomeMomentPrefix (nomePowerScalar z n) k M) 0 N
  have vw : w.Valid := ScalarSeries.block_valid _
    (weightedLambertTerm_valid z r k hr (nomeMomentGuard_lambertLocal r k hr hlocal) hz) 0 M
  have vc : c.Valid := ScalarSeries.block_valid _ (weightedLambertRectangleTerm_valid z k N) 0 M
  have vd : d.Valid := ScalarSeries.block_valid _ (fun n => polynomialNomeMomentPrefix_valid _ k M) 0 N
  have h1 : Small (sub G w) (ew M) := weightedLambertSum_close z r k hr
    (nomeMomentGuard_lambertLocal r k hr hlocal) hz (nomeMomentGuard_lambertRatio r k hr hlocal) M
  have h2 : Small (sub w c) B := weightedLambertPrefix_close_rectangle z r k hr hlocal hz N M
  have h3 : Small (sub p d) (em M) := nomeMomentOuterPrefix_close_rectangle z r k hr hlocal hz N M
  have hdc : d.Equiv c := polynomialNomeMomentPrefix_rectangle z k N M
  have hcp : Small (sub c p) (em M) := Small.congr (sub_valid vd vp) (sub_valid vc vp)
    (FunctionTheory.sub_congr hdc (equiv_refl p vp)) (small_reverse p d vp vd _ h3)
  have h4 := small_triangle G w c vG vw vc _ _ h1 h2
  have h5 := small_triangle G c p vG vc vp _ _ h4 hcp
  have horder : (ew M+B)+em M=B+(ew M+em M) := by grind only
  rw [horder] at h5
  exact h5

/-- The constructed outer moment sum equals the actual weighted Lambert sum.
Both cutoffs are removed using their explicit shrinking errors. -/
theorem nomeMomentOuterSum_eq_weightedLambertSum (z : Scalar) (r : Rat) (k : Nat)
    (hr : 0≤r) (hlocal : 4*r*(2:Rat)^k≤(1:Rat)/2) (hz : Small z.val r) :
    (nomeMomentOuterSum z r k hr hlocal hz).Equiv
      (weightedLambertSum z r k hr (nomeMomentGuard_lambertLocal r k hr hlocal) hz) := by
  let F := nomeMomentOuterSum z r k hr hlocal hz
  let G := weightedLambertSum z r k hr (nomeMomentGuard_lambertLocal r k hr hlocal) hz
  have vF : F.Valid := nomeMomentOuterSum_valid z r k hr hlocal hz
  have vG : G.Valid := weightedLambertSum_valid z r k hr
    (nomeMomentGuard_lambertLocal r k hr hlocal) hz (nomeMomentGuard_lambertRatio r k hr hlocal)
  have hB : ShrinksToZero (fun N => 4*(8*r*(4*r)^N)) := by
    have h := LocalODE.tail_bound_shrinks (8*r) (4*r) (Rat.mul_nonneg (by decide) hr)
      (Rat.mul_nonneg (by decide) hr) (nomeMomentGuard_lambertLocal r k hr hlocal)
    have he : (fun N : Nat => 4*(8*r)*(4*r)^N)=(fun N : Nat => 4*(8*r*(4*r)^N)) := by
      funext N
      grind only
    rw [he] at h
    exact h
  have he := RepresentedCauchySum.sum_shrinks _ _ (nomeMomentOuterSum_tail_shrinks r k hr hlocal) hB
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed (sub F G) 0
    (fun N => 4*(4*r)*(2*r)^N+4*(8*r*(4*r)^N)) he
  intro N
  let p := ScalarSeries.block (nomeMomentOuterTerm z r k) 0 N
  have vp : p.Valid := ScalarSeries.block_valid _ (nomeMomentOuterTerm_valid z r k hr hlocal hz) 0 N
  have h1 := nomeMomentOuterSum_close z r k hr hlocal hz N
  have h2 := weightedLambertSum_close_nomeMomentOuterPrefix z r k hr hlocal hz N
  have h := small_triangle F p G vF vp vG _ _ h1 (small_reverse G p vG vp _ h2)
  simpa only [Rat.zero_add] using h

end ComputableAnalysis.ModularForms
