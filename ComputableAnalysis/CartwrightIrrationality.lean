import ComputableAnalysis.CartwrightMomentAlgebra
import ComputableAnalysis.CartwrightMomentBounds

/-! Arithmetic after the calculus middle. The analytic route supplies the
moment laws; all denominator clearing and the final integer contradiction
are shared. No completed-real or Mathlib declaration occurs in this module. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse CartwrightArithmetic RationalSampleLimits FiniteRationalPowers IntervalSelections

private def polyBounds (K : Rat) : Nat → Rat × Rat
  | 0 => (1,1)
  | n+1 => let p:=polyBounds K n
           (p.2,(2*(n:Rat)+3)*p.2+K*p.1)

private theorem polyBounds_nonneg {K : Rat} (hK : 0≤K) (n : Nat) :
    0≤(polyBounds K n).1 ∧ 0≤(polyBounds K n).2 := by
  induction n with
  | zero => change 0≤(1:Rat) ∧ 0≤(1:Rat);exact ⟨by decide,by decide⟩
  | succ n ih =>
    have hc : 0≤2*(n:Rat)+3 := by have h:=Rat.natCast_nonneg (a:=n);grind
    exact ⟨ih.2,Rat.add_nonneg (Rat.mul_nonneg hc ih.2) (Rat.mul_nonneg hK ih.1)⟩

private theorem polynomial_pair_bounded (z : Seq) {K : Rat} (hK : 0≤K) (hz : Bounded z K) (n : Nat) :
    Bounded (fun q=>(polynomialPair (z q) n).1) (polyBounds K n).1 ∧
    Bounded (fun q=>(polynomialPair (z q) n).2) (polyBounds K n).2 := by
  induction n with
  | zero => exact ⟨fun (_:Nat)=>by change qabs (1:Rat)≤1;decide +kernel,fun (_:Nat)=>by change qabs (1:Rat)≤1;decide +kernel⟩
  | succ n ih =>
    have hc : 0≤2*(n:Rat)+3 := by have h:=Rat.natCast_nonneg (a:=n);grind
    have hC : Bounded (fun (_:Nat)=>2*(n:Rat)+3) (2*(n:Rat)+3) := fun (_:Nat)=>by
      rw [qabs_eq_self_of_nonneg hc];exact Rat.le_refl
    exact ⟨ih.2,bounded_sub (bounded_mul hc hC ih.2) (bounded_mul hK hz ih.1)⟩

private theorem polynomial_pair_close {x y : Seq} (h : Close x y) {K L : Rat}
    (hK : 0≤K) (hL : 0≤L) (hx : Bounded x K) (hy : Bounded y L) (n : Nat) :
    Close (fun q=>(polynomialPair (x q) n).1) (fun q=>(polynomialPair (y q) n).1) ∧
    Close (fun q=>(polynomialPair (x q) n).2) (fun q=>(polynomialPair (y q) n).2) := by
  induction n with
  | zero => exact ⟨close_refl (fun (_:Nat)=>1),close_refl (fun (_:Nat)=>1)⟩
  | succ n ih =>
    have h1:=close_scale (2*(n:Rat)+3) ih.2
    have h2:=close_mul h ih.1 hK (polyBounds_nonneg hL n).1 hx (polynomial_pair_bounded y hL hy n).1
    exact ⟨ih.2,close_sub h1 h2⟩

theorem polynomial_close {x y : Seq} (h : Close x y) {K L : Rat}
    (hK : 0≤K) (hL : 0≤L) (hx : Bounded x K) (hy : Bounded y L) (n : Nat) :
    Close (fun q=>polynomialValue (x q) n) (fun q=>polynomialValue (y q) n) :=
  (polynomial_pair_close h hK hL hx hy n).1

private theorem momentSample_bounded (n : Nat) : Bounded (momentSample n) 1 := fun q=>by
  have h:=momentSample_unit n q
  rw [qabs_eq_self_of_nonneg h.1]
  exact h.2

/-- Raising the hypothetical rational equation is finite polynomial algebra;
there is no rational representative selected for the frequency itself. -/
private theorem characteristic_power (a b : Nat) (hb : 0<b)
    (h : Close (fun q=>frequencySample q*frequencySample q) (fun (_:Nat)=>(a:Rat)/(b:Rat))) (n : Nat) :
    Close (fun q=>(b:Rat)^n*scaledSample n q)
      (fun q=>frequencySample q*(a:Rat)^n*momentSample n q) := by
  have hb0:=Rat.natCast_nonneg (a:=b)
  have ha0:=Rat.natCast_nonneg (a:=a)
  have hbne : (b:Rat)≠0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hb)
  have hc:=Rat.mul_inv_cancel (b:Rat) hbne
  have he : (b:Rat)*((a:Rat)/(b:Rat))=(a:Rat) := by
    rw [Rat.div_def]
    grind only
  have hbase:=close_scale (b:Rat) h
  rw [he] at hbase
  have hbb : Bounded (fun (_:Nat)=>(b:Rat)) (b:Rat) := fun (_:Nat)=>by rw [qabs_eq_self_of_nonneg hb0];exact Rat.le_refl
  have haa : Bounded (fun (_:Nat)=>(a:Rat)) (a:Rat) := fun (_:Nat)=>by rw [qabs_eq_self_of_nonneg ha0];exact Rat.le_refl
  have hpow:=close_power hbase (Rat.mul_nonneg hb0 (by decide : (0:Rat)≤4)) ha0
    (bounded_mul hb0 hbb frequencySquare_bound) haa n
  have hfactor : Bounded (fun q=>frequencySample q*momentSample n q) 2 := by
    have hmul:=bounded_mul (by decide : (0:Rat)≤2) frequency_bound (momentSample_bounded n)
    simpa only [Rat.mul_one] using hmul
  have hh:=close_bounded_mul hpow (by decide : (0:Rat)≤2) hfactor
  have hleft : (fun q=>(frequencySample q*momentSample n q)*((b:Rat)*(frequencySample q*frequencySample q))^n)=
      (fun q=>(b:Rat)^n*scaledSample n q) := by
    funext q
    unfold scaledSample
    rw [show 2*n+1=(n+n)+1 by omega,Rat.pow_succ,pow_add,mul_pow,mul_pow]
    grind only
  have hright : (fun q=>(frequencySample q*momentSample n q)*(a:Rat)^n)=
      (fun q=>frequencySample q*(a:Rat)^n*momentSample n q) := by funext q;grind
  rw [hleft,hright] at hh
  exact hh

/-- The moment evaluation gives the denominator-cleared integer as a small
positive real computation, expressed entirely through rational samples. -/
theorem integer_close (laws : MomentLaws) (a b : Nat) (hb : 0<b)
    (hyp : Close (fun q=>frequencySample q*frequencySample q) (fun (_:Nat)=>(a:Rat)/(b:Rat))) (n : Nat) :
    Close (fun (_:Nat)=>(integerValue (a:Int) (b:Int) n:Rat)*normalizer n)
      (fun q=>frequencySample q*(a:Rat)^n*momentSample n q) := by
  let z : Rat := (a:Rat)/(b:Rat)
  have hp:=polynomial_close hyp (by decide : (0:Rat)≤4) (qabs_nonneg z)
    frequencySquare_bound (bounded_const z) n
  have hp':=close_scale ((b:Rat)^n*normalizer n) hp
  have he:=close_scale ((b:Rat)^n) (evaluation_close laws n)
  have hmid : (fun q=>(b:Rat)^n*endpointSample n q)=
      (fun q=>((b:Rat)^n*normalizer n)*polynomialValue (frequencySample q*frequencySample q) n) := by
    funext q;unfold endpointSample;grind
  rw [hmid] at he
  have hjoined:=close_trans he hp'
  have hbne : ((b:Int):Rat)≠0 := by
    rw [Rat.intCast_natCast]
    exact Rat.ne_of_gt ((Rat.natCast_pos).2 hb)
  have hd:=denominator_cleared (a:Int) (b:Int) hbne n
  simp only [Rat.intCast_natCast] at hd
  have hconst : (fun (_:Nat)=>((b:Rat)^n*normalizer n)*polynomialValue z n)=
      (fun (_:Nat)=>(integerValue (a:Int) (b:Int) n:Rat)*normalizer n) := by
    funext q
    rw [hd]
    dsimp [z]
    grind
  rw [hconst] at hjoined
  exact close_trans (close_symm hjoined) (characteristic_power a b hb hyp n)

/-- This is the only information passed to the purely integer consumer. -/
theorem integer_bounds (laws : MomentLaws) (a b : Nat) (ha : 0<a) (hb : 0<b)
    (hyp : Close (fun q=>frequencySample q*frequencySample q) (fun (_:Nat)=>(a:Rat)/(b:Rat))) (n : Nat) :
    0<integerValue (a:Int) (b:Int) n ∧
    integerValue (a:Int) (b:Int) n*((2^n*factorial n:Nat):Int)≤((2*a^n:Nat):Int) := by
  have hclose:=integer_close laws a b hb hyp n
  have haR : 0<(a:Rat) := (Rat.natCast_pos).2 ha
  have hpow : 0<(a:Rat)^n := Rat.pow_pos haR
  have hpow0:=Rat.le_of_lt hpow
  have hlow : (a:Rat)^n*lowerBound n≤(integerValue (a:Int) (b:Int) n:Rat)*normalizer n := by
    apply le_const_of_close hclose
    refine ⟨6,fun q hq => ?_⟩
    have hp:=frequencySample_bounds q
    have hf0 : 0≤frequencySample q := by grind
    have hm:=momentSample_lower n hq
    have hL:=Rat.mul_le_mul_of_nonneg_left hm (Rat.mul_nonneg hf0 hpow0)
    have hF:=Rat.mul_le_mul_of_nonneg_right hp.1
      (Rat.mul_nonneg hpow0 (Rat.le_of_lt (lowerBound_pos n)))
    grind only
  have hupp : (integerValue (a:Int) (b:Int) n:Rat)*normalizer n≤2*(a:Rat)^n := by
    apply const_le_of_close hclose
    refine ⟨0,fun q _ => ?_⟩
    have hp:=frequencySample_bounds q
    have hf0 : 0≤frequencySample q := by grind
    have hm:=momentSample_unit n q
    have hM:=Rat.mul_le_mul_of_nonneg_left hm.2 (Rat.mul_nonneg hf0 hpow0)
    have hF:=Rat.mul_le_mul_of_nonneg_right hp.2 hpow0
    grind only
  have hpositive:=Rat.mul_pos hpow (lowerBound_pos n)
  have hnorm:=normalizer_pos n
  have hk : (0:Rat)<(integerValue (a:Int) (b:Int) n:Rat) := by
    by_cases h: (0:Rat)<(integerValue (a:Int) (b:Int) n:Rat)
    · exact h
    · have hm:=Rat.mul_le_mul_of_nonneg_right
        (show (integerValue (a:Int) (b:Int) n:Rat)≤0 by grind)
        (Rat.le_of_lt hnorm)
      grind only
  constructor
  · exact_mod_cast hk
  · unfold normalizer at hupp
    exact_mod_cast hupp

/-- The positive integer contradiction applies to every hypothetical rational
squared frequency. No notion of integrability is used. -/
theorem frequency_not_rational_close (laws : MomentLaws) (r : Rat)
    (hyp : Close (fun q=>frequencySample q*frequencySample q) (fun (_:Nat)=>r)) : False := by
  have hr : 1≤r := by
    apply le_const_of_close (close_symm hyp)
    refine ⟨0,fun q _ => ?_⟩
    have h:=frequencySample_bounds q
    have h0 : 0≤frequencySample q := by grind
    have hm:=Rat.mul_le_mul_of_nonneg_right h.1 h0
    grind only
  have hr0 : 0<r := by grind
  have hnum:=rat_num_pos_of_pos hr0
  let a:=r.num.natAbs
  let b:=r.den
  have ha : 0<a := by dsimp [a];omega
  have hb : 0<b := Nat.pos_of_ne_zero r.den_nz
  have hnumcast : (a:Rat)=(r.num:Rat) := by
    have hc:=congrArg (fun z:Int=>(z:Rat)) (Int.natAbs_of_nonneg (show 0≤r.num by omega))
    simpa only [Rat.intCast_natCast] using hc
  have hrepr : r=(a:Rat)/(b:Rat) := by
    have hd:=rat_den_mul_self r
    change (b:Rat)*r=(r.num:Rat) at hd
    rw [←hnumcast] at hd
    have hc:=Rat.mul_inv_cancel (b:Rat) (Rat.ne_of_gt ((Rat.natCast_pos).2 hb))
    rw [Rat.div_def]
    grind only
  rw [hrepr] at hyp
  exact no_positive_small_sequence a ha (integerValue (a:Int) (b:Int))
    (fun n=>(integer_bounds laws a b ha hb hyp n).1)
    (fun n=>(integer_bounds laws a b ha hb hyp n).2)

/-- A closed theorem about the original geometric pi algorithm, once an
analytic route supplies the moment laws. Each exported alternative below
will supply those laws rather than leave this as a hypothesis. -/
theorem piSquared_of_laws (laws : MomentLaws) : PiSquaredStatement := by
  intro r hyp
  have hv:=RealRaw.mul_valid CosinePrimitive.pi_valid CosinePrimitive.pi_valid
  have hp (q : Nat) : InBox (piCircleArea.compute q).lo (CosinePrimitive.pi.compute q) := by
    rw [CosinePrimitive.pi_compute]
    exact ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ CauchyPi.piCircleArea_valid q⟩
  have hc:=close_of_equiv hv (RealRaw.ofRat_valid r)
    (fun q=>(piCircleArea.compute q).lo*(piCircleArea.compute q).lo) (fun (_:Nat)=>r)
    (fun q=>mul_mem (hp q) (hp q)) (ClockTrigonometry.rat_mem r) hyp
  have hs:=close_scale ((1:Rat)/4) hc
  have hleft : (fun q=>(1:Rat)/4*((piCircleArea.compute q).lo*(piCircleArea.compute q).lo))=
      (fun q=>frequencySample q*frequencySample q) := by
    funext q;unfold frequencySample;simp only [Rat.div_def];grind only
  have hright : (fun (_:Nat)=>(1:Rat)/4*r)=(fun (_:Nat)=>r/4) := by
    funext q;simp only [Rat.div_def];grind only
  rw [hleft,hright] at hs
  exact frequency_not_rational_close laws (r/4) hs

end ComputableAnalysis.CartwrightMoments
