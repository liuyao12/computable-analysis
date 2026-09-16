import ComputableAnalysis.CartwrightEvaluation

/-! The arithmetic conclusion consumes the evaluated moments and their independent
positive bounds. No rationality or moment-evaluation assumption remains in the
closed route declarations. -/
namespace ComputableAnalysis.CartwrightIrrationality
open CartwrightArithmetic CartwrightEvaluation CartwrightMomentRecurrence
open CartwrightIntegrationByParts CartwrightMoments CartwrightClockBounds
open RationalErrorCalculus IntervalSelections

private theorem mul_pow (a b : Rat) (n : Nat) : (a*b)^n=a^n*b^n := by
  induction n with
  | zero => simp only [Rat.pow_zero,Rat.one_mul]
  | succ n ih => rw [Rat.pow_succ,ih,Rat.pow_succ,Rat.pow_succ];grind

private theorem polynomial_near {x : Sequence} {r : Rat} (hx : Bounded x)
    (h : Near x (fun _=>r)) (n : Nat) :
    Near (fun k=>(polynomialPair (x k) n).1) (fun _=>(polynomialPair r n).1) ∧
    Near (fun k=>(polynomialPair (x k) n).2) (fun _=>(polynomialPair r n).2) := by
  induction n with
  | zero => exact ⟨Near.refl _,Near.refl _⟩
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    exact Near.sub (Near.scale ih.2 (2*(n:Rat)+3))
      (Near.mul hx (Bounded.constant _) h ih.1)

private theorem positive_nat_ratio {r : Rat} (hr : 0<r) :
    ∃ a b : Nat, 0<a ∧ 0<b ∧ r=(a:Rat)/(b:Rat) := by
  have hnum := rat_num_pos_of_pos hr
  have hden : 0<r.den := by have h:=r.den_nz;omega
  refine ⟨r.num.natAbs,r.den,?_,hden,?_⟩
  · have h:=Int.natAbs_of_nonneg (show 0≤r.num by omega)
    omega
  · have he := rat_den_mul_self r
    have hnum' : ((r.num.natAbs:Nat):Rat)=(r.num:Rat) := by
      have h:=Int.natAbs_of_nonneg (show 0≤r.num by omega)
      exact_mod_cast h
    have hp : 0<(r.den:Rat) := (Rat.natCast_pos).2 hden
    have hc := Rat.mul_inv_cancel (r.den:Rat) (Rat.ne_of_gt hp)
    rw [hnum',Rat.div_def]
    grind

private theorem power_ge_one {a : Rat} (ha : 1≤a) (n : Nat) : 1≤a^n := by
  induction n with
  | zero => rw [Rat.pow_zero];exact Rat.le_refl
  | succ n ih =>
    rw [Rat.pow_succ]
    have hn : 0≤a^n := by grind
    have h:=Rat.mul_le_mul_of_nonneg_left ha hn
    grind

/-- The hypothetical rational square supplies the very same positive-small
integer sequence consumed by CartwrightArithmetic. -/
theorem integer_bounds (H : Laws) (a b : Nat) (ha : 0<a) (hb : 0<b)
    (hr : Near (fun k=>(frequencySample k)^2) (fun _=>(a:Rat)/(b:Rat))) (n : Nat) :
    0<integerValue (a:Int) (b:Int) n ∧
    integerValue (a:Int) (b:Int) n * ((2^n*factorial n:Nat):Int) ≤ ((2*a^n:Nat):Int) := by
  let r : Rat := (a:Rat)/(b:Rat)
  let K : Int := integerValue (a:Int) (b:Int) n
  have hpoly := (polynomial_near (Bounded.pow frequencySample_bounded 2) hr n).1
  change Near (fun k=>polynomialValue ((frequencySample k)^2) n) (fun _=>polynomialValue r n) at hpoly
  have hev := Near.trans (evaluated H n) (Near.scale hpoly (factor n))
  have hscaled := Near.scale hev ((b:Rat)^n)
  have hpB : 0<(b:Rat) := (Rat.natCast_pos).2 hb
  have hc := Rat.mul_inv_cancel (b:Rat) (Rat.ne_of_gt hpB)
  have hden := denominator_cleared (a:Int) (b:Int) (by simpa only [Rat.intCast_natCast] using Rat.ne_of_gt hpB) n
  simp only [Rat.intCast_natCast] at hden
  have hright : (fun _ : Nat=>(b:Rat)^n*(factor n*polynomialValue r n))=(fun _=>factor n*(K:Rat)) := by
    funext k
    dsimp [K,r]
    rw [hden]
    grind
  rw [hright] at hscaled
  have hrn := Near.pow (Bounded.pow frequencySample_bounded 2) (Bounded.constant r) hr n
  have hmul := Near.mul_left (Bounded.mul frequencySample_bounded (sample_bounded n)) hrn
  have hbmul := Near.scale hmul ((b:Rat)^n)
  have hleft : (fun k=>(b:Rat)^n*((frequencySample k*sample n k)*((frequencySample k)^2)^n))=
      (fun k=>(b:Rat)^n*((frequencySample k)^(2*n+1)*sample n k)) := by
    funext k
    rw [←pow_mul,pow_add,Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
    grind
  have hrpower : (b:Rat)^n*r^n=(a:Rat)^n := by
    rw [←mul_pow]
    congr 1
    dsimp [r]
    simp only [Rat.div_def]
    grind
  have hright' : (fun k=>(b:Rat)^n*((frequencySample k*sample n k)*r^n))=
      (fun k=>frequencySample k*(a:Rat)^n*sample n k) := by
    funext k
    calc
      _ = frequencySample k*((b:Rat)^n*r^n)*sample n k := by grind
      _ = _ := by rw [hrpower]
  rw [hleft,hright'] at hbmul
  have hnear := Near.trans (Near.symm hbmul) hscaled
  have ha1 : (1:Rat)≤(a:Rat) := by exact_mod_cast (show 1≤a by omega)
  have hap := power_ge_one ha1 n
  have hpbound := positiveBound_pos n
  have hbounds := Near.constant_bounds hnear 1 (A:=positiveBound n) (B:=2*(a:Rat)^n) (by
    intro k hk
    have hP:=frequencySample_bounds k
    have hJ:=sample_bounds n k
    have hl:=sample_positive n k hk
    have ha0 : 0≤(a:Rat)^n := by grind
    have hj0:=hJ.1
    have hpa := Rat.mul_le_mul_of_nonneg_left hap (show 0≤frequencySample k by grind)
    have hprod := Rat.mul_le_mul_of_nonneg_right hpa hj0
    have hPJ := Rat.mul_le_mul_of_nonneg_right hP.1 hj0
    have hupper := Rat.mul_le_mul_of_nonneg_left hJ.2 (Rat.mul_nonneg (show 0≤frequencySample k by grind) ha0)
    have hPupper := Rat.mul_le_mul_of_nonneg_right hP.2 ha0
    constructor <;> grind)
  have hKpos : (0:Rat)<(K:Rat) := by
    have hf:=factor_nonnegative n
    by_cases h : 0<(K:Rat)
    · exact h
    · have hk : (K:Rat)≤0 := by grind
      have hm:=Rat.mul_le_mul_of_nonneg_left hk hf
      grind
  have hfactor : factor n=((2^n*factorial n:Nat):Rat) := by
    simp only [factor,Rat.natCast_mul,Rat.natCast_pow,show ((2:Nat):Rat)=2 by decide +kernel]
  have hupper : (K:Rat)*((2^n*factorial n:Nat):Rat)≤((2*a^n:Nat):Rat) := by
    rw [←hfactor]
    have hh:=hbounds.2
    simp only [Rat.natCast_mul,Rat.natCast_pow,show ((2:Nat):Rat)=2 by decide +kernel]
    grind
  constructor
  · exact_mod_cast hKpos
  · exact_mod_cast hupper

/-- The square of the half-turn frequency is irrational once the moment laws
are proved. The complete native FTC route below supplies them. -/
theorem frequency_square_irrational (H : Laws) :
    RealRaw.Irrational (power frequency 2) := by
  intro r he
  have hnear := Near.of_equiv (power_valid _ frequency_valid 2) (RealRaw.ofRat_valid r) he
    (fun k=>power_mem (frequencySample_mem k) 2) (ClockTrigonometry.rat_mem r)
  have hbounds := Near.constant_bounds hnear 0 (A:=1) (B:=4) (by
    intro k _
    have hp:=frequencySample_bounds k
    have h0 : 0≤frequencySample k := by grind
    have h1:=Rat.mul_le_mul_of_nonneg_left hp.1 h0
    have h2:=Rat.mul_le_mul_of_nonneg_right hp.2 h0
    simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
    constructor <;> grind)
  have hr : 0<r := by grind
  obtain ⟨a,b,ha,hb,hrat⟩:=positive_nat_ratio hr
  rw [hrat] at hnear
  have hK:=integer_bounds H a b ha hb hnear (witnessIndex a)
  exact integer_obstruction a ha _ hK.1 hK.2

end ComputableAnalysis.CartwrightIrrationality
