import ComputableAnalysis.CartwrightMomentRecurrence

/-! The algebraic consumer of the moment recurrence, and the common native
computational statement. All analytic routes instantiate the same laws. -/
namespace ComputableAnalysis.CartwrightEvaluation
open CartwrightArithmetic CartwrightMomentRecurrence CartwrightIntegrationByParts
open CartwrightMoments CartwrightClockBounds RationalErrorCalculus IntervalSelections

abbrev power := exp.PositiveRealRaw.natPowRaw

/-- The integer-polynomial recurrence evaluated by interval arithmetic. -/
def polynomialPairRaw (z : RealRaw) : Nat → RealRaw × RealRaw
  | 0 => (RealRaw.one,RealRaw.one)
  | n+1 => let p:=polynomialPairRaw z n
           (p.2,RealRaw.scaleRat (2*(n:Rat)+3) p.2-RealRaw.mul z p.1)

def polynomialRaw (z : RealRaw) (n : Nat) : RealRaw := (polynomialPairRaw z n).1

def factor (n : Nat) : Rat := (2:Rat)^n*(factorial n:Rat)

def left (n : Nat) : RealRaw := RealRaw.mul (power frequency (2*n+1)) (CartwrightMoments.integral n)
def right (n : Nat) : RealRaw := RealRaw.scaleRat (factor n) (polynomialRaw (power frequency 2) n)
def Statement (n : Nat) : Prop := (left n).Equiv (right n)

theorem power_valid (X : RealRaw) (hX : X.Valid) (n : Nat) : (power X n).Valid := by
  induction n with
  | zero => exact RealRaw.ofRat_valid 1
  | succ n ih => exact RealRaw.mul_valid ih hX

theorem polynomialPair_valid (X : RealRaw) (hX : X.Valid) (n : Nat) :
    (polynomialPairRaw X n).1.Valid ∧ (polynomialPairRaw X n).2.Valid := by
  induction n with
  | zero => exact ⟨RealRaw.ofRat_valid 1,RealRaw.ofRat_valid 1⟩
  | succ n ih => exact ⟨ih.2,RealRaw.sub_valid (RealRaw.scaleRat_valid ih.2) (RealRaw.mul_valid hX ih.1)⟩

theorem left_valid (n : Nat) : (left n).Valid :=
  RealRaw.mul_valid (power_valid _ frequency_valid _) (integral_valid n)
theorem right_valid (n : Nat) : (right n).Valid :=
  RealRaw.scaleRat_valid (polynomialPair_valid _ (power_valid _ frequency_valid 2) n).1

theorem factor_zero : factor 0=1 := by simp only [factor,Rat.pow_zero,factorial,Rat.one_mul];rfl
theorem factor_one : factor 1=2 := by decide +kernel

theorem factor_succ (n : Nat) : factor (n+1)=2*((n+1:Nat):Rat)*factor n := by
  unfold factor
  rw [factorial,Rat.natCast_mul,Rat.pow_succ]
  grind

theorem polynomial_zero (z : Rat) : polynomialValue z 0=1 := rfl
theorem polynomial_one (z : Rat) : polynomialValue z 1=1 := rfl

theorem polynomial_step (z : Rat) (n : Nat) :
    polynomialValue z (n+2)=(2*(n:Rat)+3)*polynomialValue z (n+1)-z*polynomialValue z n := rfl

theorem pow_add (a : Rat) (m n : Nat) : a^(m+n)=a^m*a^n := by
  induction n with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ n ih => rw [show m+(n+1)=(m+n)+1 by omega,Rat.pow_succ,ih,Rat.pow_succ];grind

theorem pow_mul (a : Rat) (m n : Nat) : a^(m*n)=(a^m)^n := by
  induction n with
  | zero => simp only [Nat.mul_zero,Rat.pow_zero]
  | succ n ih => rw [Nat.mul_succ,pow_add,ih,Rat.pow_succ]

/-- The entire polynomial evaluation is now finite algebra after the recurrence. -/
theorem evaluated_pair (H : Laws) (n : Nat) :
    Near (fun k=>(frequencySample k)^(2*n+1)*sample n k)
      (fun k=>factor n*polynomialValue ((frequencySample k)^2) n) ∧
    Near (fun k=>(frequencySample k)^(2*(n+1)+1)*sample (n+1) k)
      (fun k=>factor (n+1)*polynomialValue ((frequencySample k)^2) (n+1)) := by
  induction n with
  | zero =>
    constructor
    · simp only [Nat.mul_zero,Nat.zero_add,factor_zero,polynomial_zero,Rat.pow_succ,Rat.pow_zero,Rat.one_mul,Rat.mul_one]
      exact H.zero
    · simp only [Nat.reduceAdd,Nat.reduceMul,factor_one,polynomial_one,Rat.mul_one]
      exact H.one
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    have recurrence:=H.recurrence n
    have hscaled:=Near.mul_left (Bounded.pow frequencySample_bounded (2*n+3)) recurrence
    have hA:=Near.scale ih.2 (2*((n+2:Nat):Rat)*(2*(n:Rat)+3))
    have hB0:=Near.mul_left (Bounded.pow frequencySample_bounded 2) ih.1
    have hB:=Near.scale hB0 (4*((n+1:Nat):Rat)*((n+2:Nat):Rat))
    have hcombined:=Near.sub hA hB
    have hleft : (fun k=>(frequencySample k)^(2*n+3)*((frequencySample k)^2*sample (n+2) k))=
      (fun k=>(frequencySample k)^(2*(n+2)+1)*sample (n+2) k) := by
      funext k
      rw [show 2*(n+2)+1=(2*n+3)+2 by omega,pow_add]
      grind
    have hmiddle : (fun k=>(frequencySample k)^(2*n+3)*
      (2*((n+2:Nat):Rat)*(2*(n:Rat)+3)*sample (n+1) k-4*((n+1:Nat):Rat)*((n+2:Nat):Rat)*sample n k))=
      (fun k=>2*((n+2:Nat):Rat)*(2*(n:Rat)+3)*((frequencySample k)^(2*(n+1)+1)*sample (n+1) k)-
        4*((n+1:Nat):Rat)*((n+2:Nat):Rat)*((frequencySample k)^2*((frequencySample k)^(2*n+1)*sample n k))) := by
      funext k
      rw [show 2*(n+1)+1=2*n+3 by omega,
        show 2*n+3=(2*n+1)+2 by omega,pow_add]
      grind
    rw [hleft,hmiddle] at hscaled
    have h:=Near.trans hscaled hcombined
    have hright : (fun k=>2*((n+2:Nat):Rat)*(2*(n:Rat)+3)*
        (factor (n+1)*polynomialValue ((frequencySample k)^2) (n+1))-
        4*((n+1:Nat):Rat)*((n+2:Nat):Rat)*
          ((frequencySample k)^2*(factor n*polynomialValue ((frequencySample k)^2) n)))=
      (fun k=>factor (n+2)*polynomialValue ((frequencySample k)^2) (n+2)) := by
      funext k
      rw [polynomial_step,show n+2=(n+1)+1 by omega]
      simp only [factor_succ]
      grind
    rw [hright] at h
    exact h

theorem evaluated (H : Laws) (n : Nat) :
    Near (fun k=>(frequencySample k)^(2*n+1)*sample n k)
      (fun k=>factor n*polynomialValue ((frequencySample k)^2) n) := (evaluated_pair H n).1

/-- Selected rational powers are in the corresponding interval power. -/
theorem power_mem {X : RealRaw} {x : Rat} {k : Nat} (hx : InBox x (X.compute k)) (n : Nat) :
    InBox (x^n) ((power X n).compute k) := by
  induction n with
  | zero =>
    rw [Rat.pow_zero]
    exact ClockTrigonometry.rat_mem 1 k
  | succ n ih =>
    rw [Rat.pow_succ]
    exact mul_mem ih hx

theorem polynomialPair_mem {X : RealRaw} {x : Rat} {k : Nat} (hx : InBox x (X.compute k)) (n : Nat) :
    InBox (polynomialPair x n).1 ((polynomialPairRaw X n).1.compute k) ∧
    InBox (polynomialPair x n).2 ((polynomialPairRaw X n).2.compute k) := by
  induction n with
  | zero => exact ⟨ClockTrigonometry.rat_mem 1 k,ClockTrigonometry.rat_mem 1 k⟩
  | succ n ih =>
    refine ⟨ih.2,sub_mem ?_ (mul_mem hx ih.1)⟩
    exact scale_mem ih.2 (by have hn:=Rat.natCast_nonneg (a:=n);grind)

theorem factor_nonnegative (n : Nat) : 0≤factor n :=
  Rat.mul_nonneg (Rat.le_of_lt (Rat.pow_pos (by decide +kernel))) (Rat.natCast_nonneg (a:=factorial n))

theorem left_sample (n k : Nat) :
    InBox ((frequencySample k)^(2*n+1)*sample n k) ((left n).compute k) :=
  mul_mem (power_mem (frequencySample_mem k) _) (sample_mem n k)

theorem right_sample (n k : Nat) :
    InBox (factor n*polynomialValue ((frequencySample k)^2) n) ((right n).compute k) :=
  scale_mem (polynomialPair_mem (power_mem (frequencySample_mem k) 2) n).1 (factor_nonnegative n)

/-- Every proved recurrence route returns a proof of the SAME interval statement. -/
theorem of_laws (H : Laws) (n : Nat) : Statement n :=
  Near.to_equiv (left_valid n) (right_valid n) (left_sample n) (right_sample n) (evaluated H n)

theorem viaFTC (n : Nat) : Statement n := of_laws CartwrightMomentRecurrence.viaFTC n

end ComputableAnalysis.CartwrightEvaluation
