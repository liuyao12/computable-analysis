import ComputableAnalysis.CartwrightFrequency
import ComputableAnalysis.CartwrightArithmetic
import ComputableAnalysis.FiniteRationalPowers

/-! One common computational statement for the alternative moment proofs.
Definitions in this module use no moment evaluation, recurrence, FTC or
irrationality result. The polynomial algorithm is a finite integer recurrence. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse IntervalSelections CartwrightArithmetic
open FiniteRationalPowers

/-- Interval multiplication by repeated finite products. -/
def power (X : RealRaw) : Nat → RealRaw
  | 0 => RealRaw.one
  | n+1 => RealRaw.mul (power X n) X

theorem power_valid {X : RealRaw} (hX : X.Valid) (n : Nat) : (power X n).Valid := by
  induction n with
  | zero => exact RealRaw.ofRat_valid 1
  | succ n ih => exact RealRaw.mul_valid ih hX

theorem power_mem {X : RealRaw} {x : Rat} {q : Nat} (hx : InBox x (X.compute q)) (n : Nat) :
    InBox (x^n) ((power X n).compute q) := by
  induction n with
  | zero => rw [Rat.pow_zero];exact ClockTrigonometry.rat_mem 1 q
  | succ n ih => rw [Rat.pow_succ];exact mul_mem ih hx

/-- The same recursion as CartwrightArithmetic.polynomialPair, now evaluated
by interval arithmetic at a computed argument. -/
def polynomialRawPair (z : RealRaw) : Nat → RealRaw × RealRaw
  | 0 => (RealRaw.one,RealRaw.one)
  | n+1 => let p:=polynomialRawPair z n
           (p.2,RealRaw.scaleRat (2*(n:Rat)+3) p.2-RealRaw.mul z p.1)

def polynomialRaw (z : RealRaw) (n : Nat) : RealRaw := (polynomialRawPair z n).1

theorem polynomialRawPair_valid {z : RealRaw} (hz : z.Valid) (n : Nat) :
    (polynomialRawPair z n).1.Valid ∧ (polynomialRawPair z n).2.Valid := by
  induction n with
  | zero => exact ⟨RealRaw.ofRat_valid 1,RealRaw.ofRat_valid 1⟩
  | succ n ih =>
    exact ⟨ih.2,RealRaw.sub_valid (RealRaw.scaleRat_valid ih.2) (RealRaw.mul_valid hz ih.1)⟩

theorem polynomialRawPair_mem {z : RealRaw} {x : Rat} {q : Nat}
    (hx : InBox x (z.compute q)) (n : Nat) :
    InBox (polynomialPair x n).1 ((polynomialRawPair z n).1.compute q) ∧
    InBox (polynomialPair x n).2 ((polynomialRawPair z n).2.compute q) := by
  induction n with
  | zero => exact ⟨ClockTrigonometry.rat_mem 1 q,ClockTrigonometry.rat_mem 1 q⟩
  | succ n ih =>
    have hcoef : 0≤2*(n:Rat)+3 := by have h:=Rat.natCast_nonneg (a:=n);grind
    exact ⟨ih.2,sub_mem (scale_mem ih.2 hcoef) (mul_mem hx ih.1)⟩

def normalizer (n : Nat) : Rat := ((2^n*factorial n : Nat):Rat)

theorem normalizer_pos (n : Nat) : 0<normalizer n := by
  apply (Rat.natCast_pos).2
  have hf : 0<factorial n := by have h:=FormalPowerSeries.factorial_ne_zero n;omega
  exact Nat.mul_pos (Nat.two_pow_pos n) hf

theorem normalizer_zero : normalizer 0=1 := by decide +kernel

theorem normalizer_step (n : Nat) : normalizer (n+1)=2*((n+1:Nat):Rat)*normalizer n := by
  unfold normalizer
  simp only [factorial,Nat.pow_succ,Rat.natCast_add,Rat.natCast_mul,Rat.natCast_pow,Rat.natCast_ofNat]
  grind only

def scaledMoment (n : Nat) : RealRaw := RealRaw.mul (power frequency (2*n+1)) (moment n)

def polynomialEndpoint (n : Nat) : RealRaw :=
  RealRaw.scaleRat (normalizer n) (polynomialRaw (RealRaw.mul frequency frequency) n)

/-- A single native proposition; each route must inhabit this exact type. -/
def EvaluationStatement (n : Nat) : Prop := (scaledMoment n).Equiv (polynomialEndpoint n)

def scaledSample (n q : Nat) : Rat := frequencySample q^(2*n+1)*momentSample n q

def endpointSample (n q : Nat) : Rat :=
  normalizer n*polynomialValue (frequencySample q*frequencySample q) n

theorem scaledMoment_valid (n : Nat) : (scaledMoment n).Valid :=
  RealRaw.mul_valid (power_valid frequency_valid _) (moment_valid n)

theorem polynomialEndpoint_valid (n : Nat) : (polynomialEndpoint n).Valid :=
  RealRaw.scaleRat_valid (polynomialRawPair_valid (RealRaw.mul_valid frequency_valid frequency_valid) n).1

theorem scaledSample_mem (n q : Nat) : InBox (scaledSample n q) ((scaledMoment n).compute q) :=
  mul_mem (power_mem (frequencySample_mem q) _) (momentSample_mem n q)

theorem endpointSample_mem (n q : Nat) : InBox (endpointSample n q) ((polynomialEndpoint n).compute q) :=
  scale_mem (polynomialRawPair_mem (mul_mem (frequencySample_mem q) (frequencySample_mem q)) n).1
    (Rat.le_of_lt (normalizer_pos n))

/-- The arithmetic endpoint of the application, referring to the original
geometric pi computation rather than a newly named limiting value. -/
def PiSquaredStatement : Prop := (RealRaw.mul CosinePrimitive.pi CosinePrimitive.pi).Irrational

def recurrenceA (n : Nat) : Rat := 2*((n+2:Nat):Rat)*(2*(n:Rat)+3)
def recurrenceB (n : Nat) : Rat := 4*((n+2:Nat):Rat)*((n+1:Nat):Rat)

theorem recurrenceA_nonneg (n : Nat) : 0≤recurrenceA n := by
  have h:=Rat.natCast_nonneg (a:=n)
  unfold recurrenceA
  simp only [Rat.natCast_add,Rat.natCast_ofNat]
  exact Rat.mul_nonneg (by grind) (by grind)

theorem recurrenceB_nonneg (n : Nat) : 0≤recurrenceB n :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.natCast_nonneg (a:=n+2))) (Rat.natCast_nonneg (a:=n+1))

def recurrenceSamples (n q : Nat) : Rat :=
  frequencySample q*frequencySample q*momentSample (n+2) q-
    recurrenceA n*momentSample (n+1) q+recurrenceB n*momentSample n q

def firstSamples (q : Nat) : Rat :=
  frequencySample q*frequencySample q*momentSample 1 q-2*momentSample 0 q


end ComputableAnalysis.CartwrightMoments
