import ComputableAnalysis.CartwrightIrrationality

/-! Public statements use the original geometric pi. The auxiliary rectangle
frequency used in finite derivative estimates is connected by a proved
representation edge, never by changing the definition of pi. -/
namespace ComputableAnalysis.CartwrightTheorem
open CartwrightEvaluation CartwrightMomentRecurrence CartwrightClockBounds
open IntervalSelections

/-- The half-turn frequency, defined from geometric arctangent. -/
def lambda : RealRaw := RealRaw.scaleRat (1/2) CosinePrimitive.pi

theorem lambda_valid : lambda.Valid := RealRaw.scaleRat_valid CosinePrimitive.pi_valid

theorem frequency_equiv_lambda : frequency.Equiv lambda := by
  have h := RealRaw.scaleRat_equiv (r:=(2:Rat))
    (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom (x:=1) (by decide +kernel))
  have he : RealRaw.scaleRat 2 (ArctanGeometry.arctanGeom 1)=lambda := by
    apply congrArg (fun f=>RealRaw.mk f .unknown)
    funext k
    change (RealRaw.scaleRat 2 (ArctanGeometry.arctanGeom 1)).compute k = lambda.compute k
    simp only [lambda,CosinePrimitive.pi,CosinePrimitive.A,RealRaw.scaleRat,RealRaw.scaleRatCompute]
    change (if 0≤(2:Rat) then _ else _) = (if 0≤(1:Rat)/2 then _ else _)
    simp only [if_pos (show (0:Rat)≤2 by decide +kernel),if_pos (show (0:Rat)≤1/2 by decide +kernel)]
    change ({lo:=2*((ArctanGeometry.arctanGeom 1).compute k).lo,hi:=2*((ArctanGeometry.arctanGeom 1).compute k).hi}:QInterval) =
      {lo:=(1/2)*((RealRaw.scaleRat 4 (ArctanGeometry.arctanGeom 1)).compute k).lo,
       hi:=(1/2)*((RealRaw.scaleRat 4 (ArctanGeometry.arctanGeom 1)).compute k).hi}
    simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos (show (0:Rat)≤4 by decide +kernel)]
    congr 1 <;> simp only [Rat.div_def] <;> grind
  rw [he] at h
  exact h

theorem power_equiv {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid) (h : X.Equiv Y) (n : Nat) :
    (power X n).Equiv (power Y n) := by
  induction n with
  | zero => exact RealRaw.equiv_refl _ (RealRaw.ofRat_valid 1)
  | succ n ih => exact RealRaw.mul_equiv (power_valid _ hX n) (power_valid _ hY n) hX hY ih h

theorem polynomialPair_equiv {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (h : X.Equiv Y) (n : Nat) :
    (polynomialPairRaw X n).1.Equiv (polynomialPairRaw Y n).1 ∧
    (polynomialPairRaw X n).2.Equiv (polynomialPairRaw Y n).2 := by
  induction n with
  | zero => exact ⟨RealRaw.equiv_refl _ (RealRaw.ofRat_valid 1),RealRaw.equiv_refl _ (RealRaw.ofRat_valid 1)⟩
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    exact RealRaw.sub_equiv
      (RealRaw.scaleRat_valid (polynomialPair_valid _ hX n).2)
      (RealRaw.scaleRat_valid (polynomialPair_valid _ hY n).2)
      (RealRaw.mul_valid hX (polynomialPair_valid _ hX n).1)
      (RealRaw.mul_valid hY (polynomialPair_valid _ hY n).1)
      (RealRaw.scaleRat_equiv ih.2)
      (RealRaw.mul_equiv hX hY (polynomialPair_valid _ hX n).1 (polynomialPair_valid _ hY n).1 h ih.1)

/-- The actual arithmetic application concerns this geometric square. -/
def PiSquaredStatement : Prop := RealRaw.Irrational (RealRaw.mul CosinePrimitive.pi CosinePrimitive.pi)

/-- The shared final transport from the frequency presentation to geometric pi. -/
theorem pi_squared_of_laws (H : Laws) : PiSquaredStatement := by
  intro q hq
  have hPi:=CosinePrimitive.pi_valid
  have hsquare:=RealRaw.mul_valid hPi hPi
  let scaled : RealRaw := RealRaw.scaleRat (1/4) (RealRaw.mul CosinePrimitive.pi CosinePrimitive.pi)
  have hscaled : scaled.Valid := RealRaw.scaleRat_valid hsquare
  have he : (power lambda 2).Equiv scaled := by
    apply ClockTrigonometry.equiv_of_sample_equality (power_valid _ lambda_valid 2) hscaled
      (fun k=>((1/2)*(CosinePrimitive.pi.compute k).lo)^2)
      (fun k=>(1/4)*((CosinePrimitive.pi.compute k).lo*(CosinePrimitive.pi.compute k).lo))
    · intro k
      exact power_mem (scale_mem (show InBox (CosinePrimitive.pi.compute k).lo (CosinePrimitive.pi.compute k) from
        ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ hPi k⟩) (by decide +kernel)) 2
    · intro k
      exact scale_mem (mul_mem
        (show InBox (CosinePrimitive.pi.compute k).lo (CosinePrimitive.pi.compute k) from ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ hPi k⟩)
        (show InBox (CosinePrimitive.pi.compute k).lo (CosinePrimitive.pi.compute k) from ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ hPi k⟩)) (by decide +kernel)
    · intro k
      simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul,Rat.div_def]
      grind
  have hscaledq : scaled.Equiv (RealRaw.ofRat ((1/4)*q)) := by
    have h := RealRaw.scaleRat_equiv (r:=(1:Rat)/4) hq
    have hcomp : RealRaw.scaleRat (1/4) (RealRaw.ofRat q)=RealRaw.ofRat ((1/4)*q) := by
      apply congrArg (fun f=>RealRaw.mk f .unknown)
      funext k
      change (if 0≤(1:Rat)/4 then _ else _) = _
      rw [if_pos (show (0:Rat)≤1/4 by decide +kernel)]
      rfl
    rw [hcomp] at h
    exact h
  have h0:=power_equiv frequency_valid lambda_valid frequency_equiv_lambda 2
  have h1:=RealRaw.equiv_trans (power_valid _ frequency_valid 2) (power_valid _ lambda_valid 2) hscaled h0 he
  have h2:=RealRaw.equiv_trans (power_valid _ frequency_valid 2) hscaled (RealRaw.ofRat_valid _) h1 hscaledq
  exact CartwrightIrrationality.frequency_square_irrational H _ h2

/-- One public moment statement, with geometric pi/2 on both sides. -/
def momentLeft (n : Nat) : RealRaw := RealRaw.mul (power lambda (2*n+1)) (CartwrightMoments.integral n)
def momentRight (n : Nat) : RealRaw := RealRaw.scaleRat (factor n) (polynomialRaw (power lambda 2) n)
def MomentStatement (n : Nat) : Prop := (momentLeft n).Equiv (momentRight n)

theorem momentLeft_valid (n : Nat) : (momentLeft n).Valid :=
  RealRaw.mul_valid (power_valid _ lambda_valid _) (CartwrightMoments.integral_valid n)
theorem momentRight_valid (n : Nat) : (momentRight n).Valid :=
  RealRaw.scaleRat_valid (polynomialPair_valid _ (power_valid _ lambda_valid 2) n).1

theorem moment_of_laws (H : Laws) (n : Nat) : MomentStatement n := by
  have hl : (left n).Equiv (momentLeft n) :=
    RealRaw.mul_equiv (power_valid _ frequency_valid _) (power_valid _ lambda_valid _)
      (CartwrightMoments.integral_valid n) (CartwrightMoments.integral_valid n)
      (power_equiv frequency_valid lambda_valid frequency_equiv_lambda _)
      (RealRaw.equiv_refl _ (CartwrightMoments.integral_valid n))
  have hr : (right n).Equiv (momentRight n) := RealRaw.scaleRat_equiv
    (polynomialPair_equiv (power_valid _ frequency_valid 2) (power_valid _ lambda_valid 2)
      (power_equiv frequency_valid lambda_valid frequency_equiv_lambda 2) n).1
  exact RealRaw.equiv_trans (momentLeft_valid n) (left_valid n) (momentRight_valid n) (RealRaw.equiv_symm hl)
    (RealRaw.equiv_trans (left_valid n) (right_valid n) (momentRight_valid n) (of_laws H n) hr)

/-- Closed native FTC proof of the moment evaluation. -/
theorem moment_viaFTC (n : Nat) : MomentStatement n := moment_of_laws CartwrightMomentRecurrence.viaFTC n

/-- Closed native FTC/integration-by-parts proof: geometric pi squared is irrational. -/
theorem pi_squared_viaFTC : PiSquaredStatement := pi_squared_of_laws CartwrightMomentRecurrence.viaFTC

end ComputableAnalysis.CartwrightTheorem
