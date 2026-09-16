import ComputableAnalysis.DyadicRotationPowers

/-! Closed instances of both integral proofs: no inverse-provider parameter
remains. The first-quadrant endpoint values are also proved, so the numerical
integral at 0 and 1/2 is unconditionally equivalent to the reciprocal of pi. -/
namespace ComputableAnalysis
namespace ClosedCosineIntegral
open ClosedArctanInverse SinPiIntegral IntervalSelections

abbrev OnHalf (x : Rat) := 0 <=x ∧ x <=(1 : Rat)/2

def integral (a b : Rat) (ha : OnHalf a) (hb : OnHalf b) (hab : a <=b) : RealRaw :=
  CosineFTC.integral provider a b ha hb hab

theorem integral_valid (a b : Rat) (ha : OnHalf a) (hb : OnHalf b) (hab : a <=b) :
    (integral a b ha hb hab).Valid := CosineFTC.integral_valid provider a b ha hb hab

/-- Closed FTC proof, for the same literal program as the direct proof. -/
theorem viaFTC (a b : Rat) (ha : OnHalf a) (hb : OnHalf b) (hab : a <=b) :
    (integral a b ha hb hab).Equiv
      (RealRaw.mul reciprocalPiRaw (sinPiRawOfArctan provider b hb-sinPiRawOfArctan provider a ha)) :=
  CosineFTC.integral_cosPi_viaFTC provider a b ha hb hab

/-- Closed direct-inequality proof. -/
theorem viaInequalities (a b : Rat) (ha : OnHalf a) (hb : OnHalf b) (hab : a <=b) :
    (integral a b ha hb hab).Equiv
      (RealRaw.mul reciprocalPiRaw (sinPiRawOfArctan provider b hb-sinPiRawOfArctan provider a ha)) :=
  CosineFTC.integral_cosPi_viaInequalities provider a b ha hb hab

private theorem sine_zero : (sinPiRawOfArctan provider 0 (by constructor <;> decide +kernel)).Equiv RealRaw.zero := by
  change (ClockTrigonometry.sine (2*0)).Equiv RealRaw.zero
  rw [Rat.mul_zero]
  exact ClockTrigonometry.sine_endpoint (t:=0) (Or.inl rfl)
private theorem sine_half : (sinPiRawOfArctan provider (1/2) (by constructor <;> decide +kernel)).Equiv RealRaw.one := by
  change (ClockTrigonometry.sine (2*(1/2))).Equiv RealRaw.one
  rw [show (2 : Rat)*(1/2)=1 by decide +kernel]
  exact ClockTrigonometry.sine_endpoint (t:=1) (Or.inr rfl)

private theorem mul_one (X : RealRaw) (hX : X.Valid) :
    (RealRaw.mul X RealRaw.one).Equiv X := by
  apply ClockTrigonometry.equiv_of_sample_equality (RealRaw.mul_valid hX (RealRaw.ofRat_valid 1)) hX
    (fun n=>(X.compute n).lo*1) (fun n=>(X.compute n).lo)
    (fun n=>mul_mem ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ hX n⟩ (ClockTrigonometry.rat_mem 1 n))
    (fun n=>⟨Rat.le_refl,RealRaw.interval_order_of_valid _ hX n⟩)
    (fun _=>Rat.mul_one _)

/-- The closed inverse-arctangent cosine quadrature. This numerical program
normalizes through A(1), unlike the radical-only cosine sampler. -/
def quarterIntegral : RealRaw := integral 0 (1/2)
  (by constructor <;> decide +kernel) (by constructor <;> decide +kernel) (by decide +kernel)

theorem quarterIntegral_valid : quarterIntegral.Valid := integral_valid _ _ _ _ _

theorem quarterIntegral_equiv_reciprocalPi : quarterIntegral.Equiv reciprocalPiRaw := by
  let s1:=sinPiRawOfArctan provider (1/2) (by constructor <;> decide +kernel)
  let s0:=sinPiRawOfArctan provider 0 (by constructor <;> decide +kernel)
  have h1:s1.Valid:=sinPiRawOfArctan_valid _ _ _
  have h0:s0.Valid:=sinPiRawOfArctan_valid _ _ _
  have hpoint : (RealRaw.ofRat 1-RealRaw.ofRat 0).Equiv RealRaw.one := by
    apply RealRaw.equiv_of_compute_eq (RealRaw.sub_valid (RealRaw.ofRat_valid 1) (RealRaw.ofRat_valid 0))
    funext n
    change ({lo:=1-0,hi:=1-0} : QInterval)={lo:=1,hi:=1}
    rw [show (1 : Rat)-0=1 by decide +kernel]
  have hsub : (s1-s0).Equiv RealRaw.one :=
    RealRaw.equiv_trans (RealRaw.sub_valid h1 h0)
      (RealRaw.sub_valid (RealRaw.ofRat_valid 1) (RealRaw.ofRat_valid 0)) (RealRaw.ofRat_valid 1)
      (RealRaw.sub_equiv h1 (RealRaw.ofRat_valid 1) h0 (RealRaw.ofRat_valid 0) sine_half sine_zero) hpoint
  have hm:=RealRaw.mul_equiv reciprocalPiRaw_valid reciprocalPiRaw_valid
    (RealRaw.sub_valid h1 h0) (RealRaw.ofRat_valid 1)
    (RealRaw.equiv_refl _ reciprocalPiRaw_valid) hsub
  have he:=RealRaw.equiv_trans
    (RealRaw.mul_valid reciprocalPiRaw_valid (RealRaw.sub_valid h1 h0))
    (RealRaw.mul_valid reciprocalPiRaw_valid (RealRaw.ofRat_valid 1)) reciprocalPiRaw_valid
    hm (mul_one reciprocalPiRaw reciprocalPiRaw_valid)
  exact RealRaw.equiv_trans quarterIntegral_valid
    (RealRaw.mul_valid reciprocalPiRaw_valid (RealRaw.sub_valid h1 h0)) reciprocalPiRaw_valid
    (viaFTC 0 (1/2) _ _ _) he

end ClosedCosineIntegral
end ComputableAnalysis
