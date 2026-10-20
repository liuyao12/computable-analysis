import ComputableAnalysis.ArctanInverseConstruction
import ComputableAnalysis.SinPiIntegral

/-! Circle coordinates obtained by the specific geometric arctangent search.
Rational angle inputs are primary. The normalized quarter-turn coordinate is
also rational, and its target is computed from geometric arctangent at one. -/
namespace ComputableAnalysis.ArctanInverseCircle
open ArctanInverseConstruction ArctanSecantFoundation
open SinPiIntegral
set_option maxHeartbeats 2000000

def sine (theta : Rat) : RealRaw where
  compute n := rationalCircleSinInterval ((inverse (theta/2)).compute n)

def cosine (theta : Rat) : RealRaw where
  compute n := rationalCircleCosInterval ((inverse (theta/2)).compute n)

theorem sine_valid (theta : Rat) : (sine theta).Valid :=
  rationalCircleSinInterval_valid _ (inverse_valid _) (fun n =>
    ⟨(bracket_geometry _ n).1,(bracket_geometry _ n).2.2.1⟩)

theorem cosine_valid (theta : Rat) : (cosine theta).Valid :=
  rationalCircleCosInterval_valid _ (inverse_valid _) (fun n =>
    ⟨(bracket_geometry _ n).1,(bracket_geometry _ n).2.2.1⟩)

theorem angle_identity (theta : Rat)
    (hrange : (value 0).Le (RealRaw.ofRat (theta/2)) ∧
      (RealRaw.ofRat (theta/2)).Le (value 1)) :
    (forward (RealRaw.ofRat (theta/2))).Valid ∧
    (forward (RealRaw.ofRat (theta/2))).Equiv (RealRaw.ofRat (theta/2)) :=
  rational_forward_target _ hrange

def quarterTarget (t : Rat) : RealRaw := RealRaw.scaleRat t (value 1)
def quarterSlope (t : Rat) : RealRaw := inverseExtension (quarterTarget t)

def sineQuarter (t : Rat) : RealRaw where
  compute n := rationalCircleSinInterval ((quarterSlope t).compute n)

def cosineQuarter (t : Rat) : RealRaw where
  compute n := rationalCircleCosInterval ((quarterSlope t).compute n)

theorem quarterTarget_valid (t : Rat) : (quarterTarget t).Valid :=
  RealRaw.scaleRat_valid (value_valid ⟨by decide +kernel,by decide +kernel⟩)

theorem quarterTarget_width (t : Rat) (ht : 0≤t ∧ t≤1) (n : Nat) :
    ((quarterTarget t).compute (precision n)).width≤width n/128 := by
  change (QInterval.scaleRat t ((value 1).compute (precision n))).width≤_
  rw [QInterval.scaleRat_width_of_nonneg ht.1]
  have hw := source_width 1 ⟨by decide +kernel,by decide +kernel⟩ n
  have ho := (value_valid (x:=1) ⟨by decide +kernel,by decide +kernel⟩).1 (precision n)
  have hm := Rat.mul_le_mul_of_nonneg_right ht.2 ho
  exact Rat.le_trans (by simpa only [Rat.one_mul] using hm) hw

theorem quarterTarget_range (t : Rat) (ht : 0≤t ∧ t≤1) :
    (value 0).Le (quarterTarget t) ∧ (quarterTarget t).Le (value 1) := by
  have hv := value_valid (x:=1) ⟨by decide +kernel,by decide +kernel⟩
  have hlo (n : Nat) : 0≤((value 1).compute n).lo :=
    ArctanGeometry.arctanIntegralRectangleCompute_lower_nonnegative (by decide +kernel) _
  have hhi (n : Nat) : 0≤((value 1).compute n).hi :=
    Rat.le_trans (hlo n) (RealRaw.interval_order_of_valid _ hv n)
  constructor
  · intro n m
    change ((value 0).compute n).lo≤(RealRaw.scaleRatCompute t (value 1) m).hi
    rw [show ((value 0).compute n).lo=0 from ArctanGeometry.arctanIntegralRectangleCompute_zero_lower _]
    simp only [RealRaw.scaleRatCompute,if_pos ht.1]
    exact Rat.mul_nonneg ht.1 (hhi m)
  · intro n m
    change (RealRaw.scaleRatCompute t (value 1) n).lo≤((value 1).compute m).hi
    simp only [RealRaw.scaleRatCompute,if_pos ht.1]
    have hm := Rat.mul_le_mul_of_nonneg_right ht.2 (hlo n)
    exact Rat.le_trans (by simpa only [Rat.one_mul] using hm) (RealRaw.le_refl _ hv n m)

theorem quarterSlope_target (t : Rat) (ht : 0≤t ∧ t≤1) :
    (forward (quarterTarget t)).Valid ∧
      (forward (quarterTarget t)).Equiv (quarterTarget t) :=
  forward_valid_and_target _ (quarterTarget_valid t) (quarterTarget_width t ht) (quarterTarget_range t ht)

theorem sineQuarter_valid (t : Rat) : (sineQuarter t).Valid :=
  rationalCircleSinInterval_valid _ (inverseExtension_valid _) (fun n =>
    ⟨(bracket_geometry _ n).1,(bracket_geometry _ n).2.2.1⟩)

theorem cosineQuarter_valid (t : Rat) : (cosineQuarter t).Valid :=
  rationalCircleCosInterval_valid _ (inverseExtension_valid _) (fun n =>
    ⟨(bracket_geometry _ n).1,(bracket_geometry _ n).2.2.1⟩)

end ComputableAnalysis.ArctanInverseCircle
