import ComputableAnalysis.DyadicTrigonometry

/-! Every first-quadrant dyadic angle is a finite power of one nested-radical
rotation. The paired recurrence evaluates both coordinates together and adds
no numerical pi or arctangent dependency. -/
namespace ComputableAnalysis
namespace DyadicTrigonometry
open ClosedArctanInverse

private def boxMul (I J : QInterval) : QInterval :=
  QBox.mulRealInterval I.lo I.hi J.lo J.hi

def multiplyPair (P Q : QInterval × QInterval) : QInterval × QInterval :=
  (QInterval.subInterval (boxMul P.1 Q.1) (boxMul P.2 Q.2),
   QInterval.addInterval (boxMul P.2 Q.1) (boxMul P.1 Q.2))

def powerCompute (d n : Nat) : Nat -> QInterval × QInterval
  | 0 => ({lo:=1,hi:=1},{lo:=0,hi:=0})
  | j+1 => multiplyPair (powerCompute d n j) ((cosine d).compute n,(sine d).compute n)

def powerCosine (d j : Nat) : RealRaw where
  compute := fun n=>(powerCompute d n j).1
def powerSine (d j : Nat) : RealRaw where
  compute := fun n=>(powerCompute d n j).2

theorem powerCosine_zero (d : Nat) : powerCosine d 0=RealRaw.ofRat 1 := rfl
theorem powerSine_zero (d : Nat) : powerSine d 0=RealRaw.ofRat 0 := rfl

theorem powerCosine_succ (d j : Nat) : powerCosine d (j+1)=
    RealRaw.mul (powerCosine d j) (cosine d)-RealRaw.mul (powerSine d j) (sine d) := rfl
theorem powerSine_succ (d j : Nat) : powerSine d (j+1)=
    RealRaw.mul (powerSine d j) (cosine d)+RealRaw.mul (powerCosine d j) (sine d) := rfl

theorem powers_valid (d j : Nat) : (powerCosine d j).Valid ∧ (powerSine d j).Valid := by
  induction j with
  | zero => exact ⟨RealRaw.ofRat_valid 1,RealRaw.ofRat_valid 0⟩
  | succ j ih =>
    rw [powerCosine_succ,powerSine_succ]
    exact ⟨RealRaw.sub_valid (RealRaw.mul_valid ih.1 (cosine_valid d))
      (RealRaw.mul_valid ih.2 (sine_valid d)),
      RealRaw.add_valid (RealRaw.mul_valid ih.2 (cosine_valid d))
      (RealRaw.mul_valid ih.1 (sine_valid d))⟩

def gridAngle (d j : Nat) : Rat := (j : Rat)*angle d

theorem gridAngle_step (d j : Nat) : gridAngle d (j+1)=gridAngle d j+angle d := by
  simp only [gridAngle,Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide +kernel]
  grind

theorem gridAngle_unit (d j : Nat) (hj : j <=2^d) : Unit (gridAngle d j) := by
  have hp:=angle_unit d
  have hcast : (j : Rat) <=((2^d : Nat) : Rat) := by exact_mod_cast hj
  have hpow : ((2^d : Nat) : Rat)=(2 : Rat)^d := by simp
  rw [hpow] at hcast
  have hm:=Rat.mul_le_mul_of_nonneg_right hcast hp.1
  have hc : (2 : Rat)^d*angle d=1 := by
    simp only [angle,meshRadius,Rat.div_def,Rat.one_mul]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.pow_pos (by decide)))
  rw [hc] at hm
  exact ⟨Rat.mul_nonneg (Rat.natCast_nonneg (a:=j)) hp.1,hm⟩

/-- All dyadic special values, not only the first halving sequence. -/
theorem powers_equiv (d j : Nat) (hj : j <=2^d) :
    (powerCosine d j).Equiv (ClockTrigonometry.cosine (gridAngle d j)) ∧
    (powerSine d j).Equiv (ClockTrigonometry.sine (gridAngle d j)) := by
  induction j with
  | zero =>
    have hc:=ClockTrigonometry.cosine_endpoint (t:=0) (Or.inl rfl)
    rw [show (1 : Rat)-0=1 by decide +kernel] at hc
    have hs:=ClockTrigonometry.sine_endpoint (t:=0) (Or.inl rfl)
    have he : gridAngle d 0=0 := by simp only [gridAngle,show ((0 : Nat) : Rat)=0 by decide +kernel,Rat.zero_mul]
    rw [he,powerCosine_zero,powerSine_zero]
    exact ⟨RealRaw.equiv_symm hc,RealRaw.equiv_symm hs⟩
  | succ j ih =>
    have hj0 : j <=2^d := by omega
    have hi:=ih hj0
    have hA:=gridAngle_unit d j hj0
    have hB:=angle_unit d
    have hSum : gridAngle d j+angle d <=1 := by
      rw [←gridAngle_step]
      exact (gridAngle_unit d (j+1) hj).2
    have hC:=ClockTrigonometry.cosine_addition hA hB hSum
    have hS:=ClockTrigonometry.sine_addition hA hB hSum
    have pc:=(powers_valid d j).1; have ps:=(powers_valid d j).2
    have cc:=cosine_valid d; have cs:=sine_valid d
    have ac:=ClockTrigonometry.cosine_valid hA; have ass:=ClockTrigonometry.sine_valid hA
    have bc:=ClockTrigonometry.cosine_valid hB; have bs:=ClockTrigonometry.sine_valid hB
    have hCC:=RealRaw.mul_equiv pc ac cc bc hi.1 (cosine_equiv d)
    have hSS:=RealRaw.mul_equiv ps ass cs bs hi.2 (sine_equiv d)
    have hSC:=RealRaw.mul_equiv ps ass cc bc hi.2 (cosine_equiv d)
    have hCS:=RealRaw.mul_equiv pc ac cs bs hi.1 (sine_equiv d)
    rw [powerCosine_succ,powerSine_succ,gridAngle_step]
    constructor
    · exact RealRaw.equiv_trans
        (RealRaw.sub_valid (RealRaw.mul_valid pc cc) (RealRaw.mul_valid ps cs))
        (RealRaw.sub_valid (RealRaw.mul_valid ac bc) (RealRaw.mul_valid ass bs))
        (ClockTrigonometry.cosine_valid (by rw [←gridAngle_step]; exact gridAngle_unit d (j+1) hj))
        (RealRaw.sub_equiv (RealRaw.mul_valid pc cc) (RealRaw.mul_valid ac bc)
          (RealRaw.mul_valid ps cs) (RealRaw.mul_valid ass bs) hCC hSS)
        (RealRaw.equiv_symm hC)
    · exact RealRaw.equiv_trans
        (RealRaw.add_valid (RealRaw.mul_valid ps cc) (RealRaw.mul_valid pc cs))
        (RealRaw.add_valid (RealRaw.mul_valid ass bc) (RealRaw.mul_valid ac bs))
        (ClockTrigonometry.sine_valid (by rw [←gridAngle_step]; exact gridAngle_unit d (j+1) hj))
        (RealRaw.add_equiv (RealRaw.mul_valid ps cc) (RealRaw.mul_valid ass bc)
          (RealRaw.mul_valid pc cs) (RealRaw.mul_valid ac bs) hSC hCS)
        (RealRaw.equiv_symm hS)

end DyadicTrigonometry
end ComputableAnalysis
