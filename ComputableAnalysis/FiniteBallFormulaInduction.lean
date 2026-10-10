import ComputableAnalysis.FiniteNBallVolume

/-! Induction solving the dimension-two recurrence. This is the algebraic
consequence of the geometric recurrence, not a replacement for its proof. -/
namespace ComputableAnalysis.RationalBall

/-- Finite factorial in rational arithmetic; no analytic definition. -/
def factorialQ : Nat → Rat
  | 0 => 1
  | m+1 => ((m+1:Nat):Rat)*factorialQ m

theorem factorialQ_pos (m : Nat) : 0 < factorialQ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    exact Rat.mul_pos (Rat.natCast_pos.mpr (Nat.succ_pos m)) ih

theorem factorialQ_ne_zero (m : Nat) : factorialQ m ≠ 0 := by
  have h := factorialQ_pos m
  grind

/-- Even-dimensional coefficients are obtained by induction, without
assuming a factorial formula for the volume. -/
theorem ballCoeff_even (m : Nat) :
    nBallCoeff (2*m)=1/factorialQ m := by
  induction m with
  | zero => simp [nBallCoeff,factorialQ,Rat.div_def,Rat.pow_succ] <;> grind
  | succ m ih =>
    have he : 2*(m+1)=2*m+2 := by omega
    rw [he,nBallCoeff_succ_two,ih]
    simp only [factorialQ]
    change 2/(((2*m:Nat):Rat)+2)*(1/factorialQ m)=
      1/(((m+1:Nat):Rat)*factorialQ m)
    have hcast : ((2*m:Nat):Rat)+2=2*((m+1:Nat):Rat) := by
      rw [Rat.natCast_mul,Rat.natCast_add]
      change 2*(m:Rat)+2=2*((m:Rat)+1)
      grind [Rat.mul_add]
    rw [hcast]
    simp only [Rat.div_def,Rat.inv_mul_rev]
    grind [Rat.mul_assoc,Rat.mul_comm]

/-- The odd coefficient formula follows from the same recurrence and the
one-dimensional base coefficient two. -/
theorem ballCoeff_odd_scaled (m : Nat) :
    factorialQ (2*m+1)*nBallCoeff (2*m+1)=
      (2:Rat)^(2*m+1)*factorialQ m := by
  induction m with
  | zero => simp [nBallCoeff,factorialQ,Rat.div_def,Rat.pow_succ] <;> grind
  | succ m ih =>
    have he : 2*(m+1)+1=(2*m+1)+2 := by omega
    rw [he,nBallCoeff_succ_two]
    simp only [factorialQ]
    have hden : ((2*m+3:Nat):Rat)=((2*m+1:Nat):Rat)+2 := by
      rw [show 2*m+3=(2*m+1)+2 by omega,Rat.natCast_add]
      rfl
    rw [← hden]
    change (((2*m+3:Nat):Rat)*(((2*m+2:Nat):Rat)*factorialQ (2*m+1)))*
      (2/((2*m+3:Nat):Rat)*nBallCoeff (2*m+1)) =
      (2:Rat)^(2*m+3)*(((m+1:Nat):Rat)*factorialQ m)
    have hp : (2:Rat)^(2*m+3)=(2:Rat)^(2*m+1)*4 := by
      rw [show 2*m+3=(2*m+1)+1+1 by omega,Rat.pow_succ,Rat.pow_succ]
      grind [Rat.mul_assoc]
    have hcast : ((2*m+2:Nat):Rat)=2*((m+1:Nat):Rat) := by
      rw [Rat.natCast_add,Rat.natCast_mul,Rat.natCast_add]
      change 2*(m:Rat)+2=2*((m:Rat)+1)
      grind [Rat.mul_add]
    have hd : ((2*m+3:Nat):Rat) ≠ 0 := by
      have h := Rat.natCast_pos.mpr (show 0<2*m+3 by omega)
      grind
    have hi := Rat.mul_inv_cancel ((2*m+3:Nat):Rat) hd
    rw [hp,hcast]
    grind [Rat.div_def,Rat.mul_assoc,Rat.mul_comm]

theorem ballCoeff_odd (m : Nat) :
    nBallCoeff (2*m+1)=(2:Rat)^(2*m+1)*factorialQ m/factorialQ (2*m+1) := by
  have h := ballCoeff_odd_scaled m
  have hz := factorialQ_ne_zero (2*m+1)
  have hi := Rat.mul_inv_cancel (factorialQ (2*m+1)) hz
  grind [Rat.div_def,Rat.mul_assoc,Rat.mul_comm]

/-- Finite evaluations satisfy the two general-dimensional formulas. The
parameter p will ultimately be the previously formalized disk computation. -/
theorem ballFormula_even (m : Nat) (p : Rat) :
    nBallVolumeModel (2*m) p 1 = p^m/factorialQ m := by
  have he : (2*m)/2=m := by omega
  have hone : (1:Rat)^(2*m)=1 := by
    have h : ∀ n : Nat,(1:Rat)^n=1 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [Rat.pow_succ,ih,Rat.one_mul]
    exact h _
  simp only [nBallVolumeModel,nBallPiExponent,he,hone,ballCoeff_even]
  grind [Rat.div_def,Rat.mul_assoc,Rat.mul_comm]

theorem ballFormula_odd (m : Nat) (p : Rat) :
    nBallVolumeModel (2*m+1) p 1 =
      (2:Rat)^(2*m+1)*factorialQ m*p^m/factorialQ (2*m+1) := by
  have he : (2*m+1)/2=m := by omega
  have hone : (1:Rat)^(2*m+1)=1 := by
    have h : ∀ n : Nat,(1:Rat)^n=1 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [Rat.pow_succ,ih,Rat.one_mul]
    exact h _
  simp only [nBallVolumeModel,nBallPiExponent,he,hone,ballCoeff_odd]
  grind [Rat.div_def,Rat.mul_assoc,Rat.mul_comm]

#print axioms ballCoeff_even
#print axioms ballCoeff_odd
#print axioms ballFormula_even
#print axioms ballFormula_odd
end ComputableAnalysis.RationalBall
