import ComputableAnalysis.WallisData

/-! Pure rational endpoint algebra. No integral law is used to calculate
these coefficients, their factorial descriptions, or the Wallis product. -/
namespace ComputableAnalysis.Wallis

private theorem cast_factorial (n : Nat) : (factorial (n+1):Rat)=((n+1:Nat):Rat)*(factorial n:Rat) := by
  rw [factorial,Rat.natCast_mul]

theorem coefficient_pos : (n : Nat) → 0<coefficient n
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | n+2 => by
    unfold coefficient
    rw [Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos ((Rat.natCast_pos).2 (by omega))
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (by omega)))) (coefficient_pos n)

/-- Even cosine moments yield the central factorial ratio, uniformly in n. -/
theorem coefficient_even (n : Nat) :
    (4:Rat)^n*(factorial n:Rat)*(factorial n:Rat)*coefficient (2*n)=(factorial (2*n):Rat) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have he : 2*(n+1)=2*n+2 := by omega
    rw [he,coefficient,show 2*n+2=(2*n+1)+1 by omega,
      cast_factorial (2*n+1),cast_factorial (2*n),cast_factorial n,Rat.pow_succ]
    have hc:=Rat.mul_inv_cancel (((2*n+1)+1:Nat):Rat)
      (Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega)))
    simp only [Rat.natCast_add,Rat.natCast_mul,Rat.natCast_ofNat,Rat.div_def] at hc ⊢
    grind only

/-- Odd cosine moments provide the reciprocal central factorial ratio. -/
theorem coefficient_odd (n : Nat) :
    (factorial (2*n+1):Rat)*coefficient (2*n+1)=(4:Rat)^n*(factorial n:Rat)*(factorial n:Rat) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have he : 2*(n+1)+1=(2*n+1)+2 := by omega
    rw [he,coefficient,show (2*n+1)+2=((2*n+1)+1)+1 by omega,
      cast_factorial ((2*n+1)+1),cast_factorial (2*n+1),cast_factorial n,Rat.pow_succ]
    have hc:=Rat.mul_inv_cancel ((((2*n+1)+1)+1:Nat):Rat)
      (Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega)))
    simp only [Rat.natCast_add,Rat.natCast_mul,Rat.natCast_ofNat,Rat.div_def] at hc ⊢
    grind only

/-- This rational sequence is independent of pi and of all integral values. -/
def product (n : Nat) : Rat := coefficient (2*n+1)/coefficient (2*n)

theorem product_pos (n : Nat) : 0<product n := by
  rw [product,Rat.div_def]
  exact Rat.mul_pos (coefficient_pos _) ((Rat.inv_pos).2 (coefficient_pos _))

theorem product_zero : product 0=1 := by decide +kernel

/-- The usual finite Wallis product, written without an imported product API. -/
theorem product_step (n : Nat) : product (n+1)=
    (((2*n+2:Nat):Rat)*((2*n+2:Nat):Rat)/
      (((2*n+1:Nat):Rat)*((2*n+3:Nat):Rat)))*product n := by
  have h0:=Rat.mul_inv_cancel (coefficient (2*n)) (Rat.ne_of_gt (coefficient_pos _))
  have h1:=Rat.mul_inv_cancel (coefficient (2*(n+1))) (Rat.ne_of_gt (coefficient_pos _))
  have h2:=Rat.mul_inv_cancel ((2*n+2:Nat):Rat) (Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega)))
  have h3:=Rat.mul_inv_cancel ((2*n+3:Nat):Rat) (Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega)))
  have h4:=Rat.mul_inv_cancel (((2*n+1:Nat):Rat)*((2*n+3:Nat):Rat))
    (Rat.ne_of_gt (Rat.mul_pos ((Rat.natCast_pos).2 (by omega)) ((Rat.natCast_pos).2 (by omega))))
  have he:2*(n+1)=2*n+2:=by omega
  have ho:2*(n+1)+1=(2*n+1)+2:=by omega
  rw [he,coefficient] at h1
  unfold product
  rw [ho,he,coefficient,coefficient]
  simp only [Rat.natCast_add,Rat.natCast_mul,Rat.natCast_ofNat,Rat.div_def] at *
  grind only


/-- The two equivalent rational expressions for the upper Wallis endpoint. -/
theorem upper_ratio (n : Nat) :
    coefficient (2*n+1)/coefficient (2*n+2)=
      product n*(((2*n+2:Nat):Rat)/((2*n+1:Nat):Rat)) := by
  have ha:=Rat.mul_inv_cancel (coefficient (2*n)) (Rat.ne_of_gt (coefficient_pos _))
  have hd:=Rat.mul_inv_cancel (coefficient (2*n+2)) (Rat.ne_of_gt (coefficient_pos _))
  have h1:=Rat.mul_inv_cancel ((2*n+1:Nat):Rat) (Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega)))
  have h2:=Rat.mul_inv_cancel ((2*n+2:Nat):Rat) (Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega)))
  rw [coefficient] at hd
  unfold product
  rw [coefficient]
  simp only [Rat.div_def] at *
  grind only

end ComputableAnalysis.Wallis
