import ComputableAnalysis.ZetaReal

/-! Exact order and nonvanishing laws for the existing integer Dirichlet
computations, transported to the real-zeta evaluator and any equivalent valid
computation. This does not assert a complex-zeta continuation. -/
namespace ComputableAnalysis.ZetaIntegerBounds
open DirichletSeries
set_option maxHeartbeats 2000000

private theorem one_power (p : Nat) : (1 : Rat)^p=1 := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Rat.pow_succ,ih,Rat.one_mul]

theorem valid (p : Nat) (hp : 2 ≤ p) : (zetaNatRaw p).Valid :=
  zetaNatRaw_validCompute p hp


theorem lower (p : Nat) (hp : 2 ≤ p) :
    (RealRaw.ofRat (1+1/(2 : Rat)^p)).Le (zetaNatRaw p) := by
  intro n m
  have h2 := zetaNatPartial_le_of_le p (Nat.le_max_left 2 m)
  have hm := zetaNatInterval_nested p hp m (max 2 m) (Nat.le_max_right 2 m)
  have ho := zetaNatInterval_ordered p (max 2 m)
  have he : zetaNatPartial p 2 = 1+1/(2 : Rat)^p := by
    change (0 : Rat)+1/(1 : Rat)^p+1/(2 : Rat)^p=1+1/(2 : Rat)^p
    rw [one_power]
    have he : (1 : Rat)/1=1 := by decide +kernel
    rw [he,Rat.zero_add]
  change 1+1/(2 : Rat)^p ≤ (zetaNatInterval p m).hi
  rw [he] at h2
  exact Rat.le_trans h2 (Rat.le_trans ho hm.2.2)

theorem upper (p : Nat) (hp : 2 ≤ p) :
    (zetaNatRaw p).Le (RealRaw.ofRat 2) := by
  intro n m
  have h := zetaNatInterval_nested p hp 0 n (Nat.zero_le n)
  have ho := zetaNatInterval_ordered p n
  change (zetaNatInterval p n).lo ≤ 2
  have he : (zetaNatInterval p 0).hi = 2 := by
    change (0 : Rat)+2=2; exact Rat.zero_add 2
  rw [he] at h
  exact Rat.le_trans ho h.2.2

theorem nonzero (p : Nat) (hp : 2 ≤ p) :
    ¬ (zetaNatRaw p).Equiv (RealRaw.ofRat 0) := by
  intro he
  have hle := RealRaw.le_of_equiv (x := zetaNatRaw p) (valid p hp) (RealRaw.ofRat_valid 0) he
  have h := RealRaw.le_trans (y := zetaNatRaw p) (valid p hp) (lower p hp) hle 0 0
  have hpos : 0 < 1/(2 : Rat)^p := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.inv_pos.mpr (Rat.pow_pos (n := p) (by decide))
  change 1+1/(2 : Rat)^p ≤ 0 at h
  grind only

private theorem power_mono (b : Rat) (hb : 1 ≤ b) (p q : Nat) (hpq : p ≤ q) :
    b^p ≤ b^q := by
  have hb0 : 0 ≤ b := by grind only
  induction hpq with
  | refl => exact Rat.le_refl
  | @step q hpq ih =>
    have hpow := Rat.pow_nonneg (n := q) hb0
    have h := Rat.mul_le_mul_of_nonneg_left hb hpow
    rw [Rat.mul_one,←Rat.pow_succ] at h
    exact Rat.le_trans ih h

private theorem term_mono (p q k : Nat) (hpq : p ≤ q) :
    zetaNatTerm q k ≤ zetaNatTerm p k := by
  let b : Rat := ((k+1 : Nat) : Rat)
  have hb : 1 ≤ b := by
    dsimp [b]; change ((1 : Nat) : Rat) ≤ ((k+1 : Nat) : Rat)
    exact Rat.natCast_le_natCast.mpr (by omega)
  have hbpos : 0 < b := by grind only
  have hpow := power_mono b hb p q hpq
  have hp := Rat.pow_pos (n := p) hbpos
  have hq := Rat.pow_pos (n := q) hbpos
  have hcp := Rat.mul_inv_cancel (b^p) (Rat.ne_of_gt hp)
  have hcq := Rat.mul_inv_cancel (b^q) (Rat.ne_of_gt hq)
  change 1/b^q ≤ 1/b^p
  apply Rat.le_of_mul_le_mul_right (c := b^q) ?_ hq
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hq),Rat.div_def,Rat.one_mul]
  have h := Rat.mul_le_mul_of_nonneg_left hpow (Rat.le_of_lt (Rat.inv_pos.mpr hp))
  rw [Rat.inv_mul_cancel (b^p) (Rat.ne_of_gt hp)] at h
  exact h

private theorem partial_mono (p q n : Nat) (hpq : p ≤ q) :
    zetaNatPartial q n ≤ zetaNatPartial p n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    have ht := term_mono p q n hpq
    simp only [zetaNatPartial]
    grind only

/-- The infinite computed zeta values decrease with the integer exponent. -/
theorem antitone (p q : Nat) (hp : 2 ≤ p) (hpq : p ≤ q) :
    (zetaNatRaw q).Le (zetaNatRaw p) := by
  intro n m
  let k := max n m
  have hn := zetaNatPartial_le_of_le q (Nat.le_max_left n m)
  have hqp := partial_mono p q k hpq
  have ho := zetaNatInterval_ordered p k
  have hm := zetaNatInterval_nested p hp m k (Nat.le_max_right n m)
  exact Rat.le_trans hn (Rat.le_trans hqp (Rat.le_trans ho hm.2.2))

/-- Bounds apply to any valid computation of the same value, including the
public real-argument zeta construction at the integer point. -/
theorem bounds_of_equiv (p : Nat) (hp : 2 ≤ p) (x : RealRaw) (hx : x.Valid)
    (he : x.Equiv (zetaNatRaw p)) :
    (RealRaw.ofRat (1+1/(2 : Rat)^p)).Le x ∧ x.Le (RealRaw.ofRat 2) := by
  have hv := valid p hp
  exact ⟨RealRaw.le_trans (y := zetaNatRaw p) hv (lower p hp) (RealRaw.le_of_equiv hv hx (RealRaw.equiv_symm he)),
    RealRaw.le_trans (y := zetaNatRaw p) hv (RealRaw.le_of_equiv hx hv he) (upper p hp)⟩

theorem real_zeta_bounds (p : Nat) :
    let x := (ZetaReal.zeta (Real.ofRat ((p : Rat)+2)) (ZetaReal.integer_aboveOne p)).preferred
    (RealRaw.ofRat (1+1/(2 : Rat)^(p+2))).Le x ∧ x.Le (RealRaw.ofRat 2) := by
  exact bounds_of_equiv (p+2) (by omega) _
    (ZetaReal.zeta _ _).valid (ZetaReal.zeta_integer_equiv p)

end ComputableAnalysis.ZetaIntegerBounds
