import ComputableAnalysis.RiemannHilbert.MatrixLogarithmFiniteNilpotence

/-! Executable Jordan shifts at every finite rank, their exact powers and
nilpotence, and rational diagonal changes of basis. All fiber entries may be
arbitrary valid represented complex values. -/
namespace ComputableAnalysis.RiemannHilbert.JordanShift
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}
set_option maxHeartbeats 1000000

def offset (n k : Nat) : ValueMap (Fiber n) (Fiber n) where
  eval x := ⟨fun i => if h : i.val+k<n then x.val ⟨i.val+k,h⟩ else zero,
    fun i => by dsimp; split; exact x.property _; exact ofQComplex_valid _⟩
  congr h i := by
    dsimp
    split
    · exact h _
    · exact equiv_refl _ (ofQComplex_valid _)

theorem offset_linear (n k : Nat) : IsLinear (offset n k) := by
  constructor
  · intro x y i
    dsimp [offset,Fiber.add]
    split
    · exact equiv_refl _ (add_valid (x.property _) (y.property _))
    · exact equiv_symm (zero_add_equiv zero (ofQComplex_valid _))
  · intro a x i
    dsimp [offset,Fiber.scale]
    split
    · exact equiv_refl _ (mul_valid a.property (x.property _))
    · exact equiv_symm (mul_zero_equiv a.val a.property)

theorem offset_zero (n : Nat) : (offset n 0).Equiv ValueMap.identity := by
  intro x i
  dsimp [offset]
  rw [if_pos i.isLt]
  exact equiv_refl _ (x.property i)

theorem offset_add (n a b : Nat) (x : Fiber n) :
    (offset n a).eval ((offset n b).eval x) ≈ (offset n (a+b)).eval x := by
  intro i
  dsimp [offset]
  split
  · rename_i ha
    split
    · rename_i hb
      have hab : i.val+(a+b)<n := by omega
      rw [dif_pos hab]
      have he : i.val+a+b=i.val+(a+b) := by omega
      simp only [he]
      exact equiv_refl _ (x.property _)
    · rename_i hb
      have hab : ¬ i.val+(a+b)<n := by omega
      rw [dif_neg hab]
      exact equiv_refl _ (ofQComplex_valid _)
  · rename_i ha
    have hab : ¬ i.val+(a+b)<n := by omega
    rw [dif_neg hab]
    exact equiv_refl _ (ofQComplex_valid _)

def shift (n : Nat) := offset n 1
theorem shift_linear (n : Nat) : IsLinear (shift n) := offset_linear n 1

theorem power_shift (n k : Nat) : (Neumann.power (shift n) k).Equiv (offset n k) := by
  induction k with
  | zero => exact ValueMap.equiv_symm (offset_zero n)
  | succ k ih =>
    intro x
    exact Setoid.trans ((shift n).congr (ih x))
      (by simpa only [shift,Nat.add_comm 1 k] using offset_add n 1 k x)

theorem offset_at_rank (n : Nat) (x : Fiber n) : (offset n n).eval x ≈ Fiber.zero n := by
  intro i
  dsimp [offset,Fiber.zero]
  rw [dif_neg (by omega)]
  exact equiv_refl _ (ofQComplex_valid _)

theorem shift_nilpotent (n : Nat) : MatrixLogarithm.NilpotentAt (shift n) n :=
  fun x => Setoid.trans (power_shift n n x) (offset_at_rank n x)

theorem offset_bound (n k : Nat) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((offset n k).eval x) B := by
  intro i
  dsimp [offset]
  split
  · exact hx _
  · exact bound_zero B hB (n := n) i

def rationalScale (r : Rat) : ValueMap (Fiber n) (Fiber n) :=
  ⟨ratScale r,fun h => ratScale_congr r h⟩

theorem rationalScale_linear (r : Rat) : IsLinear (rationalScale (n := n) r) :=
  ⟨ratScale_add r,ratScale_scale r⟩

def scaled (n : Nat) (r : Rat) := (shift n).followedBy (rationalScale r)
theorem scaled_linear (n : Nat) (r : Rat) : IsLinear (scaled n r) :=
  IsLinear.followedBy (shift_linear n) (rationalScale_linear r)

theorem scaled_power (n k : Nat) (r : Rat) (x : Fiber n) :
    (Neumann.power (scaled n r) k).eval x ≈ ratScale (r^k) ((offset n k).eval x) := by
  induction k with
  | zero =>
    have ho : x ≈ (offset n 0).eval x := Setoid.symm (offset_zero n x)
    have hs : (offset n 0).eval x ≈ ratScale (r^0) ((offset n 0).eval x) := by
      rw [Rat.pow_zero]
      intro i
      exact equiv_symm (scaleRat_one_equiv _ (((offset n 0).eval x).property i))
    exact Setoid.trans ho hs
  | succ k ih =>
    have ha : (shift n).eval ((Neumann.power (scaled n r) k).eval x) ≈
        ratScale (r^k) ((shift n).eval ((offset n k).eval x)) := Setoid.trans ((shift n).congr ih)
      (MatrixExponential.linear_ratScale (shift n) (shift_linear n) (r^k) ((offset n k).eval x))
    have hb : (Neumann.power (scaled n r) (k+1)).eval x ≈
        ratScale r (ratScale (r^k) ((offset n (k+1)).eval x)) :=
      ratScale_congr r (Setoid.trans ha (ratScale_congr (r^k)
        (by simpa only [shift,Nat.add_comm 1 k] using offset_add n 1 k x)))
    exact Setoid.trans hb (fun i => by
      have he : r*r^k=r^(k+1) := by rw [Rat.pow_succ]; exact Rat.mul_comm _ _
      simpa only [ratScale,he] using scaleRat_scaleRat_equiv r (r^k)
        (((offset n (k+1)).eval x).val i) (((offset n (k+1)).eval x).property i))

theorem scaled_nilpotent (n : Nat) (r : Rat) : MatrixLogarithm.NilpotentAt (scaled n r) n :=
  fun x => Setoid.trans (scaled_power n n r x)
    (Setoid.trans (ratScale_congr (r^n) (offset_at_rank n x)) (fun _ => scaleRat_zero_equiv _))

def diagonal (n : Nat) (r : Rat) : ValueMap (Fiber n) (Fiber n) where
  eval x := ⟨fun i => scaleRat (r^i.val) (x.val i),fun i => scaleRat_valid (x.property i)⟩
  congr h i := scaleRat_equiv (h i)

theorem diagonal_linear (n : Nat) (r : Rat) : IsLinear (diagonal n r) := by
  constructor
  · intro x y i
    exact scaleRat_add_equiv _ _ _ (x.property i) (y.property i)
  · intro a x i
    exact ratScale_scale (r^i.val) a x i

def inverseDiagonal (n : Nat) (r : Rat) : ValueMap (Fiber n) (Fiber n) where
  eval x := ⟨fun i => scaleRat (1/(r^i.val)) (x.val i),fun i => scaleRat_valid (x.property i)⟩
  congr h i := scaleRat_equiv (h i)

theorem rational_power_ne_zero (r : Rat) (hr : r ≠ 0) (k : Nat) : r^k ≠ 0 := by
  induction k with
  | zero => rw [Rat.pow_zero]; decide +kernel
  | succ k ih => rw [Rat.pow_succ]; grind only

def basis (n : Nat) (r : Rat) (hr : r ≠ 0) : LinearIso n n where
  toValueIso := {
    forward := diagonal n r
    backward := inverseDiagonal n r
    backward_forward x i := cancel_scale_reverse (r^i.val) (rational_power_ne_zero r hr i.val) (x.val i) (x.property i)
    forward_backward x i := cancel_scale (r^i.val) (rational_power_ne_zero r hr i.val) (x.val i) (x.property i) }
  linear := diagonal_linear n r

/-- Rational diagonal rescaling makes a Jordan shift as small as the
chosen rational coefficient, without any assumption on its nilpotence. -/
theorem basis_intertwines (n : Nat) (r : Rat) (x : Fiber n) :
    (diagonal n r).eval ((scaled n r).eval x) ≈ (shift n).eval ((diagonal n r).eval x) := by
  intro i
  dsimp [diagonal,scaled,shift,offset,ValueMap.followedBy,rationalScale,ratScale]
  split
  · rename_i h
    have he : r^i.val*r=r^(i.val+1) := (Rat.pow_succ _ _).symm
    simpa only [he] using scaleRat_scaleRat_equiv (r^i.val) r (x.val ⟨i.val+1,h⟩) (x.property _)
  · exact equiv_trans (scaleRat_valid (scaleRat_valid (ofQComplex_valid _)))
      (scaleRat_valid (ofQComplex_valid _)) (ofQComplex_valid _)
      (scaleRat_equiv (scaleRat_zero_equiv r)) (scaleRat_zero_equiv _)

end ComputableAnalysis.RiemannHilbert.JordanShift
