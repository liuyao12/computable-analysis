import ComputableAnalysis.RiemannHilbert.ContourSplitGeometry

/-! Executable positive integer meshes align any strict rational cut.
Numerators and denominators give a literal common lattice; no choice is used. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def rationalSplitLeftCount (I : QInterval) (c : Rat) : Nat := (c-I.lo).num.natAbs*(I.hi-c).den
def rationalSplitRightCount (I : QInterval) (c : Rat) : Nat := (I.hi-c).num.natAbs*(c-I.lo).den
def rationalSplitUnit (I : QInterval) (c : Rat) : Rat :=
  (((c-I.lo).den*(I.hi-c).den:Nat):Rat)⁻¹

theorem positiveRat_numerator_cast (q : Rat) (hq : 0<q) :
    (q.num.natAbs:Rat)=(q.den:Rat)*q := by
  rw [rat_den_mul_self]
  exact_mod_cast (Int.natAbs_of_nonneg (Int.le_of_lt (rat_num_pos_of_pos hq)))

theorem rationalSplitLeftCount_pos (I : QInterval) (c : Rat) (hc : I.lo<c) :
    0<rationalSplitLeftCount I c := by
  have hp : 0<c-I.lo := by grind only
  have hn := rat_num_pos_of_pos hp
  have hnat : 0<(c-I.lo).num.natAbs := by omega
  exact Nat.mul_pos hnat (Nat.pos_of_ne_zero (I.hi-c).den_nz)

theorem rationalSplitRightCount_pos (I : QInterval) (c : Rat) (hc : c<I.hi) :
    0<rationalSplitRightCount I c := by
  have hp : 0<I.hi-c := by grind only
  have hn := rat_num_pos_of_pos hp
  have hnat : 0<(I.hi-c).num.natAbs := by omega
  exact Nat.mul_pos hnat (Nat.pos_of_ne_zero (c-I.lo).den_nz)

theorem rationalSplitUnit_pos (I : QInterval) (c : Rat) : 0<rationalSplitUnit I c :=
  Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.mul_pos
    (Nat.pos_of_ne_zero (c-I.lo).den_nz) (Nat.pos_of_ne_zero (I.hi-c).den_nz)))

theorem rationalSplit_left_width (I : QInterval) (c : Rat) (hc : I.lo<c) :
    (rationalSplitLeftCount I c:Rat)*rationalSplitUnit I c=c-I.lo := by
  have hn := positiveRat_numerator_cast (c-I.lo) (by grind only)
  have hD := Rat.mul_inv_cancel (((c-I.lo).den*(I.hi-c).den:Nat):Rat)
    (Rat.ne_of_gt (Rat.natCast_pos.mpr (Nat.mul_pos
      (Nat.pos_of_ne_zero (c-I.lo).den_nz) (Nat.pos_of_ne_zero (I.hi-c).den_nz))))
  simp only [Rat.natCast_mul] at hD
  unfold rationalSplitLeftCount rationalSplitUnit
  simp only [Rat.natCast_mul]
  rw [hn]
  grind only

theorem rationalSplit_right_width (I : QInterval) (c : Rat) (hc : c<I.hi) :
    (rationalSplitRightCount I c:Rat)*rationalSplitUnit I c=I.hi-c := by
  have hn := positiveRat_numerator_cast (I.hi-c) (by grind only)
  have hD := Rat.mul_inv_cancel (((c-I.lo).den*(I.hi-c).den:Nat):Rat)
    (Rat.ne_of_gt (Rat.natCast_pos.mpr (Nat.mul_pos
      (Nat.pos_of_ne_zero (c-I.lo).den_nz) (Nat.pos_of_ne_zero (I.hi-c).den_nz))))
  simp only [Rat.natCast_mul] at hD
  unfold rationalSplitRightCount rationalSplitUnit
  simp only [Rat.natCast_mul]
  rw [hn]
  grind only

end ComputableAnalysis.RiemannHilbert.RectangularContour
