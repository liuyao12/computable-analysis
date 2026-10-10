import ComputableAnalysis.Basic

namespace ComputableAnalysis.RationalArchimedesModulus
theorem qabs_le_numNatAbs_succ (q : Rat) :
    qabs q <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
  have hraw : q <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
    by_cases hqpos : 0 < q
    · have hdenpos : 0 < ((q.den : Nat) : Rat) :=
        (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
      apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
      · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
        have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
        have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
        have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
          exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
        calc
          (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
          _ <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
            exact_mod_cast (Nat.le_succ q.num.natAbs)
          _ <= (((q.num.natAbs + 1 : Nat) : Rat)) *
              ((q.den : Nat) : Rat) := by
            exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
              (Nat.pos_of_ne_zero q.den_nz))
      · exact hdenpos
    · have hqnonpos : q <= 0 := by grind
      have hzero : (0 : Rat) <= (((q.num.natAbs + 1 : Nat) : Rat)) := by
        exact_mod_cast (Nat.zero_le (q.num.natAbs + 1))
      exact Rat.le_trans hqnonpos hzero
  unfold qabs
  by_cases hneg : q < 0
  · simp [hneg]
    have hnegRaw : -q <= ((((-q).num.natAbs + 1 : Nat) : Rat)) := by
      by_cases hpos : 0 < -q
      · have hdenpos : 0 < (((-q).den : Nat) : Rat) :=
          (Rat.natCast_pos).2 (Nat.pos_of_ne_zero (-q).den_nz)
        apply Rat.le_of_mul_le_mul_right (c := (((-q).den : Nat) : Rat))
        · rw [Rat.mul_comm (-q) (((-q).den : Nat) : Rat),
            rat_den_mul_self]
          have hnumpos : 0 < (-q).num := rat_num_pos_of_pos hpos
          have hnum_nonneg : 0 <= (-q).num := Int.le_of_lt hnumpos
          have hcast : ((((-q).num.natAbs : Nat) : Rat)) =
              ((-q).num : Rat) := by
            exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
          calc
            ((-q).num : Rat) = (((-q).num.natAbs : Nat) : Rat) := by
              rw [hcast]
            _ <= ((((-q).num.natAbs + 1 : Nat) : Rat)) := by
              exact_mod_cast (Nat.le_succ (-q).num.natAbs)
            _ <= ((((-q).num.natAbs + 1 : Nat) : Rat)) *
                (((-q).den : Nat) : Rat) := by
              exact_mod_cast (Nat.le_mul_of_pos_right ((-q).num.natAbs + 1)
                (Nat.pos_of_ne_zero (-q).den_nz))
        · exact hdenpos
      · have hnonpos : -q <= 0 := by grind
        exact Rat.le_trans hnonpos (by exact_mod_cast
          (Nat.zero_le ((-q).num.natAbs + 1)))
    have hnum : (-q).num.natAbs = q.num.natAbs := by
      cases q
      simp
    simpa [hnum] using hnegRaw
  · simp [hneg]
    have hone : (((1 : Nat) : Rat)) = 1 := by decide +kernel
    simpa only [Rat.natCast_add, hone] using hraw

/-- The reciprocal-stage convergence lemma with an arbitrary nonnegative
rational coefficient.  Internally it replaces the coefficient by the finite
natural numerator bound above and reuses `shrinksToZero_of_natOverSuccBound`. -/
theorem shrinksToZero_of_ratOverSuccBound
    {width : Nat -> Rat} {C : Rat}
    (hbound : forall n, width n <= C / (((n + 1 : Nat) : Rat))) :
    ShrinksToZero width := by
  let N : Nat := C.num.natAbs + 1
  apply shrinksToZero_of_natOverSuccBound (C := N)
  intro n
  have hCN : C <= (N : Rat) :=
    Rat.le_trans (self_le_qabs C) (by
      simpa [N] using qabs_le_numNatAbs_succ C)
  have hinv : 0 <= ((((n + 1 : Nat) : Rat))⁻¹) :=
    Rat.le_of_lt ((Rat.inv_pos).2
      ((Rat.natCast_pos).2 (Nat.succ_pos n)))
  exact Rat.le_trans (hbound n) (by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right hCN hinv)

#print axioms qabs_le_numNatAbs_succ
#print axioms shrinksToZero_of_ratOverSuccBound
end ComputableAnalysis.RationalArchimedesModulus
