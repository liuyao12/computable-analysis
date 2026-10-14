import ComputableAnalysis.PowerSeries

/-! A sequence of rational samples with certified enclosures gives an
independent valid complex computation, exactly equivalent to its anchor.
The anchor is used only in proofs: the runtime reads samples and a rational
error constant. -/

namespace ComputableAnalysis.CertifiedComplexApproximation

def rate (B : Rat) (n : Nat) : Rat := B / ((n+1 : Nat) : Rat)

theorem rate_nonneg {B : Rat} (hB : 0 ≤ B) (n : Nat) : 0 ≤ rate B n := by
  exact Rat.mul_nonneg hB (Rat.le_of_lt ((Rat.inv_pos).2
    ((Rat.natCast_pos).2 (Nat.succ_pos n))))

theorem rate_antitone {B : Rat} (hB : 0 ≤ B) {k n : Nat} (hkn : k ≤ n) :
    rate B n ≤ rate B k := by
  have hk : (0 : Rat) < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (Nat.succ_pos k)
  have hn : (0 : Rat) < ((n+1 : Nat) : Rat) := (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hle : ((k+1 : Nat) : Rat) ≤ ((n+1 : Nat) : Rat) := by
    exact_mod_cast Nat.succ_le_succ hkn
  have hm := Rat.mul_le_mul_of_nonneg_left hle hB
  have hi := Rat.mul_inv_cancel (((k+1 : Nat) : Rat)) (Rat.ne_of_gt hk)
  have hj := Rat.mul_inv_cancel (((n+1 : Nat) : Rat)) (Rat.ne_of_gt hn)
  apply Rat.le_of_mul_le_mul_right (c := ((k+1 : Nat) : Rat)*((n+1 : Nat) : Rat)) ?_
    (Rat.mul_pos hk hn)
  simp only [rate, Rat.div_def]
  have he1 : (B*((n+1 : Nat) : Rat)⁻¹)*(((k+1 : Nat) : Rat)*((n+1 : Nat) : Rat)) =
      B*((k+1 : Nat) : Rat) := by
    calc
      _ = (B*((k+1 : Nat) : Rat))*(((n+1 : Nat) : Rat)*((n+1 : Nat) : Rat)⁻¹) := by grind only
      _ = _ := by rw [hj, Rat.mul_one]
  have he2 : (B*((k+1 : Nat) : Rat)⁻¹)*(((k+1 : Nat) : Rat)*((n+1 : Nat) : Rat)) =
      B*((n+1 : Nat) : Rat) := by
    calc
      _ = (B*((n+1 : Nat) : Rat))*(((k+1 : Nat) : Rat)*((k+1 : Nat) : Rat)⁻¹) := by grind only
      _ = _ := by rw [hi, Rat.mul_one]
  rw [he1, he2]
  exact hm

private theorem rat_le_num_natAbs_succ (q : Rat) :
    q <= (((q.num.natAbs : Nat) : Rat) + 1) := by
  by_cases hqpos : 0 < q
  · have hdenpos : 0 < ((q.den : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
    · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
      have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
      have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
      have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
        exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
      calc
        (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) := by
          exact_mod_cast (Nat.le_succ q.num.natAbs)
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) *
            ((q.den : Nat) : Rat) := by
          exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
            (Nat.pos_of_ne_zero q.den_nz))
    · exact hdenpos
  · have hqnonpos : q <= 0 := by grind
    have hzero : (0 : Rat) <= (((q.num.natAbs : Nat) : Rat) + 1) := by
      exact_mod_cast (Nat.zero_le (q.num.natAbs + 1))
    exact Rat.le_trans hqnonpos hzero

theorem rate_shrinks (B : Rat) : ShrinksToZero (rate B) := by
  apply shrinksToZero_of_natOverSuccBound (C := B.num.natAbs+1)
  intro n
  have hb : B ≤ ((B.num.natAbs+1 : Nat) : Rat) := by
    simpa [Rat.natCast_add] using rat_le_num_natAbs_succ B
  exact Rat.mul_le_mul_of_nonneg_right hb (Rat.le_of_lt ((Rat.inv_pos).2
    ((Rat.natCast_pos).2 (Nat.succ_pos n))))

def candidate (sample : Nat → QComplex) : ComplexRaw where
  compute n := QBox.point (sample n)

def raw (sample : Nat → QComplex) (B : Rat) : ComplexRaw :=
  ComplexRaw.cauchyStabilize (candidate sample) (rate (2*B))

theorem future {sample : Nat → QComplex} {B : Rat} {anchor : ComplexRaw}
    (hB : 0 ≤ B) (ha : anchor.Valid)
    (he : ∀ n, (anchor.compute n).NestedIn
      (QBox.expand (QBox.point (sample n)) (rate B n)))
    (k n : Nat) (hkn : k ≤ n) :
    ((candidate sample).compute n).NestedIn
      (QBox.expand ((candidate sample).compute k) (rate (2*B) k)) := by
  have hk := he k
  have hn := he n
  have hnest := ComplexRaw.valid_nestedIn ha hkn
  have ho := ComplexRaw.valid_ordered ha n
  have hr := rate_antitone hB hkn
  simp only [QBox.NestedIn, QBox.expand, QBox.point, candidate, QComplex.le_def,
    QBox.Ordered, rate, Rat.div_def] at *
  constructor <;> constructor <;> grind only

theorem valid {sample : Nat → QComplex} {B : Rat} {anchor : ComplexRaw}
    (hB : 0 ≤ B) (ha : anchor.Valid)
    (he : ∀ n, (anchor.compute n).NestedIn
      (QBox.expand (QBox.point (sample n)) (rate B n))) :
    (raw sample B).Valid := by
  apply ComplexRaw.cauchyStabilize_valid (fun _ => QComplex.le_refl _) _
    (future hB ha he) (rate_shrinks (2*B))
  intro eps
  refine ⟨0, fun n _ => ?_⟩
  have hp := eps.property
  change (sample n).re - (sample n).re ≤ eps.val ∧
    (sample n).im - (sample n).im ≤ eps.val
  constructor <;> grind

theorem encloses_anchor {sample : Nat → QComplex} {B : Rat} {anchor : ComplexRaw}
    (hB : 0 ≤ B) (ha : anchor.Valid)
    (he : ∀ n, (anchor.compute n).NestedIn
      (QBox.expand (QBox.point (sample n)) (rate B n))) (n : Nat) :
    (anchor.compute n).NestedIn ((raw sample B).compute n) := by
  apply ComplexRaw.cauchyStabilize_contains_external (external := anchor.compute) _ n n (Nat.le_refl n)
  intro k m hkm
  have hn := ComplexRaw.valid_nestedIn ha hkm
  have hx := he k
  have hr := rate_nonneg hB k
  apply QBox.nested_trans hn
  apply QBox.nested_trans hx
  apply QBox.expand_mono_radius
  simp only [rate, Rat.div_def] at *
  grind only

theorem equiv_anchor {sample : Nat → QComplex} {B : Rat} {anchor : ComplexRaw}
    (hB : 0 ≤ B) (ha : anchor.Valid)
    (he : ∀ n, (anchor.compute n).NestedIn
      (QBox.expand (QBox.point (sample n)) (rate B n))) :
    (raw sample B).Equiv anchor := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  have hc := encloses_anchor hB ha he n
  have ho := ComplexRaw.valid_ordered ha n
  simp only [QBox.Overlaps, QBox.NestedIn, QBox.Ordered, QComplex.le_def] at *
  constructor <;> constructor <;> grind only

end ComputableAnalysis.CertifiedComplexApproximation
