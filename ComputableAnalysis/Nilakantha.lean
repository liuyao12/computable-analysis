import ComputableAnalysis.Pi

/-!
# Nilakantha's accelerated rational pi series

The termwise proof in this module is finite rational arithmetic.  It certifies
the alternating bounds and their convergence before the separate pi-proof
module compares the resulting computation with the geometric baseline.
-/

namespace ComputableAnalysis

namespace Nilakantha

private theorem neg_one_pow_even (n : Nat) :
    (-1 : Rat) ^ (2 * n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      rw [Rat.pow_succ, Rat.pow_succ, ih]
      native_decide

private theorem neg_one_pow_odd (n : Nat) :
    (-1 : Rat) ^ (2 * n + 1) = -1 := by
  rw [Rat.pow_succ, neg_one_pow_even]
  native_decide

private theorem partial_even_to_odd (n : Nat) :
    nilakanthaPartial (2 * n + 1) =
      nilakanthaPartial (2 * n) + nilakanthaTerm (2 * n + 1) := by
  rw [show 2 * n + 1 = (2 * n) + 1 by omega]
  simp [nilakanthaPartial, neg_one_pow_even]

private theorem partial_odd_to_even (n : Nat) :
    nilakanthaPartial (2 * (n + 1)) =
      nilakanthaPartial (2 * n + 1) - nilakanthaTerm (2 * n + 2) := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
  simp [nilakanthaPartial, neg_one_pow_odd]
  grind [Rat.sub_eq_add_neg]

private theorem term_pos (k : Nat) (hk : 0 < k) :
    0 < nilakanthaTerm k := by
  unfold nilakanthaTerm
  rw [Rat.div_def]
  have hkRat : 0 < (k : Rat) := (Rat.natCast_pos).2 hk
  have htwoK : 0 < 2 * (k : Rat) :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 2) hkRat
  have hnext : 0 < 2 * (k : Rat) + 1 := by grind
  have hnextnext : 0 < 2 * (k : Rat) + 2 := by grind
  exact Rat.mul_pos (by native_decide : (0 : Rat) < 4)
    ((Rat.inv_pos).2 (Rat.mul_pos (Rat.mul_pos htwoK hnext) hnextnext))

private def termRat (x : Rat) : Rat :=
  4 / ((2 * x) * (2 * x + 1) * (2 * x + 2))

private theorem term_eq_rat (k : Nat) :
    nilakanthaTerm k = termRat (k : Rat) := rfl

private theorem termRat_step (x : Rat) (hx : 0 < x) :
    termRat (x + 1) <= termRat x := by
  let d : Rat := (2 * x) * (2 * x + 1) * (2 * x + 2)
  let e : Rat := (2 * (x + 1)) * (2 * (x + 1) + 1) *
    (2 * (x + 1) + 2)
  have htwoX : 0 < 2 * x :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 2) hx
  have hd1 : 0 < 2 * x + 1 := by grind
  have hd2 : 0 < 2 * x + 2 := by grind
  have he0 : 0 <= x + 1 := by grind
  have he1 : 0 < 2 * (x + 1) := by grind
  have he2 : 0 < 2 * (x + 1) + 1 := by grind
  have he3 : 0 < 2 * (x + 1) + 2 := by grind
  have hepos : 0 < e := Rat.mul_pos (Rat.mul_pos he1 he2) he3
  have hdiff : e - d = 24 * (x + 1) * (x + 1) := by
    dsimp [d, e]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hdiffnonneg : 0 <= e - d := by
    rw [hdiff]
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 24) he0) he0
  have hde : d <= e := by
    grind [Rat.sub_eq_add_neg]
  have hdpos : 0 < d := Rat.mul_pos (Rat.mul_pos htwoX hd1) hd2
  have hprodpos : 0 < d * e := Rat.mul_pos hdpos hepos
  change 4 / e <= 4 / d
  apply Rat.le_of_mul_le_mul_right (c := d * e)
  · calc
      (4 / e) * (d * e) = 4 * d := by
        rw [Rat.div_def]
        have he_ne : e ≠ 0 := Rat.ne_of_gt hepos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= 4 * e :=
        Rat.mul_le_mul_of_nonneg_left hde (by native_decide : (0 : Rat) <= 4)
      _ = (4 / d) * (d * e) := by
        rw [Rat.div_def]
        have hd_ne : d ≠ 0 := Rat.ne_of_gt hdpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact hprodpos

private theorem term_step_antitone (k : Nat) (hk : 0 < k) :
    nilakanthaTerm (k + 1) <= nilakanthaTerm k := by
  rw [term_eq_rat, term_eq_rat]
  have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
    norm_cast
  rw [hcast]
  exact termRat_step (k : Rat) ((Rat.natCast_pos).2 hk)

private theorem termRat_le_one_div (x : Rat) (hx : 0 < x) :
    termRat x <= 1 / x := by
  let d : Rat := (2 * x) * (2 * x + 1) * (2 * x + 2)
  have h2x : 0 < 2 * x :=
    Rat.mul_pos (by native_decide : (0 : Rat) < 2) hx
  have hd1 : 0 < 2 * x + 1 := by grind
  have hd2 : 0 < 2 * x + 2 := by grind
  have hdpos : 0 < d := Rat.mul_pos (Rat.mul_pos h2x hd1) hd2
  have hdiff : d - 4 * x = 4 * x * x * (2 * x + 3) := by
    dsimp [d]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hrest : 0 <= 4 * x * x * (2 * x + 3) := by
    have h2x3 : 0 <= 2 * x + 3 := by grind
    exact Rat.mul_nonneg
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 4)
          (Rat.le_of_lt hx))
        (Rat.le_of_lt hx))
      h2x3
  have hfourx : 4 * x <= d := by
    have : 0 <= d - 4 * x := by rw [hdiff]; exact hrest
    grind [Rat.sub_eq_add_neg]
  have hprodpos : 0 < d * x := Rat.mul_pos hdpos hx
  change 4 / d <= 1 / x
  apply Rat.le_of_mul_le_mul_right (c := d * x)
  · calc
      (4 / d) * (d * x) = 4 * x := by
        rw [Rat.div_def]
        have hd_ne : d ≠ 0 := Rat.ne_of_gt hdpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= d := hfourx
      _ = (1 / x) * (d * x) := by
        rw [Rat.div_def]
        have hx_ne : x ≠ 0 := Rat.ne_of_gt hx
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact hprodpos

private theorem term_le_one_div (k : Nat) (hk : 0 < k) :
    nilakanthaTerm k <= 1 / (k : Rat) := by
  rw [term_eq_rat]
  exact termRat_le_one_div (k : Rat) ((Rat.natCast_pos).2 hk)

private theorem partial_even_mono_succ (n : Nat) :
    nilakanthaPartial (2 * n) <= nilakanthaPartial (2 * (n + 1)) := by
  rw [partial_odd_to_even, partial_even_to_odd]
  have hterm := term_step_antitone (2 * n + 1)
    (by omega : 0 < 2 * n + 1)
  have hdelta :
      0 <= nilakanthaTerm (2 * n + 1) -
        nilakanthaTerm (2 * n + 2) := by
    grind [Rat.sub_eq_add_neg]
  grind [Rat.sub_eq_add_neg]

private theorem partial_odd_anti_succ (n : Nat) :
    nilakanthaPartial (2 * (n + 1) + 1) <=
      nilakanthaPartial (2 * n + 1) := by
  rw [partial_even_to_odd, partial_odd_to_even]
  have hterm := term_step_antitone (2 * n + 2)
    (by omega : 0 < 2 * n + 2)
  have hdelta :
      0 <= nilakanthaTerm (2 * n + 2) -
        nilakanthaTerm (2 * n + 3) := by
    grind [Rat.sub_eq_add_neg]
  grind [Rat.sub_eq_add_neg]

private theorem partial_even_mono {n m : Nat} (hnm : n <= m) :
    nilakanthaPartial (2 * n) <= nilakanthaPartial (2 * m) := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step hnm ih => exact Rat.le_trans ih (partial_even_mono_succ _)

private theorem partial_odd_anti {n m : Nat} (hnm : n <= m) :
    nilakanthaPartial (2 * m + 1) <= nilakanthaPartial (2 * n + 1) := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step hnm ih =>
      exact Rat.le_trans (partial_odd_anti_succ _) ih

private theorem partial_even_le_odd (n : Nat) :
    nilakanthaPartial (2 * n) <= nilakanthaPartial (2 * n + 1) := by
  rw [partial_even_to_odd]
  have hpos := term_pos (2 * n + 1)
    (by omega : 0 < 2 * n + 1)
  grind

theorem compute_eq (n : Nat) :
    piNilakantha.compute n =
      { lo := nilakanthaPartial (2 * n),
        hi := nilakanthaPartial (2 * n + 1) } := rfl

theorem compute_width_eq (n : Nat) :
    (piNilakantha.compute n).width = nilakanthaTerm (2 * n + 1) := by
  rw [compute_eq]
  unfold QInterval.width
  rw [partial_even_to_odd]
  grind [Rat.sub_eq_add_neg]

private theorem widths_shrink :
    RealRaw.WidthsShrinkToZero piNilakantha.compute := by
  intro eps
  refine ⟨eps.val.den + 1, ?_⟩
  intro n hn
  rw [compute_width_eq]
  have hnpos : 0 < n :=
    Nat.lt_of_lt_of_le (Nat.succ_pos eps.val.den) hn
  have hterm := term_le_one_div (2 * n + 1)
    (by omega : 0 < 2 * n + 1)
  have hrecip :
      1 / (((2 * n + 1 : Nat) : Rat)) <= 1 / (n : Rat) :=
    FTC.one_div_nat_antitone hnpos
      (by omega : 0 < 2 * n + 1)
      (by omega : n <= 2 * n + 1)
  have htoeps : 1 / (n : Rat) <= eps.val := by
    have hbase :
        1 / (((eps.val.den + 1 : Nat) : Rat)) <= eps.val :=
      FTC.one_div_den_succ_le_of_pos eps.property
    have hanti :
        1 / (n : Rat) <= 1 / (((eps.val.den + 1 : Nat) : Rat)) :=
      FTC.one_div_nat_antitone
        (Nat.succ_pos eps.val.den) hnpos hn
    exact Rat.le_trans hanti hbase
  exact Rat.le_trans hterm (Rat.le_trans hrecip htoeps)

theorem valid : piNilakantha.Valid := by
  unfold RealRaw.Valid RealRaw.ValidCompute
  constructor
  · intro n
    rw [compute_width_eq]
    exact Rat.le_of_lt (term_pos (2 * n + 1) (by omega : 0 < 2 * n + 1))
  · constructor
    · intro n m hnm
      rw [compute_eq, compute_eq]
      exact ⟨partial_even_mono hnm, partial_even_le_odd m,
        partial_odd_anti hnm⟩
    · exact widths_shrink

/-- The finite Leibniz loop, reproduced locally so that the Nilakantha
comparison remains a proof about rational finite sums and does not depend on
the larger pi proof layer. -/
private def leibnizStep (state : Rat × Rat) (i : Nat) : Rat × Rat :=
  ⟨state.1 - 1 / (4 * (i : Rat) + 3) +
      1 / (4 * (i : Rat) + 5),
    state.1 - 1 / (4 * (i : Rat) + 3)⟩

private def leibnizState (n : Nat) : Rat × Rat :=
  (List.range n).foldl
    (fun state (i : Nat) =>
      ⟨state.1 - 1 / (4 * (i : Rat) + 3) +
          1 / (4 * (i : Rat) + 5),
        state.1 - 1 / (4 * (i : Rat) + 3)⟩)
    ⟨1, 0⟩

private def leibnizLo (n : Nat) : Rat :=
  (leibnizState n).2

private def leibnizHi (n : Nat) : Rat :=
  (leibnizState n).1

private theorem leibnizState_succ (n : Nat) :
    leibnizState (n + 1) = leibnizStep (leibnizState n) n := by
  unfold leibnizState
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem piLeibniz_compute_eq (n : Nat) :
    piLeibniz.compute n =
      { lo := 4 * leibnizLo n, hi := 4 * leibnizHi n } := by
  change (RealRaw.scaleRat (4 : Rat) leibnizSeries).compute n =
    { lo := 4 * leibnizLo n, hi := 4 * leibnizHi n }
  have h4 : (0 : Rat) <= 4 := by native_decide
  simp [RealRaw.scaleRat, RealRaw.scaleRatCompute, h4, leibnizSeries,
    leibnizLo, leibnizHi, leibnizState]

private theorem rat_eq_of_mul_eq_mul_ne {a b c : Rat}
    (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The one-step finite rational identity that moves an even Nilakantha
partial sum to the next even Leibniz endpoint. -/
private theorem even_correction (x : Rat) (hx : 0 <= x) :
    1 / (2 * x + 2) - termRat (2 * x + 2) =
      4 / (4 * x + 5) - 1 / (2 * x + 3) := by
  let a : Rat := 2 * x + 2
  let b : Rat := 2 * a + 1
  let c : Rat := 2 * x + 3
  let d : Rat := 2 * a
  let e : Rat := 2 * a + 2
  have ha : 0 < a := by dsimp [a]; grind
  have hb : 0 < b := by dsimp [b, a]; grind
  have hc : 0 < c := by dsimp [c]; grind
  have hd : 0 < d := by dsimp [d, a]; grind
  have he : 0 < e := by dsimp [e, a]; grind
  have hB : 4 * x + 5 = b := by dsimp [b, a]; grind
  apply rat_eq_of_mul_eq_mul_ne (c := a * b * c * d * e)
  · exact Rat.ne_of_gt
      (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos ha hb) hc) hd) he)
  · rw [hB]
    change (1 / a - termRat a) * (a * b * c * d * e) =
      (4 / b - 1 / c) * (a * b * c * d * e)
    unfold termRat
    rw [Rat.div_def]
    have hane : a ≠ 0 := Rat.ne_of_gt ha
    have hbne : b ≠ 0 := Rat.ne_of_gt hb
    have hcne : c ≠ 0 := Rat.ne_of_gt hc
    have hdne : d ≠ 0 := Rat.ne_of_gt hd
    have hene : e ≠ 0 := Rat.ne_of_gt he
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]

/-- The one-step finite rational identity that moves an odd Nilakantha
partial sum to the next odd Leibniz endpoint. -/
private theorem odd_correction (x : Rat) (hx : 0 <= x) :
    -1 / (2 * x + 3) + termRat (2 * x + 3) =
      -4 / (4 * x + 7) + 1 / (2 * x + 4) := by
  let a : Rat := 2 * x + 3
  let b : Rat := 2 * a + 1
  let c : Rat := 2 * x + 4
  let d : Rat := 2 * a
  let e : Rat := 2 * a + 2
  have ha : 0 < a := by dsimp [a]; grind
  have hb : 0 < b := by dsimp [b, a]; grind
  have hc : 0 < c := by dsimp [c]; grind
  have hd : 0 < d := by dsimp [d, a]; grind
  have he : 0 < e := by dsimp [e, a]; grind
  have hB : 4 * x + 7 = b := by dsimp [b, a]; grind
  apply rat_eq_of_mul_eq_mul_ne (c := a * b * c * d * e)
  · exact Rat.ne_of_gt
      (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos ha hb) hc) hd) he)
  · rw [hB]
    change (-1 / a + termRat a) * (a * b * c * d * e) =
      (-4 / b + 1 / c) * (a * b * c * d * e)
    unfold termRat
    rw [Rat.div_def]
    have hane : a ≠ 0 := Rat.ne_of_gt ha
    have hbne : b ≠ 0 := Rat.ne_of_gt hb
    have hcne : c ≠ 0 := Rat.ne_of_gt hc
    have hdne : d ≠ 0 := Rat.ne_of_gt hd
    have hene : e ≠ 0 := Rat.ne_of_gt he
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]

/-- Exact finite identities relating the two Nilakantha endpoints at stage
`n` to the adjacent Leibniz endpoints.  They are a summation-by-parts
transformation, not an appeal to a completed real number system. -/
private theorem endpoints_eq_leibniz (n : Nat) :
    nilakanthaPartial (2 * n) = 4 * leibnizHi n - 1 / (2 * (n : Rat) + 1) /\
      nilakanthaPartial (2 * n + 1) =
        4 * leibnizLo (n + 1) + 1 / (2 * (n : Rat) + 2) := by
  induction n with
  | zero =>
      constructor <;>
        native_decide
  | succ n ih =>
      have heven :
          nilakanthaPartial (2 * (n + 1)) =
            4 * leibnizHi (n + 1) - 1 / (2 * ((n + 1 : Nat) : Rat) + 1) := by
        rw [partial_odd_to_even, ih.2]
        rw [leibnizLo, leibnizState_succ, leibnizStep]
        rw [leibnizHi, leibnizState_succ, leibnizStep]
        rw [term_eq_rat]
        have hcast : ((2 * n + 2 : Nat) : Rat) = 2 * (n : Rat) + 2 := by
          norm_cast
        rw [hcast]
        have hcorr := even_correction (n : Rat) (by
          exact Rat.natCast_nonneg)
        grind [Rat.sub_eq_add_neg]
      constructor
      · exact heven
      · rw [partial_even_to_odd (n + 1), heven]
        rw [leibnizLo, leibnizState_succ, leibnizStep]
        rw [leibnizHi]
        rw [term_eq_rat]
        have hcast : ((2 * (n + 1) + 1 : Nat) : Rat) =
            2 * (n : Rat) + 3 := by
          norm_cast
        rw [hcast]
        have hcorr := odd_correction (n : Rat) (by
          exact Rat.natCast_nonneg)
        grind [Rat.sub_eq_add_neg]

/-- The Leibniz loop's stage width is the next omitted reciprocal. -/
private theorem leibniz_endpoint_gap (n : Nat) :
    leibnizHi n = leibnizLo n + 1 / (4 * (n : Rat) + 1) := by
  induction n with
  | zero => native_decide
  | succ n ih =>
      rw [leibnizHi, leibnizState_succ, leibnizStep]
      rw [leibnizLo, leibnizState_succ, leibnizStep]
      grind [Rat.sub_eq_add_neg]

private theorem leibniz_lo_mono_succ (n : Nat) :
    leibnizLo n <= leibnizLo (n + 1) := by
  change leibnizLo n <= (leibnizState (n + 1)).2
  rw [leibnizState_succ]
  change leibnizLo n <= leibnizHi n - 1 / (4 * (n : Rat) + 3)
  rw [leibniz_endpoint_gap n]
  have hrecip :
      1 / (((4 * n + 3 : Nat) : Rat)) <=
        1 / (((4 * n + 1 : Nat) : Rat)) :=
    FTC.one_div_nat_antitone
      (by omega : 0 < 4 * n + 1)
      (by omega : 0 < 4 * n + 3)
      (by omega : 4 * n + 1 <= 4 * n + 3)
  norm_cast at hrecip
  grind [Rat.sub_eq_add_neg]

private theorem leibniz_lo_mono {n m : Nat} (hnm : n <= m) :
    leibnizLo n <= leibnizLo m := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step hnm ih => exact Rat.le_trans ih (leibniz_lo_mono_succ _)

theorem equiv_piLeibniz : piNilakantha.Equiv piLeibniz := by
  intro n
  apply (RealRaw.compareAt_overlap_iff piNilakantha piLeibniz n n).2
  rw [compute_eq, piLeibniz_compute_eq,
    (endpoints_eq_leibniz n).1, (endpoints_eq_leibniz n).2]
  constructor
  · have hpos : 0 < 1 / (2 * (n : Rat) + 1) := by
      rw [Rat.div_def]
      apply Rat.mul_pos (by native_decide : (0 : Rat) < 1)
      apply Rat.inv_pos.mpr
      have hn : 0 <= (n : Rat) := Rat.natCast_nonneg
      grind
    grind [Rat.sub_eq_add_neg]
  · have hlo := leibniz_lo_mono (n := n) (m := n + 1) (by omega)
    have hpos : 0 <= 1 / (2 * (n : Rat) + 2) := by
      rw [Rat.div_def]
      apply Rat.mul_nonneg (by native_decide : (0 : Rat) <= 1)
      apply Rat.le_of_lt
      apply Rat.inv_pos.mpr
      have hn : 0 <= (n : Rat) := Rat.natCast_nonneg
      grind
    exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_left hlo (by native_decide : (0 : Rat) <= 4))
      (by grind)

end Nilakantha

end ComputableAnalysis
