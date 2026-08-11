import ComputableAnalysis.Polynomial

namespace ComputableAnalysis

namespace Polynomial

/-! Finite, rational Descartes-style certificates.

These lemmas use only the supplied finite coefficient list.  The coefficient
orientation is the one used by `eval`: the head is the constant coefficient.
No completeness or arbitrary-degree root-existence theorem is involved.
-/

private theorem mul_nonpos_of_nonneg_of_nonpos {u v : Rat}
    (hu : 0 ≤ u) (hv : v ≤ 0) : u * v ≤ 0 := by
  have hnv : 0 ≤ -v := by grind
  have h := Rat.mul_nonneg hu hnv
  grind [Rat.mul_neg]

private theorem mul_neg_of_pos_of_neg {u v : Rat}
    (hu : 0 < u) (hv : v < 0) : u * v < 0 := by
  have hnu : 0 ≤ u := Rat.le_of_lt hu
  have h := mul_nonpos_of_nonneg_of_nonpos hnu (Rat.le_of_lt hv)
  have hne : u * v ≠ 0 := by
    intro hz
    rcases Rat.mul_eq_zero.mp hz with hu0 | hv0
    · grind
    · grind
  grind

theorem eval_nonincreasing_of_nonpos_coeffs
    {coeffs : List Rat}
    (hcoeffs : ∀ c, c ∈ coeffs → c ≤ 0)
    {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) :
    eval coeffs y ≤ eval coeffs x := by
  induction coeffs with
  | nil => simp [eval]
  | cons c cs ih =>
      simp only [eval, List.foldr]
      have hc : c ≤ 0 := hcoeffs c (by simp)
      have hcs : ∀ d, d ∈ cs → d ≤ 0 := by
        intro d hd
        exact hcoeffs d (by simp [hd])
      have hnonpos : eval cs y ≤ 0 :=
        eval_nonpos_of_nonpos_coeffs hcs (by grind)
      have hdiff : eval cs y ≤ eval cs x := ih hcs
      have hfirst : (y - x) * eval cs y ≤ 0 := by
        have hyx : 0 ≤ y - x := by grind
        exact mul_nonpos_of_nonneg_of_nonpos hyx hnonpos
      have hsecond : x * (eval cs y - eval cs x) ≤ 0 := by
        have hdiff' : eval cs y - eval cs x ≤ 0 := by grind
        exact mul_nonpos_of_nonneg_of_nonpos hx hdiff'
      change c + y * eval cs y ≤ c + x * eval cs x
      have hidentity :
          (c + y * eval cs y) - (c + x * eval cs x) =
            (y - x) * eval cs y + x * (eval cs y - eval cs x) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm]
      have hsum :
          (y - x) * eval cs y + x * (eval cs y - eval cs x) ≤ 0 := by
        grind
      grind

theorem eval_strictly_decreasing_of_nonpos_tail
    {a : Rat} {tail : List Rat}
    (htail : ∀ c, c ∈ tail → c ≤ 0)
    (htail_neg : ∃ c, c ∈ tail ∧ c < 0)
    {x y : Rat} (hx : 0 < x) (hxy : x < y) :
    eval (a :: tail) y < eval (a :: tail) x := by
  have htail_y : eval tail y < 0 := by
    rcases htail_neg with ⟨c, hc, hcneg⟩
    exact eval_neg_of_nonpos_coeffs_of_neg htail (by grind) hc hcneg
  have htail_mono : eval tail y ≤ eval tail x :=
    eval_nonincreasing_of_nonpos_coeffs htail (Rat.le_of_lt hx) (Rat.le_of_lt hxy)
  simp only [eval, List.foldr]
  have hfirst : (y - x) * eval tail y < 0 := by
    exact mul_neg_of_pos_of_neg (by grind) htail_y
  have hsecond : x * (eval tail y - eval tail x) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (Rat.le_of_lt hx) (by grind)
  change a + y * eval tail y < a + x * eval tail x
  have hidentity :
      (a + y * eval tail y) - (a + x * eval tail x) =
        (y - x) * eval tail y + x * (eval tail y - eval tail x) := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hsum :
      (y - x) * eval tail y + x * (eval tail y - eval tail x) < 0 := by
    grind
  grind

theorem at_most_one_positive_rational_root_of_nonpos_tail
    {a : Rat} {tail : List Rat}
    (htail : ∀ c, c ∈ tail → c ≤ 0)
    (htail_neg : ∃ c, c ∈ tail ∧ c < 0)
    {x y : Rat} (hx : 0 < x) (hy : 0 < y)
    (hxroot : eval (a :: tail) x = 0)
    (hyroot : eval (a :: tail) y = 0) :
    x = y := by
  apply Rat.le_antisymm
  · by_cases hxy : x ≤ y
    · exact hxy
    · have hyx : y < x := by grind
      have hstrict := eval_strictly_decreasing_of_nonpos_tail (a := a)
        htail htail_neg hy hyx
      exfalso
      grind
  · by_cases hyx : y ≤ x
    · exact hyx
    · have hxy : x < y := by grind
      have hstrict := eval_strictly_decreasing_of_nonpos_tail (a := a)
        htail htail_neg hx hxy
      exfalso
      grind

theorem signChangeCount_one_of_pos_cons_of_neg
    {a : Rat} {coeffs : List Rat}
    (ha : 0 < a)
    (hneg : ∀ c, c ∈ coeffs → c < 0)
    (hne : coeffs ≠ []) :
    signChangeCount (a :: coeffs) = 1 := by
  cases coeffs with
  | nil => exact False.elim (hne rfl)
  | cons b bs =>
      have hb : b < 0 := hneg b (by simp)
      have hrest : signChangeCount (b :: bs) = 0 := by
        apply signChangeCount_zero_of_nonpos
        intro c hc
        exact Rat.le_of_lt (hneg c (by simp [hc]))
      have hab : a * b < 0 := by
        exact (Rat.mul_neg_iff_of_pos_left ha).2 hb
      simp [signChangeCount, hrest, hab]

theorem signChangeCountIgnoringZeros_one_of_pos_cons_nonpos_tail
    {a : Rat} {tail : List Rat}
    (ha : 0 < a)
    (htail : ∀ c, c ∈ tail → c ≤ 0)
    (htail_neg : ∃ c, c ∈ tail ∧ c < 0) :
    signChangeCountIgnoringZeros (a :: tail) = 1 := by
  have ha0 : a ≠ 0 := Rat.ne_of_gt ha
  have hfiltered_nonempty : (tail.filter (fun c => c != 0)) ≠ [] := by
    intro hempty
    rcases htail_neg with ⟨c, hc, hcneg⟩
    have hc0 : c ≠ 0 := by intro h; grind
    have hmem : c ∈ tail.filter (fun d => d != 0) :=
      List.mem_filter.mpr ⟨hc, by simp [hc0]⟩
    rw [hempty] at hmem
    simp at hmem
  have hfiltered_neg : ∀ c, c ∈ tail.filter (fun c => c != 0) → c < 0 := by
    intro c hc
    have hc_tail : c ∈ tail := (List.mem_filter.mp hc).1
    have hc_nonpos := htail c hc_tail
    have hc0 : c ≠ 0 := by simpa using (List.mem_filter.mp hc).2
    grind
  simp [signChangeCountIgnoringZeros, ha0]
  exact signChangeCount_one_of_pos_cons_of_neg ha hfiltered_neg hfiltered_nonempty

/-- A packaged one-variation certificate: the supplied coefficient list has
exactly one sign change after zero removal, and it has at most one positive
rational root.  This is the reusable finite boundary of Descartes' rule used
by the project; no general real-root count is asserted. -/
theorem one_positive_variation_certificate
    {a : Rat} {tail : List Rat}
    (ha : 0 < a)
    (htail : ∀ c, c ∈ tail → c ≤ 0)
    (htail_neg : ∃ c, c ∈ tail ∧ c < 0) :
    signChangeCountIgnoringZeros (a :: tail) = 1 /\
      (∀ x y : Rat, 0 < x → 0 < y →
        eval (a :: tail) x = 0 → eval (a :: tail) y = 0 → x = y) := by
  constructor
  · exact signChangeCountIgnoringZeros_one_of_pos_cons_nonpos_tail
      ha htail htail_neg
  · intro x y hx hy hxroot hyroot
    exact at_most_one_positive_rational_root_of_nonpos_tail
      htail htail_neg hx hy hxroot hyroot

/-- A packaged zero-variation certificate: a coefficient list with no
negative entries has no sign changes after zero removal, and a strictly
positive supplied coefficient excludes every positive rational root. -/
theorem zero_variation_root_exclusion_certificate
    {coeffs : List Rat}
    (hcoeffs : ∀ c, c ∈ coeffs → 0 ≤ c)
    {c₀ : Rat} (hc₀ : c₀ ∈ coeffs) (hc₀pos : 0 < c₀) :
    signChangeCountIgnoringZeros coeffs = 0 /\
      (∀ x : Rat, 0 < x → eval coeffs x ≠ 0) := by
  constructor
  · exact signChangeCountIgnoringZeros_zero_of_nonneg_coeffs hcoeffs
  · intro x hx
    exact eval_ne_zero_of_nonneg_coeffs_of_pos hcoeffs hx hc₀ hc₀pos

/-! A degree-free combinatorial part of Descartes' rule: after zero
    coefficients are removed, each adjacent sign change consumes one edge of
    the finite coefficient list.  This is a reusable bound for arbitrary
    rational coefficient lists; it makes no assertion about roots. -/
private theorem signChangeCount_add_one_le_length
    {xs : List Rat} (hne : xs ≠ []) :
    signChangeCount xs + 1 <= xs.length := by
  induction xs with
  | nil => contradiction
  | cons a tail ih =>
      cases tail with
      | nil => simp [signChangeCount]
      | cons b tail =>
          have htail : b :: tail ≠ [] := by simp
          have hbound := ih htail
          by_cases hab : a * b < 0
          · change (if a * b < 0 then 1 else 0) +
              signChangeCount (b :: tail) + 1 <= (b :: tail).length + 1
            rw [if_pos hab]
            have hbound' := Nat.add_le_add_left hbound 1
            omega
          · change (if a * b < 0 then 1 else 0) +
              signChangeCount (b :: tail) + 1 <= (b :: tail).length + 1
            rw [if_neg hab]
            omega

theorem signChangeCountIgnoringZeros_add_one_le_filter_length
    {coeffs : List Rat}
    (hne : (coeffs.filter (fun c => c != 0)).length > 0) :
    signChangeCountIgnoringZeros coeffs + 1 <=
      (coeffs.filter (fun c => c != 0)).length := by
  unfold signChangeCountIgnoringZeros
  apply signChangeCount_add_one_le_length
  simp at hne ⊢
  omega

end Polynomial

end ComputableAnalysis
