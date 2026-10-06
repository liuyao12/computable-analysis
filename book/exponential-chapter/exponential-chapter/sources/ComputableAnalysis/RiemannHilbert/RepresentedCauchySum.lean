import ComputableAnalysis.RiemannHilbert.PrecisionSearch
import ComputableAnalysis.Holomorphic
import ComputableAnalysis.PowerSeries

/-!
# Constructing a represented limit from finite Cauchy estimates

The runtime computes finite prefix values, searches for narrow rational boxes,
and intersects widened sample boxes. A finite comparison theorem certifies
the value's role as a sum; no completed scalar or pre-existing limit is used.
-/
namespace ComputableAnalysis.RiemannHilbert.RepresentedCauchySum

open ComplexRaw FunctionTheory

/-- A sample from a narrow box can be compared with any box of another value
using an exact bound on their represented difference. -/
theorem center_vs_box (z w : ComplexRaw) (hz : z.Valid) (hw : w.Valid)
    (B eps : Rat) (h : Small (sub z w) B) (i j : Nat)
    (hwidth : (z.compute i).width ≤ eps) (hheight : (z.compute i).height ≤ eps) :
    (z.compute i).center.re - (w.compute j).hi.re ≤ B+eps ∧
    (w.compute j).lo.re - (z.compute i).center.re ≤ B+eps ∧
    (z.compute i).center.im - (w.compute j).hi.im ≤ B+eps ∧
    (w.compute j).lo.im - (z.compute i).center.im ≤ B+eps := by
  let t := max i j
  have hnz := hz.2.1 i t (Nat.le_max_left _ _)
  have hnw := hw.2.1 j t (Nat.le_max_right _ _)
  have hc := QBox.center_mem (valid_ordered hz i)
  have h1 := h.1 0 t
  have h2 := h.2.1 t 0
  have h3 := h.2.2.1 0 t
  have h4 := h.2.2.2 t 0
  change -B ≤ (z.compute t).hi.re + -(w.compute t).lo.re at h1
  change (z.compute t).lo.re + -(w.compute t).hi.re ≤ B at h2
  change -B ≤ (z.compute t).hi.im + -(w.compute t).lo.im at h3
  change (z.compute t).lo.im + -(w.compute t).hi.im ≤ B at h4
  unfold QBox.width at hwidth
  unfold QBox.height at hheight
  rcases hc with ⟨⟨hc1,hc2⟩,⟨hc3,hc4⟩⟩
  rcases hnz with ⟨hz1,hz2,hz3,hz4⟩
  rcases hnw with ⟨hw1,hw2,hw3,hw4⟩
  exact ⟨by grind [Rat.sub_eq_add_neg], by grind [Rat.sub_eq_add_neg], by grind [Rat.sub_eq_add_neg], by grind [Rat.sub_eq_add_neg]⟩

theorem centers_close (z w : ComplexRaw) (hz : z.Valid) (hw : w.Valid)
    (B eps eta : Rat) (h : Small (sub z w) B) (i j : Nat)
    (hzw : (z.compute i).width ≤ eps) (hzh : (z.compute i).height ≤ eps)
    (hww : (w.compute j).width ≤ eta) (hwh : (w.compute j).height ≤ eta) :
    (QBox.point (z.compute i).center).NestedIn
      (QBox.expand (QBox.point (w.compute j).center) (B+eps+eta)) := by
  have hc := center_vs_box z w hz hw B eps h i j hzw hzh
  have hwc := QBox.center_mem (valid_ordered hw j)
  rcases hc with ⟨h1,h2,h3,h4⟩
  rcases hwc with ⟨⟨hw1,hw2⟩,⟨hw3,hw4⟩⟩
  unfold QBox.width at hww
  unfold QBox.height at hwh
  simp only [QBox.NestedIn, QBox.point, QBox.expand, QComplex.le_def]
  exact ⟨⟨by grind [Rat.sub_eq_add_neg], by grind [Rat.sub_eq_add_neg]⟩,⟨by grind [Rat.sub_eq_add_neg], by grind [Rat.sub_eq_add_neg]⟩⟩

def error (n : Nat) : QPos :=
  ⟨1 / ((n+1 : Nat) : Rat), by
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.succ_pos n))⟩

theorem error_antitone (k n : Nat) (h : k ≤ n) : (error n).val ≤ (error k).val := by
  apply QInterval.one_div_le_one_div_of_pos
    ((Rat.natCast_pos).2 (Nat.succ_pos k))
  exact_mod_cast Nat.succ_le_succ h

theorem error_shrinks : ShrinksToZero (fun n => (error n).val) := by
  apply shrinksToZero_of_natOverSuccBound (C := 1)
  intro n
  exact Rat.le_refl

def sample (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid) (n : Nat) : QComplex :=
  ((p n).compute (PrecisionSearch.stage (p n) (hp n) (error n))).center

def candidate (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid) : ComplexRaw where
  compute n := QBox.point (sample p hp n)

def radius (tail : Nat → Rat) (n : Nat) : Rat := tail n + 2*(error n).val

/-- Executable represented limit; its mathematical certificates are the
subsequent validity and prefix-agreement theorems. -/
def value (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid)
    (tail : Nat → Rat) : ComplexRaw :=
  cauchyStabilize (candidate p hp) (radius tail)

theorem candidate_future (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid)
    (tail : Nat → Rat)
    (hc : ∀ k n, k ≤ n → Small (sub (p n) (p k)) (tail k))
    (k n : Nat) (hkn : k ≤ n) :
    ((candidate p hp).compute n).NestedIn
      (QBox.expand ((candidate p hp).compute k) (radius tail k)) := by
  have hn := PrecisionSearch.stage_spec (p n) (hp n) (error n)
  have hk := PrecisionSearch.stage_spec (p k) (hp k) (error k)
  have h := centers_close (p n) (p k) (hp n) (hp k) (tail k)
    (error n).val (error k).val (hc k n hkn)
    (PrecisionSearch.stage (p n) (hp n) (error n))
    (PrecisionSearch.stage (p k) (hp k) (error k)) hn.1 hn.2 hk.1 hk.2
  apply QBox.nested_trans h
  apply QBox.expand_mono_radius
  have he := error_antitone k n hkn
  unfold radius
  grind

theorem radius_shrinks (tail : Nat → Rat) (ht : ShrinksToZero tail) :
    ShrinksToZero (radius tail) := by
  intro eps
  let half : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  let quarter : QPos := ⟨eps.val/4, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨Nt,hNt⟩ := ht half
  obtain ⟨Ne,hNe⟩ := error_shrinks quarter
  refine ⟨max Nt Ne, ?_⟩
  intro n hn
  have h1 := hNt n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have h2 := hNe n (Nat.le_trans (Nat.le_max_right _ _) hn)
  dsimp [half, quarter] at h1 h2
  unfold radius
  grind [Rat.div_def, Rat.mul_inv_cancel, Rat.mul_assoc]

theorem value_valid (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid)
    (tail : Nat → Rat) (ht : ShrinksToZero tail)
    (hc : ∀ k n, k ≤ n → Small (sub (p n) (p k)) (tail k)) :
    (value p hp tail).Valid := by
  apply cauchyStabilize_valid (fun _ => QComplex.le_refl _) ?_
    (candidate_future p hp tail hc) (radius_shrinks tail ht)
  intro eps
  exact ⟨0, fun n _ => by
    simp only [candidate, QBox.point, QBox.width, QBox.height]
    have h := eps.property
    constructor <;> grind⟩

/-- Rational order is closed under explicitly shrinking rational errors.
This finite contradiction does not invoke a completed ordered field. -/
theorem le_of_eventual_error (a b : Rat) (L : Nat)
    (h : ∀ n, L ≤ n → a ≤ b+(error n).val) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have hgap : 0 < a-b := by grind [Rat.sub_eq_add_neg]
    let eps : QPos := ⟨(a-b)/2, by
      rw [Rat.div_def]; exact Rat.mul_pos hgap ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨N,hN⟩ := error_shrinks eps
    have he := hN (max N L) (Nat.le_max_left _ _)
    have ha := h (max N L) (Nat.le_max_right _ _)
    dsimp [eps] at he
    have hhalf : (a-b)/2 < a-b := by
      rw [Rat.div_lt_iff (by decide : (0 : Rat) < 2)]
      grind [Rat.sub_eq_add_neg]
    grind [Rat.sub_eq_add_neg]

/-- The constructed value agrees with each prefix up to its supplied tail
bound. Thus validity is connected to the intended limit semantics. -/
theorem value_close_prefix (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid)
    (tail : Nat → Rat)
    (hc : ∀ k n, k ≤ n → Small (sub (p n) (p k)) (tail k)) (N : Nat) :
    Small (sub (value p hp tail) (p N)) (tail N) := by
  have hf := candidate_future p hp tail hc
  have hs : ∀ m n, m ≤ n →
      (QBox.point (sample p hp n)).NestedIn ((value p hp tail).compute m) :=
    cauchyStabilize_contains_external hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i m
    change -(tail N) ≤ ((value p hp tail).compute m).hi.re + -((p N).compute m).lo.re
    have hh : ((p N).compute m).lo.re - ((value p hp tail).compute m).hi.re ≤ tail N := by
      apply le_of_eventual_error _ _ (max m N)
      intro n hn
      have hm : m ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hN : N ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
      have hb := hs m n hm
      have he := PrecisionSearch.stage_spec (p n) (hp n) (error n)
      have hd := center_vs_box (p n) (p N) (hp n) (hp N) (tail N) (error n).val
        (hc N n hN) (PrecisionSearch.stage (p n) (hp n) (error n)) m he.1 he.2
      simp only [QBox.NestedIn, QBox.point, QComplex.le_def] at hb
      dsimp [sample] at hb
      grind [Rat.sub_eq_add_neg]
    grind [Rat.sub_eq_add_neg]
  · intro m i
    change ((value p hp tail).compute m).lo.re + -((p N).compute m).hi.re ≤ tail N
    apply le_of_eventual_error _ _ (max m N)
    intro n hn
    have hb := hs m n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have he := PrecisionSearch.stage_spec (p n) (hp n) (error n)
    have hd := center_vs_box (p n) (p N) (hp n) (hp N) (tail N) (error n).val
      (hc N n (Nat.le_trans (Nat.le_max_right _ _) hn))
      (PrecisionSearch.stage (p n) (hp n) (error n)) m he.1 he.2
    simp only [QBox.NestedIn, QBox.point, QComplex.le_def] at hb
    dsimp [sample] at hb
    grind [Rat.sub_eq_add_neg]
  · intro i m
    change -(tail N) ≤ ((value p hp tail).compute m).hi.im + -((p N).compute m).lo.im
    have hh : ((p N).compute m).lo.im - ((value p hp tail).compute m).hi.im ≤ tail N := by
      apply le_of_eventual_error _ _ (max m N)
      intro n hn
      have hb := hs m n (Nat.le_trans (Nat.le_max_left _ _) hn)
      have he := PrecisionSearch.stage_spec (p n) (hp n) (error n)
      have hd := center_vs_box (p n) (p N) (hp n) (hp N) (tail N) (error n).val
        (hc N n (Nat.le_trans (Nat.le_max_right _ _) hn))
        (PrecisionSearch.stage (p n) (hp n) (error n)) m he.1 he.2
      simp only [QBox.NestedIn, QBox.point, QComplex.le_def] at hb
      dsimp [sample] at hb
      grind [Rat.sub_eq_add_neg]
    grind [Rat.sub_eq_add_neg]
  · intro m i
    change ((value p hp tail).compute m).lo.im + -((p N).compute m).hi.im ≤ tail N
    apply le_of_eventual_error _ _ (max m N)
    intro n hn
    have hb := hs m n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have he := PrecisionSearch.stage_spec (p n) (hp n) (error n)
    have hd := center_vs_box (p n) (p N) (hp n) (hp N) (tail N) (error n).val
      (hc N n (Nat.le_trans (Nat.le_max_right _ _) hn))
      (PrecisionSearch.stage (p n) (hp n) (error n)) m he.1 he.2
    simp only [QBox.NestedIn, QBox.point, QComplex.le_def] at hb
    dsimp [sample] at hb
    grind [Rat.sub_eq_add_neg]

theorem small_sub_symm (z w : ComplexRaw) (B : Rat)
    (h : Small (sub z w) B) : Small (sub w z) B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i n
    have hh := h.2.1 n i
    change (z.compute n).lo.re + -(w.compute n).hi.re ≤ B at hh
    change -B ≤ (w.compute n).hi.re + -(z.compute n).lo.re
    grind
  · intro n i
    have hh := h.1 i n
    change -B ≤ (z.compute n).hi.re + -(w.compute n).lo.re at hh
    change (w.compute n).lo.re + -(z.compute n).hi.re ≤ B
    grind
  · intro i n
    have hh := h.2.2.2 n i
    change (z.compute n).lo.im + -(w.compute n).hi.im ≤ B at hh
    change -B ≤ (w.compute n).hi.im + -(z.compute n).lo.im
    grind
  · intro n i
    have hh := h.2.2.1 i n
    change -B ≤ (z.compute n).hi.im + -(w.compute n).lo.im at hh
    change (w.compute n).lo.im + -(z.compute n).hi.im ≤ B
    grind

theorem twice_shrinks (e : Nat → Rat) (he : ShrinksToZero e) :
    ShrinksToZero (fun n => 2*e n) := by
  intro eps
  let half : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨N,hN⟩ := he half
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  dsimp [half] at h
  grind [Rat.div_def, Rat.mul_inv_cancel, Rat.mul_assoc]

theorem sum_shrinks (e f : Nat → Rat) (he : ShrinksToZero e) (hf : ShrinksToZero f) :
    ShrinksToZero (fun n => e n+f n) := by
  intro eps
  let half : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨N,hN⟩ := he half
  obtain ⟨M,hM⟩ := hf half
  refine ⟨max N M, ?_⟩
  intro n hn
  have h := hN n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have k := hM n (Nat.le_trans (Nat.le_max_right _ _) hn)
  dsimp [half] at h k
  grind [Rat.div_def, Rat.mul_inv_cancel, Rat.mul_assoc]

theorem le_of_shrinking_error (e : Nat → Rat) (he : ShrinksToZero e) (a b : Rat)
    (h : ∀ n, a ≤ b+e n) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have hg : 0 < a-b := by grind
    let eps : QPos := ⟨(a-b)/2, by
      rw [Rat.div_def]; exact Rat.mul_pos hg ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨N,hN⟩ := he eps
    have hn := hN N (Nat.le_refl _)
    have hh := h N
    dsimp [eps] at hn
    have hhalf : (a-b)/2 < a-b := by
      rw [Rat.div_lt_iff (by decide : (0 : Rat) < 2)]
      grind
    grind

private theorem box_le_of_prefixes (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid)
    (tail : Nat → Rat) (ht : ShrinksToZero tail) (z w : ComplexRaw)
    (hz : z.Valid) (hw : w.Valid)
    (hZ : ∀ N, Small (sub z (p N)) (tail N))
    (hW : ∀ N, Small (sub w (p N)) (tail N)) (m : Nat) :
    (z.compute m).lo ≤ (w.compute m).hi := by
  have hr := radius_shrinks (fun n => 2*tail n) (twice_shrinks tail ht)
  have hb (N : Nat) := PrecisionSearch.stage_spec (p N) (hp N) (error N)
  have hdZ (N : Nat) := center_vs_box (p N) z (hp N) hz (tail N) (error N).val
    (small_sub_symm z (p N) (tail N) (hZ N))
    (PrecisionSearch.stage (p N) (hp N) (error N)) m (hb N).1 (hb N).2
  have hdW (N : Nat) := center_vs_box (p N) w (hp N) hw (tail N) (error N).val
    (small_sub_symm w (p N) (tail N) (hW N))
    (PrecisionSearch.stage (p N) (hp N) (error N)) m (hb N).1 (hb N).2
  constructor
  · apply le_of_shrinking_error _ hr
    intro N
    have h1 := (hdZ N).2.1
    have h2 := (hdW N).1
    unfold radius
    grind [Rat.sub_eq_add_neg]
  · apply le_of_shrinking_error _ hr
    intro N
    have h1 := (hdZ N).2.2.2
    have h2 := (hdW N).2.2.1
    unfold radius
    grind [Rat.sub_eq_add_neg]

/-- Uniqueness follows from finite prefix comparison and shrinking bounds;
it is not assumed in a limit certificate. -/
theorem unique (p : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid)
    (tail : Nat → Rat) (ht : ShrinksToZero tail) (z w : ComplexRaw)
    (hz : z.Valid) (hw : w.Valid)
    (hZ : ∀ N, Small (sub z (p N)) (tail N))
    (hW : ∀ N, Small (sub w (p N)) (tail N)) : z.Equiv w := by
  intro m
  apply (compareAt_overlap_iff z w m m).2
  exact ⟨box_le_of_prefixes p hp tail ht z w hz hw hZ hW m,
    box_le_of_prefixes p hp tail ht w z hw hz hW hZ m⟩

/-- Agreement survives changing both prefix implementations and the tail
schedule. Different numerical recipes are hidden behind value equality. -/
theorem value_congr (p q : Nat → ComplexRaw) (hp : ∀ n, (p n).Valid)
    (hq : ∀ n, (q n).Valid) (tail sigma : Nat → Rat)
    (ht : ShrinksToZero tail) (hs : ShrinksToZero sigma)
    (ht0 : ∀ n, 0 ≤ tail n) (hs0 : ∀ n, 0 ≤ sigma n)
    (hc : ∀ k n, k ≤ n → Small (sub (p n) (p k)) (tail k))
    (hd : ∀ k n, k ≤ n → Small (sub (q n) (q k)) (sigma k))
    (hpq : ∀ n, (p n).Equiv (q n)) :
    (value p hp tail).Equiv (value q hq sigma) := by
  apply unique p hp (fun n => tail n+sigma n) (sum_shrinks tail sigma ht hs)
    _ _ (value_valid p hp tail ht hc) (value_valid q hq sigma hs hd)
  · intro N
    exact (value_close_prefix p hp tail hc N).mono (by have := hs0 N; grind)
  · intro N
    have hclose := value_close_prefix q hq sigma hd N
    have hswap := Small.congr
      (sub_valid (value_valid q hq sigma hs hd) (hq N))
      (sub_valid (value_valid q hq sigma hs hd) (hp N))
      (FunctionTheory.sub_congr (equiv_refl _ (value_valid q hq sigma hs hd))
        (equiv_symm (hpq N))) hclose
    exact hswap.mono (by have := ht0 N; grind)

end ComputableAnalysis.RiemannHilbert.RepresentedCauchySum
