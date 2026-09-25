import ComputableAnalysis.ComplexIntegralEnclosure
import ComputableAnalysis.Series

/-!
# The reciprocal on a vertical segment, by direct rectangles

Each recursive step bisects a geometric vertical chunk. The evaluator sums
its outer range rectangle multiplied by the upward displacement. Coordinates
label endpoints; no parametrized integral or logarithm value is used.
-/
namespace ComputableAnalysis.VerticalReciprocalIntegral

private def u (y : Rat) : Rat := y / (1+y*y)
private def v (y : Rat) : Rat := 1 / (1+y*y)

private theorem den_pos (y : Rat) : 0 < 1+y*y := by
  have h := rat_square_nonneg_basic y
  grind

private theorem v_antitone {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) : v b ≤ v a := by
  have hp := Rat.mul_nonneg (show 0 ≤ b-a by grind) (show 0 ≤ b+a by grind)
  have horder : 1+a*a ≤ 1+b*b := by grind
  have hi := Rat.le_of_lt ((Rat.inv_pos).2 (den_pos a))
  have hj := Rat.le_of_lt ((Rat.inv_pos).2 (den_pos b))
  have hm := Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_right horder hi) hj
  have hc := Rat.mul_inv_cancel (1+a*a) (Rat.ne_of_gt (den_pos a))
  have hd := Rat.mul_inv_cancel (1+b*b) (Rat.ne_of_gt (den_pos b))
  unfold v
  simp only [Rat.div_def, Rat.one_mul]
  grind only [Rat.mul_assoc, Rat.mul_comm]

private theorem u_monotone {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    u a ≤ u b := by
  have hprod := Rat.mul_le_mul_of_nonneg_left hb ha
  have hgap : 0 ≤ (b-a)*(1-a*b) :=
    Rat.mul_nonneg (by grind) (by grind)
  have hi := Rat.le_of_lt ((Rat.inv_pos).2 (den_pos a))
  have hj := Rat.le_of_lt ((Rat.inv_pos).2 (den_pos b))
  have hc := Rat.mul_inv_cancel (1+a*a) (Rat.ne_of_gt (den_pos a))
  have hd := Rat.mul_inv_cancel (1+b*b) (Rat.ne_of_gt (den_pos b))
  have horder : a*(1+b*b) ≤ b*(1+a*a) := by grind only
  have hm := Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_right horder hi) hj
  have hleft : a*(1+b*b)*(1+a*a)⁻¹*(1+b*b)⁻¹ = a*(1+a*a)⁻¹ := by
    calc
      _ = (a*(1+a*a)⁻¹)*((1+b*b)*(1+b*b)⁻¹) := by grind only
      _ = _ := by rw [hd, Rat.mul_one]
  have hright : b*(1+a*a)*(1+a*a)⁻¹*(1+b*b)⁻¹ = b*(1+b*b)⁻¹ := by
    calc
      _ = (b*((1+a*a)*(1+a*a)⁻¹))*(1+b*b)⁻¹ := by grind only
      _ = _ := by rw [hc, Rat.mul_one]
  rw [hleft,hright] at hm
  exact hm

/-- Reciprocal values on the line whose real coordinate is one. -/
def valueAt (z : QComplex) : QComplex := ⟨v z.im, -u z.im⟩

/-- The outer value rectangle on a vertical chunk before rotation. -/
def range (a b : Rat) : QBox := ⟨⟨v b,-u b⟩,⟨v a,-u a⟩⟩

/-- Both coordinates are bounded on the whole geometric chunk. -/
theorem range_contains (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (z : QComplex) (_hre : z.re = 1) (hz : a ≤ z.im ∧ z.im ≤ b) :
    (range a b).lo ≤ valueAt z ∧ valueAt z ≤ (range a b).hi := by
  have h1 := v_antitone (a := a) (b := z.im) ha hz.1
  have h2 := v_antitone (a := z.im) (b := b) (by grind) hz.2
  have h3 := u_monotone (a := a) (b := z.im) ha hz.1 (by grind)
  have h4 := u_monotone (a := z.im) (b := b) (by grind) hz.2 hb
  simp only [range,valueAt,QComplex.le_def]
  constructor <;> constructor <;> grind only

/-- The chosen value is the reciprocal, proved by multiplication. -/
theorem valueAt_reciprocal (z : QComplex) (hz : z.re = 1) :
    QComplex.mul z (valueAt z) = QComplex.one := by
  have hc := Rat.mul_inv_cancel (1+z.im*z.im) (Rat.ne_of_gt (den_pos z.im))
  simp only [QComplex.mul,valueAt,u,v,QComplex.one,hz,Rat.div_def,QComplex.mk.injEq]
  constructor <;> grind

/-- The chunk contribution after rotation and multiplication by its length. -/
def chunk (a b : Rat) : QBox :=
  ⟨⟨(b-a)*u a,(b-a)*v b⟩,⟨(b-a)*u b,(b-a)*v a⟩⟩

theorem chunk_eq_scaled_range (a b : Rat) (hab : a ≤ b) :
    chunk a b = QBox.scaleRat (b-a) (ComplexPathIntegral.rotateRange (range a b)) := by
  simp [QBox.scaleRat, show 0 ≤ b-a by grind, chunk,
    ComplexPathIntegral.rotateRange, range] <;> grind

/-- Every reciprocal value on the chunk, multiplied by the actual geometric
increment, lies in its contribution rectangle. -/
theorem chunk_contains (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (z : QComplex) (hre : z.re = 1) (hz : a ≤ z.im ∧ z.im ≤ b) :
    (chunk a b).lo ≤ QComplex.mul (valueAt z) (QComplex.sub ⟨1,b⟩ ⟨1,a⟩) ∧
    QComplex.mul (valueAt z) (QComplex.sub ⟨1,b⟩ ⟨1,a⟩) ≤ (chunk a b).hi := by
  have h1 := u_monotone ha hz.1 (by grind)
  have h2 := u_monotone (by grind : 0 ≤ z.im) hz.2 hb
  have h3 := v_antitone ha hz.1
  have h4 := v_antitone (by grind : 0 ≤ z.im) hz.2
  have hlen : 0 ≤ b-a := by grind
  have h1' := Rat.mul_le_mul_of_nonneg_left h1 hlen
  have h2' := Rat.mul_le_mul_of_nonneg_left h2 hlen
  have h3' := Rat.mul_le_mul_of_nonneg_left h3 hlen
  have h4' := Rat.mul_le_mul_of_nonneg_left h4 hlen
  simp only [chunk,valueAt,QComplex.mul,QComplex.sub,QComplex.add,
    QComplex.neg,QComplex.le_def]
  constructor <;> constructor <;> grind only

/-- Direct dyadic subdivision and addition of contribution rectangles. -/
def boxes : Nat → Rat → Rat → QBox
  | 0,a,b => chunk a b
  | n+1,a,b => QBox.add (boxes n a ((a+b)/2)) (boxes n ((a+b)/2) b)

private theorem add_nested {A B C D : QBox}
    (hA : A.NestedIn B) (hC : C.NestedIn D) :
    (QBox.add A C).NestedIn (QBox.add B D) := by
  simp only [QBox.NestedIn,QBox.add,QComplex.add,QComplex.le_def] at *
  constructor <;> constructor <;> grind only

private theorem step_nested (n : Nat) (a b : Rat)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (boxes (n+1) a b).NestedIn (boxes n a b) := by
  induction n generalizing a b with
  | zero =>
    let m := (a+b)/2
    have ham : a ≤ m := by dsimp [m]; grind
    have hmb : m ≤ b := by dsimp [m]; grind
    have h1 := u_monotone ha ham (by grind)
    have h2 := u_monotone (by grind : 0 ≤ m) hmb hb
    have h3 := v_antitone ha ham
    have h4 := v_antitone (by grind : 0 ≤ m) hmb
    have hu1 := Rat.mul_le_mul_of_nonneg_left h1 (show 0 ≤ b-m by grind)
    have hu2 := Rat.mul_le_mul_of_nonneg_left h2 (show 0 ≤ m-a by grind)
    have hv1 := Rat.mul_le_mul_of_nonneg_left h3 (show 0 ≤ b-m by grind)
    have hv2 := Rat.mul_le_mul_of_nonneg_left h4 (show 0 ≤ m-a by grind)
    simp only [boxes,chunk,QBox.NestedIn,QBox.add,QComplex.add,QComplex.le_def]
    change ((b-a)*u a ≤ (m-a)*u a+(b-m)*u m ∧
      (b-a)*v b ≤ (m-a)*v m+(b-m)*v b) ∧
      ((m-a)*u m+(b-m)*u b ≤ (b-a)*u b ∧
      (m-a)*v a+(b-m)*v m ≤ (b-a)*v a)
    constructor <;> constructor <;> grind only
  | succ n ih =>
    exact add_nested (ih a ((a+b)/2) ha (by grind) (by grind))
      (ih ((a+b)/2) b (by grind) (by grind) hb)

private theorem widths (n : Nat) (a b : Rat) :
    (boxes n a b).width = (b-a)*(1/2 : Rat)^n*(u b-u a) ∧
    (boxes n a b).height = (b-a)*(1/2 : Rat)^n*(v a-v b) := by
  induction n generalizing a b with
  | zero => simp [boxes,chunk,QBox.width,QBox.height] <;> constructor <;> grind
  | succ n ih =>
    have hl := ih a ((a+b)/2)
    have hr := ih ((a+b)/2) b
    simp only [boxes,QBox.width,QBox.height,QBox.add,QComplex.add,Rat.pow_succ] at *
    constructor <;> grind

/-- Explicit coordinate errors for the unit vertical segment. -/
theorem unit_widths (n : Nat) :
    (boxes n 0 1).width = (1/2 : Rat)^(n+1) ∧
    (boxes n 0 1).height = (1/2 : Rat)^(n+1) := by
  have h := widths n 0 1
  have h0u : u 0 = 0 := by native_decide
  have h0v : v 0 = 1 := by native_decide
  have h1u : u 1 = 1/2 := by native_decide
  have h1v : v 1 = 1/2 := by native_decide
  rw [h0u,h0v,h1u,h1v] at h
  rw [Rat.pow_succ]
  constructor <;> grind

/-- The integral value is computed solely from the reciprocal's rectangles. -/
def raw : ComplexRaw where
  compute n := boxes n 0 1

theorem raw_valid : raw.Valid := by
  have hpow : ∀ n : Nat, 0 ≤ (1/2 : Rat)^n := by
    intro n
    induction n with
    | zero => simpa only [Rat.pow_zero] using (show (0 : Rat) ≤ 1 by decide)
    | succ n ih => rw [Rat.pow_succ]; exact Rat.mul_nonneg ih (by native_decide)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have h := unit_widths n
    exact ⟨h.1 ▸ hpow (n+1), h.2 ▸ hpow (n+1)⟩
  · intro n m hnm
    have nest : (boxes m 0 1).NestedIn (boxes n 0 1) := by
      induction m with
      | zero =>
        have hn : n=0 := by omega
        subst n
        exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩
      | succ m ih =>
        by_cases hm : n ≤ m
        · have h1 := ih hm
          have h2 := step_nested m 0 1 (by decide) (by decide) (by decide)
          simp only [QBox.NestedIn,QComplex.le_def] at *
          constructor <;> constructor <;> grind only
        · have hn : n=m+1 := by omega
          subst n
          exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩
    exact ⟨nest.1.1,nest.2.1,nest.1.2,nest.2.2⟩
  · have hs : ShrinksToZero (fun n => (1/2 : Rat)^(n+1)) := by
      apply shrinksToZero_of_natOverSuccBound (C := 1)
      intro n
      have h := Series.half_pow_le_one_div_succ (n+1)
      have h2 := Series.half_pow_le_one_div_succ n
      have hp := hpow n
      rw [Rat.pow_succ]
      grind
    intro eps
    obtain ⟨N,hN⟩ := hs eps
    refine ⟨N,?_⟩
    intro n hn
    have h := unit_widths n
    exact ⟨h.1 ▸ hN n hn,h.2 ▸ hN n hn⟩

end ComputableAnalysis.VerticalReciprocalIntegral
