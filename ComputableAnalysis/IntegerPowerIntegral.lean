import ComputableAnalysis.IntegralRectangleSpecification

/-!
Function-specific compact and improper integrals for integer powers.
All computations and inequalities are rational; no completed real is imported.
The exponent domain in this module is explicitly integer, not represented-real.
-/
namespace ComputableAnalysis.IntegerPowerIntegral
open Integral

private theorem mul_left_comm (a b c : Rat) : a*(b*c)=b*(a*c) := by grind only

/-- Finite algebraic secant factor of the natural power. -/
def slope : Nat → Rat → Rat → Rat
  | 0, _, _ => 1
  | k+1, a, b => a^(k+1) + b*slope k a b

theorem power_difference (k : Nat) (a b : Rat) :
    b^(k+1)-a^(k+1) = (b-a)*slope k a b := by
  induction k with
  | zero => simp [slope, Rat.pow_succ]
  | succ k ih =>
    rw [slope, Rat.pow_succ b (k+1), Rat.pow_succ a (k+1)]
    grind only

theorem power_mono (k : Nat) {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    a^k ≤ b^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Rat.pow_succ, Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
      (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (Rat.le_trans ha hab)))

theorem slope_bounds (k : Nat) {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((k : Rat)+1)*a^k ≤ slope k a b ∧
      slope k a b ≤ ((k : Rat)+1)*b^k := by
  induction k with
  | zero => simp [slope]; constructor <;> grind
  | succ k ih =>
    have hb : 0 ≤ b := Rat.le_trans ha hab
    have hp := power_mono (k+1) ha hab
    have hl := Rat.mul_le_mul_of_nonneg_left ih.1 hb
    have hh := Rat.mul_le_mul_of_nonneg_left ih.2 hb
    have hk : 0 ≤ (k : Rat)+1 := by have := Rat.natCast_nonneg (a := k); grind
    have hz := Rat.mul_nonneg hk (Rat.pow_nonneg ha (n := k))
    have hx := Rat.mul_le_mul_of_nonneg_right hab hz
    simp only [slope, Rat.natCast_add, Rat.pow_succ]
    simp only [Rat.pow_succ] at hp
    constructor <;> grind only

/-- Independent reciprocal-power integrand. -/
def integrand (p : Nat) (x : Rat) : Rat := (x⁻¹)^p

/-- The proposed finite value for the exponent `k+2`. -/
def compact (k : Nat) (a b : Rat) : Rat :=
  ((a⁻¹)^(k+1)-(b⁻¹)^(k+1))/((k : Rat)+1)

theorem inverse_antitone {a b : Rat} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := (by grind : 0 < b)
  have hca := Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
  have hcb := Rat.mul_inv_cancel b (Rat.ne_of_gt hb)
  apply Rat.le_of_mul_le_mul_right (c := a*b) ?_ (Rat.mul_pos ha hb)
  calc
    b⁻¹*(a*b) = a := by grind only
    _ ≤ b := hab
    _ = a⁻¹*(a*b) := by grind only

theorem integrand_antitone (p : Nat) {a b : Rat} (ha : 0 < a) (hab : a ≤ b) :
    integrand p b ≤ integrand p a :=
  power_mono p (Rat.le_of_lt ((Rat.inv_pos).2 ((by grind : 0 < b))))
    (inverse_antitone ha hab)

/-- The finite cell theorem: endpoint rectangles enclose the proposed value. -/
theorem compact_cell_bounds (k : Nat) {a b : Rat} (ha : 0 < a) (hab : a ≤ b) :
    (b-a)*integrand (k+2) b ≤ compact k a b ∧
      compact k a b ≤ (b-a)*integrand (k+2) a := by
  have hb : 0 < b := (by grind : 0 < b)
  have hai : 0 < a⁻¹ := (Rat.inv_pos).2 ha
  have hbi : 0 < b⁻¹ := (Rat.inv_pos).2 hb
  have hc := slope_bounds k (Rat.le_of_lt hbi) (inverse_antitone ha hab)
  have hd := power_difference k b⁻¹ a⁻¹
  have hca := Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
  have hcb := Rat.mul_inv_cancel b (Rat.ne_of_gt hb)
  have hi : a⁻¹-b⁻¹=(b-a)*a⁻¹*b⁻¹ := by grind only
  have hgap : 0 ≤ a⁻¹-b⁻¹ := by have := inverse_antitone ha hab; grind
  have hl := Rat.mul_le_mul_of_nonneg_left hc.1 hgap
  have hu := Rat.mul_le_mul_of_nonneg_left hc.2 hgap
  have hmon := inverse_antitone ha hab
  have hlow := Rat.mul_le_mul_of_nonneg_right hmon
    (Rat.mul_nonneg (show 0 ≤ b-a by grind) (Rat.pow_nonneg (Rat.le_of_lt hbi) (n := k+1)))
  have hupp := Rat.mul_le_mul_of_nonneg_right hmon
    (Rat.mul_nonneg (show 0 ≤ b-a by grind) (Rat.pow_nonneg (Rat.le_of_lt hai) (n := k+1)))
  have hk : 0 < (k : Rat)+1 := by have := Rat.natCast_nonneg (a := k); grind
  have hck := Rat.mul_inv_cancel ((k : Rat)+1) (Rat.ne_of_gt hk)
  have hl' := Rat.mul_le_mul_of_nonneg_right hlow (Rat.le_of_lt hk)
  have hu' := Rat.mul_le_mul_of_nonneg_right hupp (Rat.le_of_lt hk)
  rw [hi] at hl hu hd
  simp only [Rat.pow_succ] at hd
  unfold integrand compact
  simp only [Rat.pow_succ] at hl' hu' ⊢
  have hcancel : (a⁻¹^k*a⁻¹-b⁻¹^k*b⁻¹)/((k : Rat)+1)*((k : Rat)+1) =
      a⁻¹^k*a⁻¹-b⁻¹^k*b⁻¹ := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.mul_comm ((k : Rat)+1)⁻¹, hck, Rat.mul_one]
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := (k : Rat)+1) ?_ hk
    rw [hcancel]
    calc
      _ ≤ a⁻¹*((b-a)*(b⁻¹^k*b⁻¹))*((k : Rat)+1) := by
        simpa only [Rat.mul_assoc, Rat.mul_comm, mul_left_comm] using hl'
      _ ≤ (b-a)*a⁻¹*b⁻¹*slope k b⁻¹ a⁻¹ := by
        simpa only [Rat.mul_assoc, Rat.mul_comm, mul_left_comm] using hl
      _ = _ := hd.symm
  · apply Rat.le_of_mul_le_mul_right (c := (k : Rat)+1) ?_ hk
    rw [hcancel, hd]
    calc
      _ ≤ (b-a)*a⁻¹*b⁻¹*(((k : Rat)+1)*a⁻¹^k) := hu
      _ ≤ a⁻¹*((b-a)*(a⁻¹^k*a⁻¹))*((k : Rat)+1) := by
        simpa only [Rat.mul_assoc, Rat.mul_comm, mul_left_comm] using hu'
      _ = _ := by grind only

/-- Whole-segment order evidence is constructed from the algebraic cell lemma. -/
theorem compact_order (k : Nat) {a b : Rat} (ha : 0 < a) :
    ExactCellOrderPreservation (integrand (k+2)) (compact k) a b where
  lower_const := by
    intro u v c hau huv _hc hf
    have h := (compact_cell_bounds k (show 0 < u by grind) huv).1
    have hh := Rat.mul_le_mul_of_nonneg_left (hf huv (Rat.le_refl)) (show 0 ≤ v-u by grind)
    exact Rat.le_trans hh h
  upper_const := by
    intro u v c hau huv _hc hf
    have h := (compact_cell_bounds k (show 0 < u by grind) huv).2
    have hh := Rat.mul_le_mul_of_nonneg_left (hf (Rat.le_refl) huv) (show 0 ≤ v-u by grind)
    exact Rat.le_trans h hh

/-- A semantic compact integral, not just validity of a proposed number. -/
theorem compact_hasIntegral (k : Nat) {a b : Rat} (ha : 0 < a) (hab : a ≤ b) :
    Integral.HasIntegral (FunctionOnInterval.exactRat (integrand (k+2)) a b)
      (RealRaw.ofRat (compact k a b)) := by
  have h : ExactCellOrderPreservation (integrand (k+2))
      (fun u v => -(v⁻¹)^(k+1)/((k : Rat)+1) - (-(u⁻¹)^(k+1)/((k : Rat)+1))) a b := by
    have he : (fun u v => -(v⁻¹)^(k+1)/((k : Rat)+1) - (-(u⁻¹)^(k+1)/((k : Rat)+1))) = compact k := by
      funext u v
      unfold compact
      simp only [Rat.div_def]
      grind only
    rw [he]
    exact compact_order k ha
  have ht := Integral.antitone_tight (integrand (k+2)) a b hab
    (fun x y hx hxy _hy => integrand_antitone (k+2) (by grind) hxy)
  have hr := Integral.ExactCellOrderPreservation.hasIntegral h ht
  have he : -(b⁻¹)^(k+1)/((k : Rat)+1) - (-(a⁻¹)^(k+1)/((k : Rat)+1)) = compact k a b := by
    unfold compact
    simp only [Rat.div_def]
    grind only
  rw [he] at hr
  exact hr

/-- The closed form applies to every valid name of the supplied integral. -/
theorem compact_exact (k : Nat) {a b : Rat} (ha : 0 < a) (hab : a ≤ b)
    {I : RealRaw}
    (hI : Integral.HasIntegral (FunctionOnInterval.exactRat (integrand (k+2)) a b) I) :
    I.Equiv (RealRaw.ofRat (compact k a b)) :=
  hI.unique (compact_hasIntegral k ha hab)

end ComputableAnalysis.IntegerPowerIntegral
