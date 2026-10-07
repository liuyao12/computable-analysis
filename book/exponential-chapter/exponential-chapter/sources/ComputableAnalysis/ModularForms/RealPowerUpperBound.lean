import ComputableAnalysis.ModularForms.RealPowerLowerBound
import ComputableAnalysis.ModularForms.RealExponentialTwoUpperBound

/-! Exact upper bounds for actual represented nonnegative finite powers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

private theorem clipped_power_nonnegative (x : RealRaw) (hx : x.Valid)
    (hl : (RealRaw.ofRat 0).Le x) (n k : Nat) :
    0≤((realFinitePower (RealRaw.lowerClip x 0) n).compute k).lo := by
  have hv := RealRaw.lowerClip_valid x 0 hx (fun j => hl 0 j)
  have hc : 0≤((RealRaw.lowerClip x 0).compute k).lo := by
    change 0≤maxRat2 (x.compute k).lo 0
    unfold maxRat2
    split <;> grind only
  induction n with
  | zero => change (0:Rat)≤1; decide +kernel
  | succ n ih =>
    have hp := QBox.mulRealInterval_of_nonneg ih
      (RealRaw.interval_order_of_valid _ (realFinitePower_valid _ hv n) k) hc
      (RealRaw.interval_order_of_valid _ hv k)
    change 0≤(QBox.mulRealInterval ((realFinitePower (RealRaw.lowerClip x 0) n).compute k).lo
      ((realFinitePower (RealRaw.lowerClip x 0) n).compute k).hi
      ((RealRaw.lowerClip x 0).compute k).lo ((RealRaw.lowerClip x 0).compute k).hi).lo
    rw [hp]
    exact Rat.mul_nonneg ih hc

/-- Arbitrary valid represented nonnegative inputs bounded by a rational
have actual finite powers bounded by the corresponding rational power. -/
theorem realFinitePower_upper (x : RealRaw) (hx : x.Valid) (a : Rat) (ha : 0≤a)
    (hl : (RealRaw.ofRat 0).Le x) (hu : x.Le (RealRaw.ofRat a)) (n : Nat) :
    (realFinitePower x n).Le (RealRaw.ofRat (a^n)) := by
  let c := RealRaw.lowerClip x 0
  have hc : c.Valid := RealRaw.lowerClip_valid x 0 hx (fun j => hl 0 j)
  have he : c.Equiv x := lowerClip_equiv x hx 0 hl
  have hup : c.Le (RealRaw.ofRat a) := RealRaw.le_trans hx
    (RealRaw.le_of_equiv hc hx he) hu
  have hnonneg (k : Nat) : 0≤(c.compute k).lo := by
    change 0≤maxRat2 (x.compute k).lo 0
    unfold maxRat2
    split <;> grind only
  have hbound (k : Nat) : ∀ n, ((realFinitePower c n).compute k).lo≤a^n := by
    intro n
    induction n with
    | zero => change (1:Rat)≤a^0; rw [Rat.pow_zero]; exact Rat.le_refl
    | succ n ih =>
      have hn := clipped_power_nonnegative x hx hl n k
      have hp := QBox.mulRealInterval_of_nonneg hn
        (RealRaw.interval_order_of_valid _ (realFinitePower_valid _ hc n) k) (hnonneg k)
        (RealRaw.interval_order_of_valid _ hc k)
      have hupper := hup k 0
      change (c.compute k).lo≤a at hupper
      change (QBox.mulRealInterval ((realFinitePower c n).compute k).lo ((realFinitePower c n).compute k).hi
        (c.compute k).lo (c.compute k).hi).lo≤a^(n+1)
      rw [hp,Rat.pow_succ]
      have h1 := Rat.mul_le_mul_of_nonneg_right ih (hnonneg k)
      have h2 := Rat.mul_le_mul_of_nonneg_left hupper (Rat.pow_nonneg (n := n) ha)
      exact Rat.le_trans h1 h2
  have hp : (realFinitePower c n).Equiv (realFinitePower x n) := by
    induction n with
    | zero => exact RealRaw.equiv_refl _ (RealRaw.ofRat_valid 1)
    | succ n ih => exact RealRaw.mul_equiv (realFinitePower_valid _ hc n) (realFinitePower_valid _ hx n) hc hx ih he
  have hb : (realFinitePower c n).Le (RealRaw.ofRat (a^n)) := by
    intro i j
    exact hbound i n
  exact RealRaw.le_trans (realFinitePower_valid _ hc n)
    (RealRaw.le_of_equiv (realFinitePower_valid _ hx n) (realFinitePower_valid _ hc n) (RealRaw.equiv_symm hp)) hb

end ComputableAnalysis.ModularForms
