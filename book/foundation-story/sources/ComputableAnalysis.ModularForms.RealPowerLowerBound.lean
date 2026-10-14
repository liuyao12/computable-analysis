import ComputableAnalysis.ModularForms.PositiveReciprocalAgreement
import ComputableAnalysis.RiemannHilbert.LocalODESum

/-! Positive real-coordinate lower bounds for actual represented finite powers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

def realFinitePower (x : RealRaw) : Nat → RealRaw
  | 0 => RealRaw.one
  | n+1 => RealRaw.mul (realFinitePower x n) x

theorem realFinitePower_valid (x : RealRaw) (hx : x.Valid) (n : Nat) :
    (realFinitePower x n).Valid := by
  induction n with
  | zero => exact RealRaw.ofRat_valid 1
  | succ n ih => exact RealRaw.mul_valid ih hx

theorem realFinitePower_complex (x : RealRaw) (hx : x.Valid) (n : Nat) :
    (LocalODE.power (ofRealRaw x) n).Equiv (ofRealRaw (realFinitePower x n)) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih =>
    exact equiv_trans (LocalODE.power_valid _ (ofRealRaw_valid _ hx) (n+1))
      (mul_valid (ofRealRaw_valid _ (realFinitePower_valid x hx n)) (ofRealRaw_valid _ hx))
      (ofRealRaw_valid _ (realFinitePower_valid x hx (n+1)))
      (mul_equiv (LocalODE.power_valid _ (ofRealRaw_valid _ hx) n)
        (ofRealRaw_valid _ (realFinitePower_valid x hx n)) (ofRealRaw_valid _ hx) (ofRealRaw_valid _ hx)
        ih (equiv_refl _ (ofRealRaw_valid _ hx)))
      (real_embedding_mul _ _ (realFinitePower_valid x hx n) hx)

private theorem clippedPower_lower (x : RealRaw) (hx : x.Valid) (a : Rat) (ha : 0≤a)
    (hl : (RealRaw.ofRat a).Le x) (n k : Nat) :
    a^n ≤ ((realFinitePower (RealRaw.lowerClip x a) n).compute k).lo := by
  have hclip (j : Nat) : a ≤ ((RealRaw.lowerClip x a).compute j).lo := by
    change a ≤ maxRat2 (x.compute j).lo a
    unfold maxRat2
    split <;> grind only
  have hv := RealRaw.lowerClip_valid x a hx (fun j => hl 0 j)
  induction n with
  | zero => change a^0 ≤ (1:Rat); rw [Rat.pow_zero]; exact Rat.le_refl
  | succ n ih =>
    have hp := Rat.pow_nonneg (n := n) ha
    have ho := RealRaw.interval_order_of_valid _ (realFinitePower_valid _ hv n) k
    have hc := RealRaw.interval_order_of_valid _ hv k
    have hb := QBox.mulRealInterval_of_nonneg (Rat.le_trans hp ih) ho
      (Rat.le_trans ha (hclip k)) hc
    change a^(n+1) ≤ (QBox.mulRealInterval
      ((realFinitePower (RealRaw.lowerClip x a) n).compute k).lo
      ((realFinitePower (RealRaw.lowerClip x a) n).compute k).hi
      ((RealRaw.lowerClip x a).compute k).lo ((RealRaw.lowerClip x a).compute k).hi).lo
    rw [hb,Rat.pow_succ]
    exact rat_mul_le_mul_of_nonneg hp ih ha (hclip k)

theorem realFinitePower_lower (x : RealRaw) (hx : x.Valid) (a : Rat) (ha : 0≤a)
    (hl : (RealRaw.ofRat a).Le x) (n : Nat) :
    (RealRaw.ofRat (a^n)).Le (realFinitePower x n) := by
  have hv := RealRaw.lowerClip_valid x a hx (fun k => hl 0 k)
  have he : (realFinitePower (RealRaw.lowerClip x a) n).Equiv (realFinitePower x n) := by
    induction n with
    | zero => exact RealRaw.equiv_refl _ (RealRaw.ofRat_valid 1)
    | succ n ih =>
      exact RealRaw.mul_equiv (realFinitePower_valid _ hv n) (realFinitePower_valid _ hx n)
        hv hx ih (lowerClip_equiv x hx a hl)
  have hb : (RealRaw.ofRat (a^n)).Le (realFinitePower (RealRaw.lowerClip x a) n) := by
    intro i j
    exact Rat.le_trans (clippedPower_lower x hx a ha hl n j)
      (RealRaw.interval_order_of_valid _ (realFinitePower_valid _ hv n) j)
  exact RealRaw.le_trans (realFinitePower_valid _ hv n) hb
    (RealRaw.le_of_equiv (realFinitePower_valid _ hv n) (realFinitePower_valid _ hx n) he)

end ComputableAnalysis.ModularForms
