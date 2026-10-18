import ComputableAnalysis.ComputableCoefficientQuotient
import ComputableAnalysis.RepresentedPositiveSquareRoot
import ComputableAnalysis.BracketDerivativeConstruction

/-!
# Measurement-free Coulomb coupling

The input is the dimensionless squared coupling \(u=\alpha^2\), with
\(0\le u<1\). No value of \(\alpha\), mass, charge, or speed is measured or
inserted. Finite rational separation supplies an internal upper bound below
one. Positive square-root charts derive their bounds and margins from it;
callers do not select a precision, root bracket, or chart.
-/
namespace ComputableAnalysis.HydrogenCoupling
open ComputableCoefficient RepresentedPositiveSquareRoot

structure Coupling where
  squared : Real
  nonnegative : (RealRaw.ofRat 0).Le squared.preferred
  le_one : squared.preferred.Le (RealRaw.ofRat 1)
  ne_one : ¬ squared.preferred.Equiv (RealRaw.ofRat 1)

namespace Coupling

def gap (A : Coupling) : Value := Value.sub (Value.rational 1) (Value.parameter A.squared)

theorem gap_nonzero (A : Coupling) : ¬ A.gap.real.preferred.Equiv RealRaw.zero := by
  intro h
  apply A.ne_one
  intro n
  have hh := (RealRaw.compareAt_overlap_iff _ _ n n).1 (h n)
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change 1 + -(A.squared.compute n).hi ≤ 0 ∧ 0 ≤ 1 + -(A.squared.compute n).lo at hh
  change (A.squared.compute n).lo ≤ 1 ∧ 1 ≤ (A.squared.compute n).hi
  constructor <;> grind only

def separation (A : Coupling) : Nat := apartStage A.gap.real A.gap_nonzero

theorem separation_pos (A : Coupling) : 0 < (A.gap.real.compute A.separation).lo := by
  have h := apartStage_spec A.gap.real A.gap_nonzero
  have hb := A.le_one A.separation 0
  change (A.squared.compute A.separation).lo ≤ 1 at hb
  change 0 < (A.gap.real.compute A.separation).lo ∨ (A.gap.real.compute A.separation).hi < 0 at h
  rcases h with hp | hn
  · exact hp
  · change 1 + -(A.squared.compute A.separation).lo < 0 at hn
    grind only

def margin (A : Coupling) : Rat := (A.gap.real.compute A.separation).lo / 2
def upper (A : Coupling) : Rat := 1 - A.margin

theorem margin_bounds (A : Coupling) : 0 < A.margin ∧ A.margin ≤ 1 / 2 := by
  have hp := A.separation_pos
  have hz := A.nonnegative 0 A.separation
  change 0 ≤ (A.squared.compute A.separation).hi at hz
  change 0 < 1 + -(A.squared.compute A.separation).hi at hp
  change 0 < (1 + -(A.squared.compute A.separation).hi) / 2 ∧
    (1 + -(A.squared.compute A.separation).hi) / 2 ≤ 1 / 2
  constructor
  · rw [Rat.div_def]; exact Rat.mul_pos hp (Rat.inv_pos.mpr (by decide +kernel))
  · grind only [Rat.div_def]

theorem upper_bounds (A : Coupling) : 0 < A.upper ∧ A.upper < 1 := by
  have hm := A.margin_bounds
  unfold upper
  constructor <;> grind only

theorem squared_le_upper (A : Coupling) : A.squared.preferred.Le (RealRaw.ofRat A.upper) := by
  intro n k
  have hn := RealRaw.le_refl A.squared.preferred A.squared.valid n A.separation
  have hm := A.margin_bounds
  change (A.squared.compute n).lo ≤ (A.squared.compute A.separation).hi at hn
  change (A.squared.compute n).lo ≤ 1 - (1 + -(A.squared.compute A.separation).hi) / 2
  change 0 < (1 + -(A.squared.compute A.separation).hi) / 2 ∧ _ at hm
  grind only [Rat.div_def]

def bounded (A : Coupling) : Real :=
  Real.ofRaw (BracketDerivative.clipped 0 A.upper A.squared.preferred)
    (BracketDerivative.clipped_valid A.squared.valid A.upper_bounds.1 A.nonnegative A.squared_le_upper)

theorem bounded_equiv (A : Coupling) : A.bounded.preferred.Equiv A.squared.preferred :=
  BracketDerivative.clipped_equiv A.squared.valid A.nonnegative A.squared_le_upper

theorem bounded_interval (A : Coupling) (n : Nat) :
    0 ≤ (A.bounded.compute n).lo ∧ (A.bounded.compute n).hi ≤ A.upper :=
  ⟨(BracketDerivative.clipped_bounds 0 A.upper A.squared.preferred n).1,
    (BracketDerivative.clipped_bounds 0 A.upper A.squared.preferred n).2.2.1⟩

def value (A : Coupling) : Value := Value.parameter A.bounded

def angularRadicand (A : Coupling) (k : Nat) : Value :=
  Value.sub (Value.rational ((k : Rat) * (k : Rat))) A.value

def angularRootInput (A : Coupling) (k : Nat) (hk : 0 < k) :
    PositiveInput (k * k) A.margin where
  raw := (A.angularRadicand k).real.preferred
  valid := (A.angularRadicand k).real.valid
  margin_pos := A.margin_bounds.1
  center_le_bound := by
    intro n
    have hb := A.bounded_interval n
    have ho := RealRaw.interval_order_of_valid _ A.bounded.valid n
    have hm := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _ (A.angularRadicand k).real.valid n)
    have hhi : ((A.angularRadicand k).real.compute n).hi ≤ (k : Rat) * (k : Rat) := by
      change (k : Rat) * (k : Rat) + -(A.bounded.compute n).lo ≤ (k : Rat) * (k : Rat)
      grind only
    have hcast : ((k * k : Nat) : Rat) = (k : Rat) * (k : Rat) := Rat.natCast_mul k k
    rw [hcast]
    exact Rat.le_trans hm.2 hhi
  margin_sq_le_center := by
    intro n
    have hb := A.bounded_interval n
    have hm := A.margin_bounds
    have hk1 : (1 : Rat) ≤ (k : Rat) := by exact_mod_cast (show 1 ≤ k by omega)
    have hksq : 1 ≤ (k : Rat) * (k : Rat) := by
      have h := rat_mul_le_mul_of_nonneg (by decide +kernel) hk1 (by decide +kernel) hk1
      grind only
    have hmid := QInterval.midpoint_mem (RealRaw.interval_order_of_valid _ (A.angularRadicand k).real.valid n)
    have hmul := Rat.mul_le_mul_of_nonneg_left (show A.margin ≤ 1 by grind only) (Rat.le_of_lt hm.1)
    change A.margin * A.margin ≤ ((A.angularRadicand k).real.preferred.compute n).midpoint
    have hlo := hmid.1
    change (k : Rat) * (k : Rat) + -(A.bounded.compute n).hi ≤ _ at hlo
    unfold upper at hb
    grind only

/-- Positive branch \(\sqrt{k^2-u}\), with rational bisection and all
implementation bounds chosen internally. -/
def angularRoot (A : Coupling) (k : Nat) (hk : 0 < k) : Real :=
  Real.ofRaw (A.angularRootInput k hk).awayRootRaw.realPart
    (ComplexRaw.realPart_valid (A.angularRootInput k hk).awayRootRaw_valid)

theorem angularRoot_positive (A : Coupling) (k : Nat) (hk : 0 < k) (n : Nat) :
    A.margin / 2 ≤ ((A.angularRoot k hk).compute n).lo :=
  ((A.angularRootInput k hk).awayRootRaw_nested_guard n).1.1

theorem angularRoot_real_embedding (A : Coupling) (k : Nat) (hk : 0 < k) :
    (ComplexRaw.ofRealRaw (A.angularRoot k hk).preferred).Equiv (A.angularRootInput k hk).awayRootRaw := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  have ho := ComplexRaw.valid_ordered (A.angularRootInput k hk).awayRootRaw_valid n
  have hg := (A.angularRootInput k hk).awayRootRaw_nested_guard n
  change (((A.angularRootInput k hk).awayRootRaw.compute n).lo.re ≤
      ((A.angularRootInput k hk).awayRootRaw.compute n).hi.re ∧
      0 ≤ ((A.angularRootInput k hk).awayRootRaw.compute n).hi.im) ∧
    (((A.angularRootInput k hk).awayRootRaw.compute n).lo.re ≤
      ((A.angularRootInput k hk).awayRootRaw.compute n).hi.re ∧
      ((A.angularRootInput k hk).awayRootRaw.compute n).lo.im ≤ 0)
  exact ⟨⟨ho.1,Rat.le_trans hg.1.2 ho.2⟩,⟨ho.1,Rat.le_trans ho.2 hg.2.2⟩⟩

theorem angularRoot_square (A : Coupling) (k : Nat) (hk : 0 < k) :
    (Value.mul (Value.parameter (A.angularRoot k hk)) (Value.parameter (A.angularRoot k hk))).real.preferred.Equiv
      (A.angularRadicand k).real.preferred := by
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.ofRealRaw_valid _ (A.angularRoot k hk).valid)
    (hright := (A.angularRootInput k hk).awayRootRaw_valid) (A.angularRoot_real_embedding k hk)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ComplexRaw.mul_valid (A.angularRootInput k hk).awayRootRaw_valid (A.angularRootInput k hk).awayRootRaw_valid)
    (hright := ComplexRaw.ofRealRaw_valid _ (A.angularRadicand k).real.valid)
    (A.angularRootInput k hk).awayRootRaw_square_equiv_raw
  apply QuotientBridge.raw_equiv_of_quotient_eq
  rw [QuotientBridge.quotient_mul]
  change QuotientBridge.quotient (Value.parameter (A.angularRoot k hk)) = _ at hr
  change QuotientBridge.quotient (Value.parameter (A.angularRoot k hk)) *
    QuotientBridge.quotient (Value.parameter (A.angularRoot k hk)) = _
  rw [hr]
  exact hs

theorem value_equiv (A B : Coupling) (h : A.squared.preferred.Equiv B.squared.preferred) :
    A.value.real.preferred.Equiv B.value.real.preferred :=
  RealRaw.equiv_trans A.bounded.valid A.squared.valid B.bounded.valid A.bounded_equiv
    (RealRaw.equiv_trans A.squared.valid B.squared.valid B.bounded.valid h (RealRaw.equiv_symm B.bounded_equiv))

/-- Changing the input representation can change the finite separation,
margin, and bisection chart. Positivity and the proved square equations
still identify the exact same branch. -/
theorem angularRoot_equiv (A B : Coupling) (h : A.squared.preferred.Equiv B.squared.preferred)
    (k : Nat) (hk : 0 < k) : (A.angularRoot k hk).preferred.Equiv (B.angularRoot k hk).preferred := by
  let x := Value.parameter (A.angularRoot k hk)
  let y := Value.parameter (B.angularRoot k hk)
  let total := Value.add x y
  have hp : 0 < (total.real.compute 0).lo := by
    have hx := A.angularRoot_positive k hk 0
    have hy := B.angularRoot_positive k hk 0
    have hA := A.margin_bounds
    have hB := B.margin_bounds
    change 0 < ((A.angularRoot k hk).compute 0).lo + ((B.angularRoot k hk).compute 0).lo
    grind only [Rat.div_def]
  have hunit := QuotientBridge.quotient_eq (y := Value.rational 1) (QuotientBridge.positiveInv_identity total 0 hp)
  simp only [QuotientBridge.quotient_mul,QuotientBridge.quotient_one] at hunit
  have ht : QuotientBridge.quotient total = QuotientBridge.quotient x + QuotientBridge.quotient y :=
    QuotientBridge.quotient_add x y
  rw [ht] at hunit
  have hsA := QuotientBridge.quotient_eq (A.angularRoot_square k hk)
  have hsB := QuotientBridge.quotient_eq (B.angularRoot_square k hk)
  have hu := QuotientBridge.quotient_eq (A.value_equiv B h)
  simp only [angularRadicand,QuotientBridge.quotient_mul,QuotientBridge.quotient_sub] at hsA hsB
  change (QuotientBridge.quotient x + QuotientBridge.quotient y) *
    QuotientBridge.quotient (Value.positiveInv total 0 hp) = 1 at hunit
  apply QuotientBridge.raw_equiv_of_quotient_eq (x := x) (y := y)
  change QuotientBridge.quotient x * QuotientBridge.quotient x = _ at hsA
  change QuotientBridge.quotient y * QuotientBridge.quotient y = _ at hsB
  rw [hu] at hsA
  clear h
  grind only

end Coupling
end ComputableAnalysis.HydrogenCoupling
