import ComputableAnalysis.RiemannHilbert.GeneralSeriesHolomorphic
import ComputableAnalysis.RiemannHilbert.BoxApproximation
import ComputableAnalysis.RiemannHilbert.DomainFunctions

/-! A genuine represented-input Taylor logarithm near one. Its literal
coefficient algorithm, bound, actual holomorphic witness and normalization
are proved before identifying the derivative with the reciprocal. -/
namespace ComputableAnalysis.RiemannHilbert.LocalLogarithm
open ComplexRaw FunctionTheory LocalODE

def radius : QPos := ⟨1/32, by decide +kernel⟩

def coefficientRat : Nat → Rat
  | 0 => 0
  | k+1 => FormalPowerSeries.altSign k / ((k+1 : Nat) : Rat)

def coefficient (k : Nat) : ComplexRaw := scaleRat (coefficientRat k) one

theorem coefficient_valid (k : Nat) : (coefficient k).Valid := scaleRat_valid (ofQComplex_valid _)

theorem rationalUnit_as_point (r : Rat) : (scaleRat r one).Equiv (ofQComplex (QComplex.ofRat r)) := by
  intro k
  apply (compareAt_overlap_iff _ _ k k).2
  dsimp [one, ofQComplex, QBox.scaleRat]
  simp only [scaleRat]
  dsimp [QBox.scaleRat]
  split <;> simp only [QComplex.one, QComplex.ofRat, QBox.Overlaps, Rat.mul_one, Rat.mul_zero]
  all_goals exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩

theorem coefficientRat_bound (k : Nat) : -1 ≤ coefficientRat k ∧ coefficientRat k ≤ 1 := by
  cases k with
  | zero => constructor <;> decide +kernel
  | succ k =>
    have hn : (1 : Rat) ≤ ((k+1 : Nat) : Rat) := by exact_mod_cast (show 1 ≤ k+1 by omega)
    have hp : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (Nat.succ_pos k)
    have hnonneg := Rat.le_of_lt ((Rat.inv_pos).2 hp)
    have hm := Rat.mul_le_mul_of_nonneg_left hn hnonneg
    have hc := Rat.inv_mul_cancel (a := ((k+1 : Nat) : Rat)) (Rat.ne_of_gt hp)
    have hi : ((k+1 : Nat) : Rat)⁻¹ ≤ 1 := by grind
    dsimp [coefficientRat, FormalPowerSeries.altSign]
    rw [Rat.div_def]
    split <;> constructor <;> grind

theorem coefficient_bound (k : Nat) : Small (coefficient k) (1*(1 : Rat)^k) := by
  have hb := coefficientRat_bound k
  have hp : ∀ j : Nat, (1 : Rat)^j=1 := by intro j; induction j with | zero => rfl | succ j ih => rw [Rat.pow_succ, ih, Rat.one_mul]
  rw [hp k, Rat.mul_one]
  unfold coefficient
  apply Small.congr (ofQComplex_valid _) (scaleRat_valid (ofQComplex_valid _))
    (equiv_symm (rationalUnit_as_point _))
  exact ⟨fun _ _ => hb.1, fun _ _ => hb.2, fun _ _ => by change (-1 : Rat) ≤ 0; decide,
    fun _ _ => by change (0 : Rat) ≤ 1; decide⟩

theorem coefficient_equation (k : Nat) :
    ((k+1 : Nat) : Rat)*coefficientRat (k+1) = FormalPowerSeries.altSign k := by
  have hn : ((k+1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos k))
  have h := Rat.div_mul_cancel (a := FormalPowerSeries.altSign k) hn
  dsimp [coefficientRat]
  grind

def certifiedMap : CertifiedFunctions.Map :=
  BoundedSeries.seriesMap coefficient coefficient_valid 1 1 radius.val
    (by decide) (by decide) (by decide +kernel) coefficient_bound (by decide +kernel)

def certifiedHolomorphic : CertifiedFunctions.Holomorphic certifiedMap :=
  BoundedSeries.seriesMap_holomorphic coefficient coefficient_valid 1 1 radius.val
    (by decide) (by decide) (by decide +kernel) coefficient_bound (by decide +kernel)

def function : DomainFunctions.Map := DomainFunctions.ofCertified certifiedMap

def holomorphic : DomainFunctions.Holomorphic function :=
  DomainFunctions.ofCertifiedHolomorphic certifiedHolomorphic

theorem initial : (function.eval ⟨zero, ofQComplex_valid _⟩ (interior_zero radius.val radius.property)).val.Equiv zero :=
  equiv_trans (function.eval ⟨zero, ofQComplex_valid _⟩ (interior_zero radius.val radius.property)).property
    (coefficient_valid 0) (ofQComplex_valid _)
    (BoundedSeries.seriesMap_initial coefficient coefficient_valid 1 1 radius.val
      (by decide) (by decide) (by decide +kernel) coefficient_bound (by decide +kernel))
    (scaleRat_zeroScalar_equiv one (ofQComplex_valid _))

end ComputableAnalysis.RiemannHilbert.LocalLogarithm
