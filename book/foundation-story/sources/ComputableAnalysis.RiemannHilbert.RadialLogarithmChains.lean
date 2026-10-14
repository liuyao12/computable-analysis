import ComputableAnalysis.RiemannHilbert.RadialGrowthArithmetic
import ComputableAnalysis.RiemannHilbert.LogarithmicChainGerms
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction

/-! Constructed radial logarithm chains at every nonzero represented
center. Each step multiplies the center by a fixed positive rational and
has the same actual Taylor logarithm increment, independently of the name. -/
namespace ComputableAnalysis.RiemannHilbert.RadialLogarithmChains
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch LogarithmContinuation
open RadialGrowthArithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000

def scale (r : Rat) (c : Scalar) : Scalar := ⟨scaleRat r c.val,scaleRat_valid c.property⟩

theorem scale_nonzero (r : Rat) (hr : 0 < r) (c : Scalar) (hc : Nonzero c) : Nonzero (scale r c) := by
  let d := scale r⁻¹ (RepresentedReciprocal.inverse c hc)
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid c.property (RepresentedReciprocal.inverse c hc).property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse c hc)
  apply RepresentedReciprocal.nonzero_of_inverse (scale r c) d
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (scale r c).property d.property) (hright := ofQComplex_valid _)
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let D := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  change C*D=1 at hi
  change ComplexRawQuotient.scaleRat r C*ComplexRawQuotient.scaleRat r⁻¹ D=1
  rw [ComplexRawQuotient.scaleRat_mul_scaleRat,hi,Rat.mul_inv_cancel r (Rat.ne_of_gt hr),ComplexRawQuotient.scaleRat_one]

def center (c : Scalar) : Nat → Scalar
  | 0 => c
  | k+1 => scale ratio (center c k)
theorem center_nonzero (c : Scalar) (hc : Nonzero c) : (k : Nat) → Nonzero (center c k)
  | 0 => hc
  | k+1 => scale_nonzero ratio ratio_positive (center c k) (center_nonzero c hc k)

theorem center_value (c : Scalar) (k : Nat) : (center c k).val.Equiv (scaleRat (ratio^k) c.val) := by
  induction k with
  | zero =>
      simp only [center,Rat.pow_zero]
      exact equiv_symm (scaleRat_one_equiv c.val c.property)
  | succ k ih =>
      apply equiv_trans (center c (k+1)).property (scaleRat_valid (scaleRat_valid c.property)) (scaleRat_valid c.property)
        (scaleRat_equiv ih)
      have he := scaleRat_scaleRat_equiv ratio (ratio^k) c.val c.property
      have hr : ratio*ratio^k=ratio^(k+1) := by rw [Rat.pow_succ,Rat.mul_comm]
      rw [hr] at he
      exact he

theorem center_congr (c d : Scalar) (hcd : c.val.Equiv d.val) (k : Nat) : (center c k).val.Equiv (center d k).val := by
  induction k with
  | zero => exact hcd
  | succ k ih => exact scaleRat_equiv ih

def offset : Scalar := ⟨ofQComplex ⟨-1/64,0⟩,ofQComplex_valid _⟩
theorem offset_mem : interior LocalLogarithm.radius.val offset :=
  ⟨1/64,by decide +kernel,by decide +kernel,
    ⟨fun _ _ => by change -(1/64 : Rat) ≤ -1/64; decide +kernel,
      fun _ _ => by change (-1/64 : Rat) ≤ 1/64; decide +kernel,
      fun _ _ => by change -(1/64 : Rat) ≤ 0; decide +kernel,
      fun _ _ => by change (0 : Rat) ≤ 1/64; decide +kernel⟩⟩
def stepLog : Scalar := LocalLogarithm.function.eval offset offset_mem

theorem point_step (c : Scalar) (hc : Nonzero c) :
    (RelativeLogarithm.point c hc (scale ratio c)).val.Equiv offset.val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (RepresentedReciprocal.inverse c hc).property c.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.inverse_mul c hc)
  have he : (RelativeLogarithm.point c hc (scale ratio c)).val.Equiv (scaleRat (-1/64) one) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (RelativeLogarithm.point c hc (scale ratio c)).property) (hright := scaleRat_valid (ofQComplex_valid _))
    let C := ComplexRawQuotient.ofRaw c.val c.property
    let R := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
    change R*C=1 at hi
    change -1+R*ComplexRawQuotient.scaleRat ratio C=ComplexRawQuotient.scaleRat (-1/64) 1
    rw [ComplexRawQuotient.mul_scaleRat,hi]
    have hr : ratio=1+(-1/64) := by decide +kernel
    rw [hr,← ComplexRawQuotient.add_scaleRat,ComplexRawQuotient.scaleRat_one]
    grind only
  exact equiv_trans (RelativeLogarithm.point c hc (scale ratio c)).property (scaleRat_valid (ofQComplex_valid _)) offset.property
    he (LocalLogarithm.rationalUnit_as_point (-1/64))

theorem step_mem (c : Scalar) (hc : Nonzero c) : RelativeLogarithm.domain c hc (scale ratio c) :=
  Centered.interior_congr LocalLogarithm.radius.val offset _ (equiv_symm (point_step c hc)) offset_mem

theorem step_value (c : Scalar) (hc : Nonzero c) :
    ((RelativeLogarithm.function c hc).eval (scale ratio c) (step_mem c hc)).val.Equiv stepLog.val :=
  LocalLogarithm.function.eval_congr _ offset (step_mem c hc) offset_mem (point_step c hc)

def stepChain (c : Scalar) (hc : Nonzero c) : Chain c hc (scale ratio c) (scale_nonzero ratio ratio_positive c hc) :=
  .step (step_mem c hc) (.nil _ _)

theorem step_increment (c : Scalar) (hc : Nonzero c) : (increment (stepChain c hc)).val.Equiv stepLog.val :=
  equiv_trans (increment (stepChain c hc)).property ((RelativeLogarithm.function c hc).eval (scale ratio c) (step_mem c hc)).property
    stepLog.property (add_zero_equiv _ ((RelativeLogarithm.function c hc).eval (scale ratio c) (step_mem c hc)).property) (step_value c hc)

def chain (c : Scalar) (hc : Nonzero c) : (k : Nat) → Chain c hc (center c k) (center_nonzero c hc k)
  | 0 => .nil c hc
  | k+1 => append (chain c hc k) (stepChain (center c k) (center_nonzero c hc k))

theorem increment_succ (c : Scalar) (hc : Nonzero c) (k : Nat) :
    (increment (chain c hc (k+1))).val.Equiv (scalarSum (increment (chain c hc k)) stepLog).val :=
  equiv_trans (increment (chain c hc (k+1))).property
    (scalarSum (increment (chain c hc k)) (increment (stepChain (center c k) (center_nonzero c hc k)))).property
    (scalarSum (increment (chain c hc k)) stepLog).property (increment_append _ _)
    (add_equiv (equiv_refl _ (increment (chain c hc k)).property) (step_increment _ _))

theorem increment_value (c : Scalar) (hc : Nonzero c) (k : Nat) :
    (increment (chain c hc k)).val.Equiv (scaleRat (k : Rat) stepLog.val) := by
  induction k with
  | zero => exact equiv_symm (scaleRat_zeroScalar_equiv _ stepLog.property)
  | succ k ih =>
      have hsum := add_equiv ih (equiv_refl _ stepLog.property)
      have he : (add (scaleRat (k : Rat) stepLog.val) stepLog.val).Equiv (scaleRat ((k+1 : Nat) : Rat) stepLog.val) := by
        apply ComplexRawQuotient.equiv_of_ofRaw_eq
          (hleft := add_valid (scaleRat_valid stepLog.property) stepLog.property) (hright := scaleRat_valid stepLog.property)
        let L := ComplexRawQuotient.ofRaw stepLog.val stepLog.property
        change ComplexRawQuotient.scaleRat (k : Rat) L+L=ComplexRawQuotient.scaleRat ((k+1 : Nat) : Rat) L
        rw [Rat.natCast_add]
        change ComplexRawQuotient.scaleRat (k : Rat) L+L=ComplexRawQuotient.scaleRat ((k : Rat)+1) L
        rw [← ComplexRawQuotient.add_scaleRat,ComplexRawQuotient.scaleRat_one]
      exact equiv_trans (increment (chain c hc (k+1))).property (scalarSum (increment (chain c hc k)) stepLog).property
        (scaleRat_valid stepLog.property) (increment_succ c hc k)
        (equiv_trans (scalarSum (increment (chain c hc k)) stepLog).property
          (add_valid (scaleRat_valid stepLog.property) stepLog.property) (scaleRat_valid stepLog.property) hsum he)

end ComputableAnalysis.RiemannHilbert.RadialLogarithmChains
