import ComputableAnalysis.ExponentialComputations.LogarithmRemainder
import ComputableAnalysis.ModularForms.ExponentialPowers
import ComputableAnalysis.ModularForms.ExponentialContinuity
import ComputableAnalysis.RiemannHilbert.ReciprocalExamples

/-! Compound-interest approximations at arbitrary represented complex inputs.
The actual local logarithm supplies a quadratic error. Its inverse identity
and the exponential addition law turn this into a quantitative limit proof. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions ModularForms
set_option maxHeartbeats 1000000

/-- A literal finite compound-interest power, including negative/complex inputs. -/
def compoundApproximation (z : Scalar) (n : Nat) : Scalar :=
  ⟨power (add one (scaleRat (1/((n+1:Nat):Rat)) z.val)) (n+1),
    power_valid _ (add_valid (ofQComplex_valid _) (scaleRat_valid z.property)) _⟩

def compoundRadius (z : Scalar) : QPos :=
  ⟨2*scalarBound z+1,by have h := scalarBound_pos z; grind only⟩

def compoundErrorConstant (z : Scalar) : Rat :=
  256*exponentialBudget (exponentialRatio (compoundRadius z))*
    (exponentialRatio (compoundRadius z))^2*(scalarBound z)^2

theorem compoundErrorConstant_nonnegative (z : Scalar) : 0 ≤ compoundErrorConstant z := by
  unfold compoundErrorConstant
  exact Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel)
      (exponentialBudget_nonnegative _ (exponentialRatio_positive _)))
    (Rat.pow_nonneg (Rat.le_of_lt (exponentialRatio_positive _))))
    (Rat.pow_nonneg (Rat.le_of_lt (scalarBound_pos z)))

/-- Explicit error for every sufficiently fine compound-interest power.
The hypothesis is just a computable lower bound on the finite mesh size. -/
theorem compoundApproximation_error (z : Scalar) (n : Nat)
    (hmesh : scalarBound z/((n+1:Nat):Rat) ≤ (1:Rat)/128) :
    Small (sub (compoundApproximation z n).val (entireExponentialValue z).val)
      (compoundErrorConstant z/((n+1:Nat):Rat)) := by
  let C := scalarBound z
  let m : Rat := ((n+1:Nat):Rat)
  have hm : 0<m := Rat.natCast_pos.mpr (Nat.succ_pos n)
  have hi : 0≤1/m := Rat.le_of_lt (by rw [Rat.div_def,Rat.one_mul]; exact Rat.inv_pos.mpr hm)
  have hC : 0<C := scalarBound_pos z
  have hC0 := Rat.le_of_lt hC
  let w : Scalar := ⟨scaleRat (1/m) z.val,scaleRat_valid z.property⟩
  have hw : Small w.val (C/m) := by
    have h := small_scale hi (scalar_small z)
    change Small w.val ((1/m)*C) at h
    have he : (1/m)*C=C/m := by grind [Rat.div_def]
    rw [he] at h
    exact h
  have hs : 0≤C/m := Rat.mul_nonneg hC0 (Rat.le_of_lt (Rat.inv_pos.mpr hm))
  have hd : interior LocalLogarithm.radius.val w :=
    ⟨C/m,hs,by change C/m≤(1:Rat)/128 at hmesh; change C/m<(1:Rat)/32; grind only,hw⟩
  let l := LocalLogarithm.function.eval w hd
  let a : Scalar := ⟨scaleRat m l.val,scaleRat_valid l.property⟩
  let E := 16*C^2/m
  have hE : 0≤E := Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hC0)) (Rat.le_of_lt (Rat.inv_pos.mpr hm))
  have hlinear := localLogarithm_linear_error w hd (C/m) hs hw
  have hscale := small_scale (Rat.le_of_lt hm) hlinear
  have he : (scaleRat m (sub l.val w.val)).Equiv (sub a.val z.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (sub_valid l.property w.property))
      (hright := sub_valid a.property z.property)
    let L := ComplexRawQuotient.ofRaw l.val l.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change ComplexRawQuotient.scaleRat m (L-ComplexRawQuotient.scaleRat (1/m) Z)=
      ComplexRawQuotient.scaleRat m L-Z
    change ComplexRawQuotient.scaleRat m (L+ -ComplexRawQuotient.scaleRat (1/m) Z)=
      ComplexRawQuotient.scaleRat m L+ -Z
    have hneg (Y : ComplexRawQuotient.Value) :
        ComplexRawQuotient.scaleRat m (-Y)= -(ComplexRawQuotient.scaleRat m Y) := by
      rw [ComplexRawQuotient.neg_eq_scaleRat_neg_one,ComplexRawQuotient.scaleRat_scaleRat,
        ComplexRawQuotient.neg_eq_scaleRat_neg_one,ComplexRawQuotient.scaleRat_scaleRat]
      congr 1
      grind only
    rw [ComplexRawQuotient.scaleRat_add,hneg,ComplexRawQuotient.scaleRat_scaleRat]
    rw [show m*(1/m)=1 by have h := Rat.mul_inv_cancel m (Rat.ne_of_gt hm); grind [Rat.div_def],
      ComplexRawQuotient.scaleRat_one]
  have herr : Small (sub a.val z.val) E := by
    have hh := Small.congr (scaleRat_valid (sub_valid l.property w.property))
      (sub_valid a.property z.property) he hscale
    have hiid := Rat.mul_inv_cancel m (Rat.ne_of_gt hm)
    have heB : m*(16*(C/m)^2)=E := by
      dsimp [E]
      rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_zero,Rat.pow_succ,Rat.pow_succ,Rat.pow_zero]
      grind [Rat.div_def]
    rw [heB] at hh
    exact hh
  have heC : E≤C := by
    have h := Rat.mul_le_mul_of_nonneg_left hmesh (show 0≤16*C by grind only)
    change 16*C*(C/m)≤16*C*((1:Rat)/128) at h
    dsimp [E]; rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_zero]; grind [Rat.div_def]
  have haSmall : Small a.val (2*C) := by
    have h := small_add herr (scalar_small z)
    have heq : (add (sub a.val z.val) z.val).Equiv a.val := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := add_valid (sub_valid a.property z.property) z.property) (hright := a.property)
      change (ComplexRawQuotient.ofRaw a.val a.property-ComplexRawQuotient.ofRaw z.val z.property)+
        ComplexRawQuotient.ofRaw z.val z.property=ComplexRawQuotient.ofRaw a.val a.property
      grind only
    exact Small.mono (Small.congr
      (add_valid (sub_valid a.property z.property) z.property) a.property heq h) (by grind only)
  have hzR : (exponentialChart (compoundRadius z)).domain z :=
    ⟨C,hC0,by dsimp [compoundRadius,C]; grind only,scalar_small z⟩
  have haR : (exponentialChart (compoundRadius z)).domain a :=
    ⟨2*C,by grind only,by dsimp [compoundRadius,C]; grind only,haSmall⟩
  have hcontinuity := entireExponential_lipschitz (compoundRadius z) z a hzR haR E hE herr
  have hpow := power_congr (entireExponentialValue l).val (LocalLogarithm.onePlus w).val
    (entireExponentialValue l).property (LocalLogarithm.onePlus w).property
    (entireExponential_localLogarithm w hd) (n+1)
  have hnat := entireExponential_nat_multiple l (n+1)
  have happrox : (compoundApproximation z n).val.Equiv (entireExponentialValue a).val :=
    equiv_symm (equiv_trans (entireExponentialValue a).property
      (power_valid _ (entireExponentialValue l).property _) (compoundApproximation z n).property
      hnat hpow)
  have hh := Small.congr
    (sub_valid (entireExponentialValue a).property (entireExponentialValue z).property)
    (sub_valid (compoundApproximation z n).property (entireExponentialValue z).property)
    (FunctionTheory.sub_congr (equiv_symm happrox) (equiv_refl _ (entireExponentialValue z).property)) hcontinuity
  have heB : 16*exponentialBudget (exponentialRatio (compoundRadius z))*
      (exponentialRatio (compoundRadius z))^2*E=compoundErrorConstant z/((n+1:Nat):Rat) := by
    dsimp [compoundErrorConstant,E,m,C]
    grind [Rat.div_def]
  rw [heB] at hh
  exact hh

/-- A finite initial mesh bound, computed from the input's rational box. -/
def compoundStart (z : Scalar) : Nat := 128*((scalarBound z).num.natAbs+1)

def compoundPrefix (z : Scalar) (k : Nat) : Scalar := compoundApproximation z (compoundStart z+k)
def compoundError (z : Scalar) (k : Nat) : Rat := compoundErrorConstant z/((k+1:Nat):Rat)

theorem reciprocal_antitone {a b : Rat} (ha : 0<a) (hab : a≤b) : 1/b≤1/a := by
  have hb : 0<b := by grind only
  apply Rat.le_of_mul_le_mul_right (c := a*b)
  · have heA := Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
    have heB := Rat.mul_inv_cancel b (Rat.ne_of_gt hb)
    calc
      (1/b)*(a*b)=a := by rw [Rat.div_def]; grind [Rat.mul_assoc,Rat.mul_comm,Rat.mul_inv_cancel _ (Rat.ne_of_gt hb)]
      _≤b := hab
      _=(1/a)*(a*b) := by rw [Rat.div_def]; grind [Rat.mul_assoc,Rat.mul_comm,Rat.mul_inv_cancel _ (Rat.ne_of_gt ha)]
  · exact Rat.mul_pos ha hb

theorem compoundPrefix_error (z : Scalar) (k : Nat) :
    Small (sub (compoundPrefix z k).val (entireExponentialValue z).val) (compoundError z k) := by
  let C := scalarBound z
  let B : Rat := (((scalarBound z).num.natAbs+1:Nat):Rat)
  let m : Rat := ((compoundStart z+k+1:Nat):Rat)
  have hC : C≤B := Rat.le_trans (self_le_qabs C) (qabs_le_numNatAbs_succ C)
  have hm : 0<m := Rat.natCast_pos.mpr (by omega)
  have hlarge : 128*B≤m := by
    have hn : compoundStart z≤compoundStart z+k+1 := by omega
    have hc : ((compoundStart z:Nat):Rat)≤m := by change ((compoundStart z):Rat)≤((compoundStart z+k+1:Nat):Rat); exact_mod_cast hn
    have he : ((compoundStart z):Rat)=128*B := by
      dsimp [compoundStart,B]
      rw [Rat.natCast_mul]
      rfl
    rw [he] at hc
    exact hc
  have him : 0≤m⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hm)
  have hmul := Rat.mul_le_mul_of_nonneg_right (show 128*C≤m by grind only) him
  have he := Rat.mul_inv_cancel m (Rat.ne_of_gt hm)
  have hmesh : C/m≤(1:Rat)/128 := by grind [Rat.div_def]
  have herror := compoundApproximation_error z (compoundStart z+k) hmesh
  have hk : 0<((k+1:Nat):Rat) := Rat.natCast_pos.mpr (Nat.succ_pos k)
  have hkm : ((k+1:Nat):Rat)≤m := by change ((k+1:Nat):Rat)≤((compoundStart z+k+1:Nat):Rat); exact_mod_cast (show k+1≤compoundStart z+k+1 by omega)
  have hi := reciprocal_antitone hk hkm
  have hK := compoundErrorConstant_nonnegative z
  have hh := Rat.mul_le_mul_of_nonneg_left hi hK
  apply Small.mono herror
  simpa only [compoundError,Rat.div_def,Rat.one_mul] using hh

theorem compoundError_antitone (z : Scalar) {k n : Nat} (hkn : k≤n) :
    compoundError z n≤compoundError z k := by
  have hk : 0<((k+1:Nat):Rat) := Rat.natCast_pos.mpr (Nat.succ_pos k)
  have hn : ((k+1:Nat):Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show k+1≤n+1 by omega)
  have h := Rat.mul_le_mul_of_nonneg_left (reciprocal_antitone hk hn)
    (compoundErrorConstant_nonnegative z)
  simpa only [compoundError,Rat.div_def,Rat.one_mul] using h

theorem compoundError_shrinks (z : Scalar) : ShrinksToZero (compoundError z) :=
  shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl)

theorem compoundPrefix_cauchy (z : Scalar) (k n : Nat) (hkn : k≤n) :
    Small (sub (compoundPrefix z n).val (compoundPrefix z k).val) (2*compoundError z k) := by
  have h := SeriesLimitLaws.small_sub (compoundPrefix_error z n) (compoundPrefix_error z k)
  have he : (sub (sub (compoundPrefix z n).val (entireExponentialValue z).val)
      (sub (compoundPrefix z k).val (entireExponentialValue z).val)).Equiv
      (sub (compoundPrefix z n).val (compoundPrefix z k).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid (compoundPrefix z n).property (entireExponentialValue z).property)
        (sub_valid (compoundPrefix z k).property (entireExponentialValue z).property))
      (hright := sub_valid (compoundPrefix z n).property (compoundPrefix z k).property)
    change (ComplexRawQuotient.ofRaw (compoundPrefix z n).val (compoundPrefix z n).property-
      ComplexRawQuotient.ofRaw (entireExponentialValue z).val (entireExponentialValue z).property)-
      (ComplexRawQuotient.ofRaw (compoundPrefix z k).val (compoundPrefix z k).property-
      ComplexRawQuotient.ofRaw (entireExponentialValue z).val (entireExponentialValue z).property)=
      ComplexRawQuotient.ofRaw (compoundPrefix z n).val (compoundPrefix z n).property-
      ComplexRawQuotient.ofRaw (compoundPrefix z k).val (compoundPrefix z k).property
    grind only
  have hb := Small.congr
    (sub_valid (sub_valid (compoundPrefix z n).property (entireExponentialValue z).property)
      (sub_valid (compoundPrefix z k).property (entireExponentialValue z).property))
    (sub_valid (compoundPrefix z n).property (compoundPrefix z k).property) he h
  exact Small.mono hb (by have h := compoundError_antitone z hkn; grind only)

/-- Executable limit from finite powers and shrinking error bounds. The
runtime samples the compound powers; it does not evaluate the power series. -/
def compoundValue (z : Scalar) : Scalar :=
  ⟨RepresentedCauchySum.value (fun k => (compoundPrefix z k).val)
      (fun k => (compoundPrefix z k).property) (fun k => 2*compoundError z k),
    RepresentedCauchySum.value_valid _ _ _
      (SeriesLimitLaws.shrinks_scale _ (compoundError_shrinks z) 2 (by decide +kernel))
      (compoundPrefix_cauchy z)⟩

/-- Exact agreement of the compound-interest and power-series constructions
on every valid represented complex input. -/
theorem compoundValue_equiv_powerSeries (z : Scalar) :
    (compoundValue z).val.Equiv (entireExponentialValue z).val := by
  apply RepresentedCauchySum.unique (fun k => (compoundPrefix z k).val)
    (fun k => (compoundPrefix z k).property) (fun k => 2*compoundError z k)
    (SeriesLimitLaws.shrinks_scale _ (compoundError_shrinks z) 2 (by decide +kernel))
    _ _ (compoundValue z).property (entireExponentialValue z).property
  · exact RepresentedCauchySum.value_close_prefix _ _ _ (compoundPrefix_cauchy z)
  · intro k
    have hs := RepresentedCauchySum.small_sub_symm _ _ _ (compoundPrefix_error z k)
    have hnonneg : 0≤compoundError z k := Rat.mul_nonneg (compoundErrorConstant_nonnegative z)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.succ_pos k))))
    exact Small.mono hs (by grind only)

theorem compoundValue_congr (z w : Scalar) (hzw : z.val.Equiv w.val) :
    (compoundValue z).val.Equiv (compoundValue w).val :=
  equiv_trans (compoundValue z).property (entireExponentialValue z).property (compoundValue w).property
    (compoundValue_equiv_powerSeries z)
    (equiv_trans (entireExponentialValue z).property (entireExponentialValue w).property (compoundValue w).property
      (entireExponentialValue_congr z w hzw) (equiv_symm (compoundValue_equiv_powerSeries w)))
end ComputableAnalysis.ExponentialComputations

