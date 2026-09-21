import ComputableAnalysis.TaylorFTC
import ComputableAnalysis.RationalLipschitzIntegral
import ComputableAnalysis.UnitPowerCalculus

/-! An arbitrary-order, nonpolynomial client of TaylorFTC. The function is
1/(2-x), on [0,1]. Derivatives are proved from a finite inverse identity.
The remainder integral is an independent dyadic rational quadrature, whose
convergence uses Lipschitz bounds, not the proposed Taylor evaluation. -/
namespace ComputableAnalysis.TaylorReciprocal
open ClosedArctanInverse MonotoneAverage RationalSampleLimits
open FiniteSampleCalculus UnitPowerCalculus

def reciprocal (x : Rat) : Rat := (2-x)⁻¹

private theorem den_pos {x : Rat} (hx : Unit x) : 0<2-x := by
  have h:=hx.2;grind only

private theorem cancel {x : Rat} (hx : Unit x) : (2-x)*reciprocal x=1 :=
  Rat.mul_inv_cancel _ (Rat.ne_of_gt (den_pos hx))

theorem reciprocal_unit {x : Rat} (hx : Unit x) : Unit (reciprocal x) := by
  have hi : 0<reciprocal x := (Rat.inv_pos).2 (den_pos hx)
  have h0:=Rat.le_of_lt hi
  have hc:=cancel hx
  have hd : 1≤2-x := by have h:=hx.2;grind only
  have h:=Rat.mul_le_mul_of_nonneg_right hd h0
  exact ⟨h0,by grind only⟩

theorem reciprocal_difference {a b : Rat} (ha : Unit a) (hb : Unit b) :
    reciprocal b-reciprocal a=(b-a)*reciprocal a*reciprocal b := by
  have h1:=cancel ha;have h2:=cancel hb
  grind only

theorem reciprocal_lipschitz : RationalLipschitzIntegral.Lipschitz reciprocal 1 := by
  intro a b ha hb
  have hu:=reciprocal_unit ha;have hv:=reciprocal_unit hb
  have hprod:=mul_abs_bound (by decide : (0:Rat)≤1) (abs_le_unit hu) (abs_le_unit hv)
  rw [reciprocal_difference hb ha,qabs_mul,qabs_mul]
  have hs:=Rat.mul_le_mul_of_nonneg_left hprod (qabs_nonneg (a-b))
  rw [qabs_mul] at hs
  grind only

def reciprocalModel : Model (fun x _=>reciprocal x) (fun x _=>reciprocal x*reciprocal x) where
  valueBound:=1
  slopeBound:=1
  errorBound:=1
  valueBound_nonneg:=by decide
  slopeBound_nonneg:=by decide
  errorBound_nonneg:=by decide
  value:=fun x _ hx=>abs_le_unit (reciprocal_unit hx)
  slope:=by
    intro x q hx
    simpa only [show (1:Rat)*1=1 by decide +kernel] using
      mul_abs_bound (by decide : (0:Rat)≤1) (abs_le_unit (reciprocal_unit hx)) (abs_le_unit (reciprocal_unit hx))
  local_error:=by
    intro a b ha hb hab
    refine ⟨0,fun q _=>?_⟩
    have h:=reciprocal_difference ha hb
    have hu:=reciprocal_unit ha;have hv:=reciprocal_unit hb
    have h2:=mul_abs_bound (by decide : (0:Rat)≤1) (abs_le_unit hu) (abs_le_unit hu)
    have h3:=mul_abs_bound (by decide : (0:Rat)≤1)
      (by simpa only [show (1:Rat)*1=1 by decide +kernel] using h2) (abs_le_unit hv)
    have hh : 0≤b-a := by grind only
    have hp:=Rat.mul_le_mul_of_nonneg_left h3 (Rat.mul_nonneg hh hh)
    have he : reciprocal b-reciprocal a-(b-a)*(reciprocal a*reciprocal a)=
      (b-a)*(b-a)*(reciprocal a*reciprocal a*reciprocal b) := by grind only
    rw [he,qabs_mul,qabs_mul,qabs_eq_self_of_nonneg hh]
    grind only

/-- The kth derivative, independent of any Taylor identity. -/
def derivatives (k : Nat) : SampleFunction :=
  fun x _=>factorialRat k*reciprocal x^(k+1)

def derivativeModel (k : Nat) : Model (derivatives k) (derivatives (k+1)) :=
  ((Model.const (factorialRat k)).mul (modelPower reciprocalModel (k+1))).congr
    (fun _ _=>rfl) (by
      intro t q
      change 0*reciprocal t^(k+1)+factorialRat k*
        (((k+1:Nat):Rat)*reciprocal t^k*(reciprocal t*reciprocal t))=derivatives (k+1) t q
      simp only [derivatives,FormalPowerSeries.factorialRat_succ,Rat.pow_succ]
      grind only)

def normalizedIntegrand (n : Nat) (x : Rat) : Rat :=
  (1-x)^n*reciprocal x^(n+2)

private theorem complement_unit {x : Rat} (hx : Unit x) : Unit (1-x) := by
  have h0:=hx.1;have h1:=hx.2;constructor <;> grind only

private theorem power_unit {x : Rat} (hx : Unit x) (n : Nat) : Unit (x^n) :=
  ⟨FiniteRationalPowers.pow_nonneg hx.1 n,
    by simpa only [FiniteRationalPowers.one_pow] using FiniteRationalPowers.pow_mono hx.1 hx.2 n⟩

private theorem integrand_unit (n : Nat) {x : Rat} (hx : Unit x) : Unit (normalizedIntegrand n x) := by
  have h1:=power_unit (complement_unit hx) n
  have h2:=power_unit (reciprocal_unit hx) (n+2)
  refine ⟨Rat.mul_nonneg h1.1 h2.1,?_⟩
  have h:=Rat.mul_le_mul_of_nonneg_right h1.2 h2.1
  unfold normalizedIntegrand;grind only

theorem integrand_lipschitz (n : Nat) :
    RationalLipschitzIntegral.Lipschitz (normalizedIntegrand n) ((2*n+2:Nat):Rat) := by
  intro a b ha hb
  have h1:=power_difference (complement_unit ha) (complement_unit hb) n
  have ha1 : qabs ((1-a)-(1-b))=qabs (a-b) := by
    rw [show (1-a)-(1-b)= -(a-b) by grind only,qabs_neg]
  rw [ha1] at h1
  have h2:=power_difference (reciprocal_unit ha) (reciprocal_unit hb) (n+2)
  have h3:=Rat.mul_le_mul_of_nonneg_left (reciprocal_lipschitz a b ha hb) (Rat.natCast_nonneg (a:=n+2))
  have ht2 : qabs (reciprocal a^(n+2)-reciprocal b^(n+2))≤((n+2:Nat):Rat)*qabs (a-b) := by grind only
  have hb1:=mul_abs_bound (by decide : (0:Rat)≤1)
    (abs_le_unit (power_unit (reciprocal_unit ha) (n+2))) h1
  have hb2:=mul_abs_bound (by decide : (0:Rat)≤1)
    (abs_le_unit (power_unit (complement_unit hb) n)) ht2
  have ht:=qabs_add_le
    (reciprocal a^(n+2)*((1-a)^n-(1-b)^n))
    ((1-b)^n*(reciprocal a^(n+2)-reciprocal b^(n+2)))
  have he : reciprocal a^(n+2)*((1-a)^n-(1-b)^n)+
    (1-b)^n*(reciprocal a^(n+2)-reciprocal b^(n+2))=normalizedIntegrand n a-normalizedIntegrand n b := by
    unfold normalizedIntegrand;grind only
  rw [he] at ht
  simp only [Rat.natCast_add,Rat.natCast_mul,Rat.natCast_ofNat] at ht2 hb1 hb2 ⊢
  grind only

def quadratureData (n : Nat) : RationalLipschitzIntegral.Data where
  sample:=normalizedIntegrand n
  range:=fun _ hx=>integrand_unit n hx
  constant:=2*n+2
  bound:=integrand_lipschitz n

/-- Actual quadrature; no endpoint value is used to define it. -/
def remainderIntegral (n : Nat) : RealRaw :=
  RealRaw.scaleRat ((n+1:Nat):Rat) (RationalLipschitzIntegral.raw (quadratureData n))

theorem remainderIntegral_valid (n : Nat) : (remainderIntegral n).Valid :=
  RealRaw.scaleRat_valid (RationalLipschitzIntegral.valid (quadratureData n))

def integralSample (n q : Nat) : Rat :=
  ((n+1:Nat):Rat)*left (normalizedIntegrand n) 0 1 q

private theorem derivative_weight (n : Nat) (x : Rat) (q : Nat) :
    TaylorFTC.remainderSample derivatives 1 n x q=((n+1:Nat):Rat)*normalizedIntegrand n x := by
  unfold TaylorFTC.remainderSample TaylorFTC.weight derivatives normalizedIntegrand
  rw [FormalPowerSeries.factorialRat_succ]
  have hc:=Rat.mul_inv_cancel (factorialRat n) (Rat.ne_of_gt (RationalMajorant.factorialRat_pos n))
  simp only [Rat.div_def]
  grind only

private theorem sample_mem (n q : Nat) :
    IntervalSelections.InBox (integralSample n q) ((remainderIntegral n).compute q) :=
  IntervalSelections.scale_mem
    (RationalLipschitzIntegral.contains_future (quadratureData n) q q (Nat.le_refl q)) Rat.natCast_nonneg

/-- A nonpolynomial, arbitrary-order evaluation of the independently computed
remainder integral, obtained through TaylorFTC rather than a geometric-series
identity. -/
theorem remainderIntegral_equiv_gap (n : Nat) :
    (remainderIntegral n).Equiv
      (RealRaw.ofRat (1-TaylorFTC.polynomial derivatives 0 1 n 0)) := by
  have h:=TaylorFTC.integral_remainder derivatives n (fun k _=>derivativeModel k)
    (a:=0) (b:=1) ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide)
    (integralSample n) (((n+1:Nat):Rat)*((2*n+2:Nat):Rat))
    (Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg) (by
      intro d q hdq
      have hc : 0≤((n+1:Nat):Rat) := Rat.natCast_nonneg
      have hm:=RationalLipschitzIntegral.mesh_error (normalizedIntegrand n) ((2*n+2:Nat):Rat)
        Rat.natCast_nonneg (integrand_lipschitz n) d q hdq
      have hs:=Rat.mul_le_mul_of_nonneg_left hm hc
      have he : (fun t=>TaylorFTC.remainderSample derivatives 1 n t q)=
          (fun t=>((n+1:Nat):Rat)*normalizedIntegrand n t) := funext (fun t=>derivative_weight n t q)
      rw [he,left_mul]
      simp only [integralSample,show (1:Rat)-0=1 by decide +kernel,Rat.one_mul]
      rw [show ((n+1:Nat):Rat)*left (normalizedIntegrand n) 0 1 q-
        ((n+1:Nat):Rat)*left (normalizedIntegrand n) 0 1 d=
        ((n+1:Nat):Rat)*(left (normalizedIntegrand n) 0 1 q-left (normalizedIntegrand n) 0 1 d) by grind only,
        qabs_mul,qabs_eq_self_of_nonneg hc]
      simpa only [Rat.mul_assoc] using hs)
  apply equiv_of_close (remainderIntegral_valid n) (RealRaw.ofRat_valid _)
    (integralSample n) (fun _=>1-TaylorFTC.polynomial derivatives 0 1 n 0)
    (sample_mem n) (fun _=>⟨Rat.le_refl,Rat.le_refl⟩)
  have hval : ∀ q, derivatives 0 1 q=1 := by
    intro q;change (1:Rat)*(2-1)⁻¹^(0+1)=1;decide +kernel
  have hpoly : ∀ q, TaylorFTC.polynomial derivatives 0 1 n q=TaylorFTC.polynomial derivatives 0 1 n 0 := by
    intro q;rfl
  simpa only [hval,hpoly] using h

end ComputableAnalysis.TaylorReciprocal

namespace ComputableAnalysis.TaylorReciprocal

private theorem coefficient_term (k : Nat) :
    TaylorFTC.weight 1 k 0 * derivatives k 0 0 = (1/2:Rat)^(k+1) := by
  unfold TaylorFTC.weight derivatives reciprocal
  rw [show (1:Rat)-0=1 by decide +kernel,FiniteRationalPowers.one_pow,
    show (2:Rat)-0=2 by decide +kernel]
  have hc:=Rat.mul_inv_cancel (factorialRat k) (Rat.ne_of_gt (RationalMajorant.factorialRat_pos k))
  simp only [Rat.div_def,Rat.one_mul]
  grind only

/-- The Taylor coefficients at zero display the ordinary geometric pattern. -/
theorem polynomial_value (n : Nat) :
    TaylorFTC.polynomial derivatives 0 1 n 0 = 1-(1/2:Rat)^(n+1) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    change TaylorFTC.polynomial derivatives 0 1 n 0+
      TaylorFTC.weight 1 (n+1) 0 * derivatives (n+1) 0 0 = _
    rw [ih,coefficient_term,Rat.pow_succ]
    simp only [Rat.div_def];grind only

/-- The chosen rational quadrature evaluates to the exact Taylor remainder.
The interval program contains no reference to this value. -/
theorem remainderIntegral_evaluation (n : Nat) :
    (remainderIntegral n).Equiv (RealRaw.ofRat ((1/2:Rat)^(n+1))) := by
  have h:=remainderIntegral_equiv_gap n
  rw [polynomial_value] at h
  simpa only [show ∀ x:Rat, 1-(1-x)=x by intro x;grind only] using h

end ComputableAnalysis.TaylorReciprocal
