import ComputableAnalysis.FiniteSamplePowers
import ComputableAnalysis.TaylorCancellation

/-!
# Taylor's formula from the existing finite-sample FTC

All functions are rational samples of the project's computations. Each link
in the derivative chain carries a local quadratic-remainder Model. No Taylor
identity or convergence of an infinite Taylor series is assumed.

The remainder quadrature is supplied independently with its finite mesh
comparison. A weighted sum of derivatives supplies its primitive, by product
rules and finite cancellation. This module uses no completed real numbers.
-/
namespace ComputableAnalysis.TaylorFTC
open FiniteSampleCalculus UnitPowerCalculus RationalSampleLimits
open ClosedArctanInverse MonotoneAverage

/-- Reversed divided powers, with a rational endpoint `b`. -/
def weight (b : Rat) (n : Nat) (t : Rat) : Rat :=
  (b-t)^n / factorialRat n

def weightSlope (b : Rat) : Nat → Rat → Rat
  | 0 => fun _ => 0
  | n+1 => fun t => -weight b n t

private theorem fact_lower (n : Nat) :
    ((n+1:Nat):Rat) * (factorialRat (n+1))⁻¹ = (factorialRat n)⁻¹ := by
  rw [FormalPowerSeries.factorialRat_succ, Rat.inv_mul_rev]
  have hp : 0 < ((n+1:Nat):Rat) := by
    have hn : (0:Rat) ≤ (n:Rat) := Rat.natCast_nonneg
    simp only [Rat.natCast_add,Rat.natCast_ofNat]; grind only
  have hc := Rat.mul_inv_cancel ((n+1:Nat):Rat) (Rat.ne_of_gt hp)
  grind only

private def reverseLinear (b : Rat) :
    Model (fun t _=>b-t) (fun _ _=> -1) :=
  ((Model.const b).sub Model.identity).congr (fun _ _=>rfl)
    (by intro t q; grind only)

/-- Differentiation of every finite polynomial weight. -/
def weightModel (b : Rat) (n : Nat) :
    Model (fun t _=>weight b n t) (fun t _=>weightSlope b n t) :=
  ((Model.const ((factorialRat n)⁻¹)).mul (modelPower (reverseLinear b) n)).congr
    (by intro t q; unfold weight; rw [Rat.div_def]; exact Rat.mul_comm _ _)
    (by
      intro t q
      cases n with
      | zero => simp only [slopePower,weightSlope,Rat.zero_mul,Rat.mul_zero,Rat.zero_add]
      | succ n =>
        change 0*(b-t)^(n+1)+(factorialRat (n+1))⁻¹*
          (((n+1:Nat):Rat)*(b-t)^n*(-1)) = -weight b n t
        have hc:=fact_lower n
        unfold weight; simp only [Rat.div_def]
        grind only)

/-- The finite weighted derivative sum. `n` is its degree. -/
def primitive (F : Nat → SampleFunction) (b : Rat) (n : Nat) (t : Rat) (q : Nat) : Rat :=
  TaylorCancellation.sum (fun k=>weight b k t) (fun k=>F k t q) (n+1)

def remainderSample (F : Nat → SampleFunction) (b : Rat) (n : Nat) (t : Rat) (q : Nat) : Rat :=
  weight b n t * F (n+1) t q

/-- The analytic bridge missing from the previous finite-cancellation result:
product differentiation of the supplied chain builds a model for the whole
weighted sum, and leaves only the last weighted derivative. -/
def primitiveModel (F : Nat → SampleFunction) (b : Rat) :
    (n : Nat) → (∀ k, k≤n → Model (F k) (F (k+1))) →
    Model (primitive F b n) (remainderSample F b n)
  | 0, chain => (chain 0 (Nat.le_refl 0)).congr
      (by
        intro t q
        simp only [primitive,TaylorCancellation.sum,weight,Rat.pow_zero,
          factorialRat,factorial]
        simp only [Rat.natCast_ofNat, show (1:Rat)/1=1 by decide +kernel, Rat.one_mul, Rat.zero_add])
      (by
        intro t q
        simp only [remainderSample,weight,Rat.pow_zero,factorialRat,factorial]
        simp only [Rat.natCast_ofNat, show (1:Rat)/1=1 by decide +kernel, Rat.one_mul])
  | n+1, chain =>
      ((primitiveModel F b n (fun k hk=>chain k (by omega))).add
        ((weightModel b (n+1)).mul (chain (n+1) (Nat.le_refl _)))).congr
        (by intro t q; rfl)
        (by
          intro t q
          simp only [remainderSample,weightSlope]
          grind only)

/-- Taylor polynomial evaluated at the endpoint, from derivative samples at a. -/
def polynomial (F : Nat → SampleFunction) (a b : Rat) (n q : Nat) : Rat :=
  TaylorCancellation.sum (fun k=>weight b k a) (fun k=>F k a q) (n+1)

private theorem weight_at_endpoint (b : Rat) (n : Nat) :
    weight b (n+1) b = 0 := by
  unfold weight
  rw [Rat.sub_self, FiniteRationalPowers.zero_pow (by omega), Rat.div_def, Rat.zero_mul]

private theorem primitive_at_endpoint (F : Nat → SampleFunction) (b : Rat) (n q : Nat) :
    primitive F b n b q = F 0 b q := by
  induction n with
  | zero =>
    simp only [primitive,TaylorCancellation.sum,weight,Rat.pow_zero,factorialRat,factorial]
    simp only [Rat.natCast_ofNat, show (1:Rat)/1=1 by decide +kernel, Rat.one_mul, Rat.zero_add]
  | succ n ih =>
    change primitive F b n b q + weight b (n+1) b * F (n+1) b q = F 0 b q
    rw [weight_at_endpoint,Rat.zero_mul,Rat.add_zero,ih]

/-- The old FTC extended to a rational subinterval of the certified unit chart.
Only the endpoint and mesh scaling differ from `chosen_samples_FTC`. -/
theorem chosen_samples_FTC_on {F D : SampleFunction} (f : Model F D)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a<b)
    (I : Nat → Rat) (B : Rat) (hB : 0≤B)
    (mesh_error : ∀ d q, d≤q →
      qabs (I q-(b-a)*left (fun t=>D t q) a b d) ≤ B*meshRadius d) :
    Close I (fun q=>F b q-F a q) := by
  have hK : 0≤f.errorBound*(b-a)*(b-a)+B :=
    Rat.add_nonneg (Rat.mul_nonneg (Rat.mul_nonneg f.errorBound_nonneg (by grind)) (by grind)) hB
  have hs : Small (fun d=>(f.errorBound*(b-a)*(b-a)+B)*meshRadius d) :=
    small_of_geometric_bound _ hK (fun d=>by
      rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg hK (Rat.le_of_lt (meshRadius_pos d)))]
      exact Rat.le_refl)
  intro eps
  obtain ⟨d,hd⟩:=hs eps
  obtain ⟨N,hN⟩:=finite_telescope f d ha hb hab
  refine ⟨max N d,fun q hq=>?_⟩
  have h1:=hN q (by omega)
  have h2:=mesh_error d q (by omega)
  have h3:=hd d (Nat.le_refl d)
  have ht:=qabs_sub_le (I q-(b-a)*left (fun t=>D t q) a b d)
    (F b q-F a q-(b-a)*left (fun t=>D t q) a b d)
  have he : (I q-(b-a)*left (fun t=>D t q) a b d)-
      (F b q-F a q-(b-a)*left (fun t=>D t q) a b d)=I q-(F b q-F a q) := by grind only
  rw [he] at ht
  have hp:=self_le_qabs ((f.errorBound*(b-a)*(b-a)+B)*meshRadius d)
  grind only

/-- Arbitrary-order Taylor formula with an independently computed integral
remainder. The mesh hypothesis describes the remainder quadrature, not the
Taylor identity or its endpoint value. -/
theorem integral_remainder (F : Nat → SampleFunction) (n : Nat)
    (chain : ∀ k, k≤n → Model (F k) (F (k+1)))
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a<b)
    (I : Nat → Rat) (B : Rat) (hB : 0≤B)
    (mesh_error : ∀ d q, d≤q →
      qabs (I q-(b-a)*left (fun t=>remainderSample F b n t q) a b d) ≤ B*meshRadius d) :
    Close I (fun q=>F 0 b q-polynomial F a b n q) := by
  have h:=chosen_samples_FTC_on (primitiveModel F b n chain) ha hb hab I B hB mesh_error
  simpa only [primitive_at_endpoint,show (fun q=>primitive F b n a q)=
      (fun q=>polynomial F a b n q) from rfl] using h

end ComputableAnalysis.TaylorFTC

namespace ComputableAnalysis.TaylorFTC
open FiniteSampleCalculus UnitPowerCalculus RationalSampleLimits
open ClosedArctanInverse MonotoneAverage

private theorem weight_nonneg {b t : Rat} (ht : t≤b) (n : Nat) : 0≤weight b n t := by
  unfold weight; rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.pow_nonneg (by grind))
    (Rat.le_of_lt ((Rat.inv_pos).2 (RationalMajorant.factorialRat_pos n)))

/-- A finite weighted sum preserves a pointwise magnitude bound. -/
private theorem left_weight_bound (f w : Rat → Rat) (M : Rat)
    {a b : Rat} (hab : a≤b)
    (hw : ∀ t, a≤t → t≤b → 0≤w t)
    (hf : ∀ t, a≤t → t≤b → qabs (f t)≤M*w t) (d : Nat) :
    qabs (left f a b d)≤M*left w a b d := by
  induction d generalizing a b with
  | zero => exact hf a Rat.le_refl hab
  | succ d ih =>
    have hm:=midpoint_between hab
    have h1:=ih hm.1 (fun t ha ht=>hw t ha (Rat.le_trans ht hm.2))
      (fun t ha ht=>hf t ha (Rat.le_trans ht hm.2))
    have h2:=ih hm.2 (fun t ht hb=>hw t (Rat.le_trans hm.1 ht) hb)
      (fun t ht hb=>hf t (Rat.le_trans hm.1 ht) hb)
    have ht:=qabs_add_le (left f a ((a+b)/2) d) (left f ((a+b)/2) b d)
    simp only [left,Rat.div_def,qabs_mul,show qabs ((2:Rat)⁻¹)=(2:Rat)⁻¹ by decide +kernel]
    grind only

/-- Sharp Taylor remainder bound. It is obtained from the finite FTC estimate
for the weighted derivative chain and the same estimate for its polynomial
majorant. Only arbitrary rational slack is discarded. -/
theorem remainder_bound (F : Nat → SampleFunction) (n : Nat)
    (chain : ∀ k, k≤n → Model (F k) (F (k+1)))
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a<b)
    (M : Rat) (hM : 0≤M)
    (last_bound : ∀ t q, a≤t → t≤b → qabs (F (n+1) t q)≤M) :
    ∀ eps : QPos, ∃ N, ∀ q, N≤q →
      qabs (F 0 b q-polynomial F a b n q) ≤
        M*weight b (n+1) a+eps.val := by
  let g:=primitiveModel F b n chain
  let w:=weightModel b (n+1)
  let K:= (g.errorBound+M*w.errorBound)*(b-a)*(b-a)
  have hh : 0≤b-a := by grind
  have hK : 0≤K := Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.add_nonneg g.errorBound_nonneg (Rat.mul_nonneg hM w.errorBound_nonneg)) hh) hh
  have hs : Small (fun d=>K*meshRadius d) :=
    small_of_geometric_bound K hK (fun d=>by
      rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg hK (Rat.le_of_lt (meshRadius_pos d)))]
      exact Rat.le_refl)
  intro eps
  obtain ⟨d,hd⟩:=hs eps
  obtain ⟨N,hN⟩:=finite_telescope g d ha hb hab
  obtain ⟨Nw,hNw⟩:=finite_telescope w d ha hb hab
  refine ⟨max N Nw,fun q hq=>?_⟩
  have h1:=hN q (by omega)
  have h2:=hNw q (by omega)
  change qabs (weight b (n+1) b-weight b (n+1) a-
    (b-a)*left (fun t=> -weight b n t) a b d) ≤w.errorBound*(b-a)*(b-a)*meshRadius d at h2
  rw [weight_at_endpoint] at h2
  have hn : (fun t=> -weight b n t)=(fun t=>(-1)*weight b n t) := by funext t;grind only
  rw [hn,left_mul] at h2
  have he2 : (0:Rat)-weight b (n+1) a-(b-a)*((-1)*left (weight b n) a b d)=
      (b-a)*left (weight b n) a b d-weight b (n+1) a := by grind only
  rw [he2] at h2
  have h2p:=self_le_qabs ((b-a)*left (weight b n) a b d-weight b (n+1) a)
  have hb2:=Rat.mul_le_mul_of_nonneg_left (Rat.le_trans h2p h2) hM
  have hsample:=left_weight_bound (fun t=>remainderSample F b n t q) (weight b n) M
    (Rat.le_of_lt hab) (fun t _ ht=>weight_nonneg ht n) (by
      intro t hat htb
      unfold remainderSample
      rw [qabs_mul,qabs_eq_self_of_nonneg (weight_nonneg htb n)]
      have ht:=Rat.mul_le_mul_of_nonneg_left (last_bound t q hat htb) (weight_nonneg htb n)
      simpa only [Rat.mul_comm] using ht) d
  have hscaled:=Rat.mul_le_mul_of_nonneg_left hsample hh
  have ht:=qabs_add_le
    (F 0 b q-polynomial F a b n q-(b-a)*left (fun t=>remainderSample F b n t q) a b d)
    ((b-a)*left (fun t=>remainderSample F b n t q) a b d)
  have het : (F 0 b q-polynomial F a b n q-(b-a)*left (fun t=>remainderSample F b n t q) a b d)+
      (b-a)*left (fun t=>remainderSample F b n t q) a b d = F 0 b q-polynomial F a b n q := by grind only
  rw [het,qabs_mul,qabs_eq_self_of_nonneg hh] at ht
  change qabs (primitive F b n b q-primitive F b n a q-
    (b-a)*left (fun t=>remainderSample F b n t q) a b d)≤_ at h1
  rw [primitive_at_endpoint] at h1
  change qabs (F 0 b q-polynomial F a b n q-
    (b-a)*left (fun t=>remainderSample F b n t q) a b d)≤_ at h1
  have hsmall:=Rat.le_trans (self_le_qabs (K*meshRadius d)) (hd d (Nat.le_refl d))
  dsimp [K] at hsmall
  grind only

/-- The remainder estimate constrains every pair of output stages of the
actual value and polynomial computations. This is an interval assertion,
not a claim about an unconstructed limiting real. -/
theorem approximation_intervals (F : Nat → SampleFunction) (n : Nat)
    (chain : ∀ k, k≤n → Model (F k) (F (k+1)))
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a<b)
    (M : Rat) (hM : 0≤M)
    (last_bound : ∀ t q, a≤t → t≤b → qabs (F (n+1) t q)≤M)
    {value poly : RealRaw} (value_valid : value.Valid) (poly_valid : poly.Valid)
    (value_sample : ∀ q, IntervalSelections.InBox (F 0 b q) (value.compute q))
    (poly_sample : ∀ q, IntervalSelections.InBox (polynomial F a b n q) (poly.compute q)) :
    ∀ j k, (QInterval.expand (poly.compute j) (M*weight b (n+1) a)).Overlaps (value.compute k) :=
  IntervalSelections.expanded_overlaps_of_selected_error poly_valid value_valid
    (fun q=>polynomial F a b n q) (fun q=>F 0 b q) poly_sample value_sample _
    (remainder_bound F n chain ha hb hab M hM last_bound)

end ComputableAnalysis.TaylorFTC

namespace ComputableAnalysis.TaylorFTC
open FiniteSampleCalculus RationalSampleLimits ClosedArctanInverse MonotoneAverage

/-- Taylor's formula as an equality of native computations. The polynomial,
function value, and remainder integral are independently supplied valid raws;
their rational samples are related to the finite formula above. -/
theorem integral_remainder_equiv (F : Nat → SampleFunction) (n : Nat)
    (chain : ∀ k, k≤n → Model (F k) (F (k+1)))
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a<b)
    (I : Nat → Rat) (B : Rat) (hB : 0≤B)
    (mesh_error : ∀ d q, d≤q →
      qabs (I q-(b-a)*left (fun t=>remainderSample F b n t q) a b d) ≤ B*meshRadius d)
    {value poly remainder : RealRaw}
    (value_valid : value.Valid) (poly_valid : poly.Valid) (remainder_valid : remainder.Valid)
    (value_sample : ∀ q, IntervalSelections.InBox (F 0 b q) (value.compute q))
    (poly_sample : ∀ q, IntervalSelections.InBox (polynomial F a b n q) (poly.compute q))
    (integral_sample : ∀ q, IntervalSelections.InBox (I q) (remainder.compute q)) :
    value.Equiv (RealRaw.add poly remainder) := by
  have h:=integral_remainder F n chain ha hb hab I B hB mesh_error
  apply equiv_of_close value_valid (RealRaw.add_valid poly_valid remainder_valid)
    (fun q=>F 0 b q) (fun q=>polynomial F a b n q+I q) value_sample
  · intro q
    have hp:=poly_sample q;have hi:=integral_sample q
    change (poly.compute q).lo+(remainder.compute q).lo≤polynomial F a b n q+I q ∧
      polynomial F a b n q+I q≤(poly.compute q).hi+(remainder.compute q).hi
    unfold IntervalSelections.InBox at hp hi
    constructor <;> grind only
  · have he : (fun q=>F 0 b q-(polynomial F a b n q+I q))=
        (fun q=> -(I q-(F 0 b q-polynomial F a b n q))) := by funext q;grind only
    unfold Close
    rw [he]
    exact small_neg h

end ComputableAnalysis.TaylorFTC
