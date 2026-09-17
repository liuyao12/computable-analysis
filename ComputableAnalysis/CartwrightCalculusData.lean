import ComputableAnalysis.CartwrightEvaluationData
import ComputableAnalysis.FiniteRationalPowers
import ComputableAnalysis.CartwrightTrigCalculus
import ComputableAnalysis.CartwrightMomentBounds

/-! Shared finite polynomial models, sample comparisons and endpoint estimates.
No moment recurrence or general FTC application is proved in this module. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse SinPiIntegral IntervalSelections
open FiniteSampleCalculus RationalSampleLimits

private theorem zero_abs : qabs (0:Rat)=0 := by decide +kernel
private theorem qsubzero (x : Rat) : x-0=x := by grind

/-- Differentiation of the finite polynomial weight, without real calculus. -/
def weightDerivative : Nat → Rat → Rat
  | 0, _ => 0
  | n+1, x => -2*((n+1:Nat):Rat)*x*weight n x

def singleWeightModel : Model (fun x _ => 1-x*x) (fun x _ => -2*x) :=
  ((Model.const 1).sub (Model.identity.mul Model.identity)).congr
    (fun _ _ => rfl) (by intro x q; grind)

def weightModel : (n : Nat) → Model (fun x _ => weight n x) (fun x _ => weightDerivative n x)
  | 0 => (Model.const 1).congr
      (by intro x q; simp only [weight,Rat.pow_zero]) (fun _ _ => rfl)
  | n+1 => ((weightModel n).mul singleWeightModel).congr
      (by intro x q; simp only [weight,Rat.pow_succ])
      (by
        intro x q
        cases n with
        | zero => simp only [weightDerivative,weight,Rat.pow_zero,Rat.natCast_add,
            Rat.natCast_ofNat,Rat.zero_add];grind only
        | succ n =>
          simp only [weightDerivative,weight,Rat.pow_succ,Rat.natCast_add,Rat.natCast_ofNat]
          grind only)

def weightedCoordinateModel (n : Nat) :
    Model (fun x _ => x*weight (n+1) x)
      (fun x _ => weight (n+1) x-2*((n+1:Nat):Rat)*x*x*weight n x) :=
  (Model.identity.mul (weightModel (n+1))).congr (fun _ _=>rfl)
    (by intro x q;simp only [weightDerivative];grind only)

def frequencyModel : Model (fun _ q => frequencySample q) (fun _ _ => 0) :=
  Model.constant frequencySample 2 (by decide +kernel) (fun q => by
    have h:=frequencySample_bounds q
    rw [qabs_eq_self_of_nonneg (by grind : 0≤frequencySample q)]
    exact h.2)

def recurrencePrimitive (n : Nat) (x : Rat) (q : Nat) : Rat :=
  frequencySample q*weight (n+2) x*ClockTrigonometry.s x q-
    2*((n+2:Nat):Rat)*x*weight (n+1) x*ClockTrigonometry.c x q

def recurrenceDerivative (n : Nat) (x : Rat) (q : Nat) : Rat :=
  frequencySample q*frequencySample q*sample (n+2) x q-
    recurrenceA n*sample (n+1) x q+recurrenceB n*sample n x q

def firstPrimitive (x : Rat) (q : Nat) : Rat :=
  frequencySample q*(1-x*x)*ClockTrigonometry.s x q-2*x*ClockTrigonometry.c x q

def firstDerivative (x : Rat) (q : Nat) : Rat :=
  frequencySample q*frequencySample q*sample 1 x q-2*sample 0 x q

private theorem chosen_mesh_error (n d q : Nat) (hdq : d≤q) :
    qabs (momentSample n q-MonotoneAverage.left (fun x=>sample n x q) 0 1 d)≤meshRadius d := by
  have h:=MonotoneAverage.mesh_error (fun x=>sample n x q) (sample_decreases n q)
    (sample_unit n (x:=1) ⟨by decide,by decide⟩ q).1
    (sample_unit n (x:=0) ⟨by decide,by decide⟩ q).2 hdq
  have he : momentSample n q-MonotoneAverage.left (fun x=>sample n x q) 0 1 d =
    -(MonotoneAverage.left (fun x=>sample n x q) 0 1 d-momentSample n q) := by grind
  rw [he,qabs_neg]
  exact h

theorem frequency_square_bound (q : Nat) : qabs (frequencySample q*frequencySample q)≤4 := by
  have h:=frequencySample_bounds q
  have h0 : 0≤frequencySample q := by grind
  have hh:=mul_abs_bound (by decide : (0:Rat)≤2)
    (by rw [qabs_eq_self_of_nonneg h0];exact h.2) (by rw [qabs_eq_self_of_nonneg h0];exact h.2)
  have he : (2:Rat)*2=4 := by decide +kernel
  rw [he] at hh
  exact hh

theorem recurrence_mesh_error (n d q : Nat) (hdq : d≤q) :
    qabs (recurrenceSamples n q-MonotoneAverage.left (fun x=>recurrenceDerivative n x q) 0 1 d)≤
      (4+recurrenceA n+recurrenceB n)*meshRadius d := by
  have hA:=recurrenceA_nonneg n;have hB:=recurrenceB_nonneg n
  have h1:=mul_abs_bound (by decide : (0:Rat)≤4) (frequency_square_bound q) (chosen_mesh_error (n+2) d q hdq)
  have h2:=mul_abs_bound hA (by rw [qabs_eq_self_of_nonneg hA];exact Rat.le_refl) (chosen_mesh_error (n+1) d q hdq)
  have h3:=mul_abs_bound hB (by rw [qabs_eq_self_of_nonneg hB];exact Rat.le_refl) (chosen_mesh_error n d q hdq)
  have h4:=qabs_sub_le
    ((frequencySample q*frequencySample q)*(momentSample (n+2) q-MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d))
    (recurrenceA n*(momentSample (n+1) q-MonotoneAverage.left (fun x=>sample (n+1) x q) 0 1 d))
  have h5:=qabs_add_le
    (((frequencySample q*frequencySample q)*(momentSample (n+2) q-MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d))-
      (recurrenceA n*(momentSample (n+1) q-MonotoneAverage.left (fun x=>sample (n+1) x q) 0 1 d)))
    (recurrenceB n*(momentSample n q-MonotoneAverage.left (fun x=>sample n x q) 0 1 d))
  unfold recurrenceSamples recurrenceDerivative
  rw [MonotoneAverage.left_add,MonotoneAverage.left_sub,MonotoneAverage.left_mul,
      MonotoneAverage.left_mul,MonotoneAverage.left_mul]
  have he : ((frequencySample q*frequencySample q)*(momentSample (n+2) q-MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d))-
      (recurrenceA n*(momentSample (n+1) q-MonotoneAverage.left (fun x=>sample (n+1) x q) 0 1 d))+
      (recurrenceB n*(momentSample n q-MonotoneAverage.left (fun x=>sample n x q) 0 1 d)) =
      frequencySample q*frequencySample q*momentSample (n+2) q-recurrenceA n*momentSample (n+1) q+recurrenceB n*momentSample n q-
        ((frequencySample q*frequencySample q)*MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d-
         recurrenceA n*MonotoneAverage.left (fun x=>sample (n+1) x q) 0 1 d+
         recurrenceB n*MonotoneAverage.left (fun x=>sample n x q) 0 1 d) := by grind only
  rw [he] at h5
  grind only

theorem first_mesh_error (d q : Nat) (hdq : d≤q) :
    qabs (firstSamples q-MonotoneAverage.left (fun x=>firstDerivative x q) 0 1 d)≤6*meshRadius d := by
  have h1:=mul_abs_bound (by decide : (0:Rat)≤4) (frequency_square_bound q) (chosen_mesh_error 1 d q hdq)
  have h2:=mul_abs_bound (by decide : (0:Rat)≤2)
    (by decide +kernel : qabs (2:Rat)≤2) (chosen_mesh_error 0 d q hdq)
  have ht:=qabs_sub_le
    ((frequencySample q*frequencySample q)*(momentSample 1 q-MonotoneAverage.left (fun x=>sample 1 x q) 0 1 d))
    ((2:Rat)*(momentSample 0 q-MonotoneAverage.left (fun x=>sample 0 x q) 0 1 d))
  unfold firstSamples firstDerivative
  rw [MonotoneAverage.left_sub,MonotoneAverage.left_mul,MonotoneAverage.left_mul]
  have he : ((frequencySample q*frequencySample q)*(momentSample 1 q-MonotoneAverage.left (fun x=>sample 1 x q) 0 1 d))-
    ((2:Rat)*(momentSample 0 q-MonotoneAverage.left (fun x=>sample 0 x q) 0 1 d)) =
    frequencySample q*frequencySample q*momentSample 1 q-2*momentSample 0 q-
      ((frequencySample q*frequencySample q)*MonotoneAverage.left (fun x=>sample 1 x q) 0 1 d-
       2*MonotoneAverage.left (fun x=>sample 0 x q) 0 1 d) := by grind only
  rw [he] at ht
  grind only

theorem zero_mesh_error (d q : Nat) (hdq : d≤q) :
    qabs (frequencySample q*momentSample 0 q-MonotoneAverage.left
      (fun x=>frequencySample q*ClockTrigonometry.c x q) 0 1 d)≤2*meshRadius d := by
  have hp:=frequencySample_bounds q
  have h1:=mul_abs_bound (by decide : (0:Rat)≤2)
    (by rw [qabs_eq_self_of_nonneg (by grind : 0≤frequencySample q)];exact hp.2)
    (chosen_mesh_error 0 d q hdq)
  have hf : (fun x=>sample 0 x q)=(fun x=>ClockTrigonometry.c x q) := by
    funext x;simp only [sample,weight,Rat.pow_zero,Rat.one_mul]
  rw [hf] at h1
  rw [MonotoneAverage.left_mul]
  have he : frequencySample q*(momentSample 0 q-MonotoneAverage.left (fun x=>ClockTrigonometry.c x q) 0 1 d)=
    frequencySample q*momentSample 0 q-frequencySample q*MonotoneAverage.left (fun x=>ClockTrigonometry.c x q) 0 1 d := by grind
  rw [he] at h1
  exact h1

theorem sine_zero_small : Small (ClockTrigonometry.s 0) := by
  apply small_of_geometric_bound 28 (by decide)
  intro q
  have h:=(ClockTrigonometry.sample_endpoint (t:=0) (Or.inl rfl) q).2
  simpa only [qsubzero] using h

theorem cosine_one_small : Small (ClockTrigonometry.c 1) := by
  apply small_of_geometric_bound 56 (by decide)
  intro q
  have h:=(ClockTrigonometry.sample_endpoint (t:=1) (Or.inr rfl) q).1
  rw [Rat.sub_self,qsubzero] at h
  exact h

theorem sine_one_close : Close (ClockTrigonometry.s 1) (fun _=>1) := by
  apply small_of_geometric_bound 28 (by decide)
  exact fun q=>(ClockTrigonometry.sample_endpoint (t:=1) (Or.inr rfl) q).2

theorem frequency_bounded : Bounded frequencySample 2 := fun q=>by
  have h:=frequencySample_bounds q
  rw [qabs_eq_self_of_nonneg (by grind : 0≤frequencySample q)]
  exact h.2

theorem recurrence_boundary_small (n : Nat) : Small (fun q=>recurrencePrimitive n 1 q-recurrencePrimitive n 0 q) := by
  have h:=small_neg (small_bounded_mul (by decide : (0:Rat)≤2) frequency_bounded sine_zero_small)
  have he : (fun q=>recurrencePrimitive n 1 q-recurrencePrimitive n 0 q)=
      (fun q=> -(frequencySample q*ClockTrigonometry.s 0 q)) := by
    funext q
    unfold recurrencePrimitive
    simp only [weight,Rat.one_mul,Rat.mul_zero,Rat.zero_mul,Rat.sub_self,qsubzero,FiniteRationalPowers.one_pow]
    rw [FiniteRationalPowers.zero_pow (by omega : 0<n+2),FiniteRationalPowers.zero_pow (by omega : 0<n+1)]
    grind only
  rw [he]
  exact h

theorem first_boundary_small : Small (fun q=>firstPrimitive 1 q-firstPrimitive 0 q) := by
  have h1:=small_bounded_mul (qabs_nonneg (2:Rat)) (bounded_const 2) cosine_one_small
  have h2:=small_bounded_mul (by decide : (0:Rat)≤2) frequency_bounded sine_zero_small
  have h:=small_neg (small_add h1 h2)
  have he : (fun q=>firstPrimitive 1 q-firstPrimitive 0 q)=
      (fun q=> -(2*ClockTrigonometry.c 1 q+frequencySample q*ClockTrigonometry.s 0 q)) := by
    funext q;unfold firstPrimitive;grind only
  rw [he]
  exact h


end ComputableAnalysis.CartwrightMoments
