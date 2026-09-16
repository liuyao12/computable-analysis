import ComputableAnalysis.FiniteFirstOrderCalculus
import ComputableAnalysis.RationalErrorCalculus

/-!
# A finite FTC with explicit subdivision and evaluation schedules

The derivative certificate is a finite first-order remainder estimate. The
particular schedule used by the moment computations makes accumulated errors
shrink. This module neither defines an integral by endpoints nor constructs
an unrestricted integral operator.
-/
namespace ComputableAnalysis.UniformGridFTC
open CartwrightClockBounds CartwrightMoments CartwrightFiniteSums FiniteRiemannAlgebra
open RationalErrorCalculus
abbrev Unit := CartwrightClockBounds.Unit
abbrev Family := Nat → Rat → Rat

def riemann (f : Family) (k : Nat) : Rat :=
  sum (fun j=>step k*f (sampleStage k) (grid k j)) (cells k)

def endpoint (f : Family) (k : Nat) : Rat := f (sampleStage k) 1-f (sampleStage k) 0

structure Certificate (F D : Family) where
  coefficient : Rat
  nonnegative : 0≤coefficient
  residual : ∀q a b,Unit a→Unit b→a≤b→
    qabs (F q b-F q a-(b-a)*D q a) ≤ coefficient*((b-a)*(b-a)+delta q)

theorem stage_error (k : Nat) : (cells k:Rat)*(step k*step k+delta (sampleStage k))≤2*delta k := by
  have he : delta (2*k)=delta k*delta k := by
    simp only [delta,ClosedArctanInverse.meshRadius,Rat.div_def,Rat.one_mul]
    have hadd (a : Rat) (m n : Nat) : a^(m+n)=a^m*a^n := by
      induction n with
      | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
      | succ n ih => rw [show m+(n+1)=(m+n)+1 by omega,Rat.pow_succ,ih,Rat.pow_succ];grind
    rw [show 2*k=k+k by omega,hadd,Rat.inv_mul_rev]
  have hd:=ClosedArctanInverse.meshRadius_antitone (n:=2*k) (m:=sampleStage k) (by unfold sampleStage;omega)
  change delta (sampleStage k)≤delta (2*k) at hd
  rw [he,←step_eq k] at hd
  have hn:=Rat.natCast_nonneg (a:=cells k)
  have hm:=Rat.mul_le_mul_of_nonneg_left hd hn
  have hc:=cells_step k
  have hid : (cells k:Rat)*(step k*step k)=step k := by
    rw [←Rat.mul_assoc,hc,Rat.one_mul]
  rw [hid] at hm
  rw [←step_eq k,Rat.mul_add,hid]
  grind

/-- The general FTC estimate: a finite telescope, with the source error retained. -/
theorem finite_bound {F D : Family} (h : Certificate F D) (k : Nat) :
    qabs (endpoint F k-riemann D k)≤2*h.coefficient*delta k := by
  have ht:=telescope_bound (s:=fun j=>F (sampleStage k) (grid k j))
    (c:=fun j=>D (sampleStage k) (grid k j)) (h:=step k) (p:=1)
    (e:=h.coefficient*(step k*step k+delta (sampleStage k))) (cells k) (by
      intro j hj
      have ha:=grid_unit k j (by omega)
      have hb:=grid_unit k (j+1) (by omega)
      have hg:=grid_step k j
      have hs:=step_pos k
      have hl : grid k j≤grid k (j+1) := by grind
      have hh:=h.residual (sampleStage k) (grid k j) (grid k (j+1)) ha hb hl
      rw [hg] at hh
      simpa only [Rat.one_mul] using hh)
  rw [grid_last,grid_zero,Rat.one_mul] at ht
  have hs:=Rat.mul_le_mul_of_nonneg_left (stage_error k) h.nonnegative
  change qabs (endpoint F k-riemann D k)≤_ at ht
  grind

theorem conclusion {F D : Family} (h : Certificate F D) : Near (riemann D) (endpoint F) := by
  apply Near.symm
  exact Near.geometric (2*h.coefficient) (Rat.mul_nonneg (by decide +kernel) h.nonnegative) (finite_bound h)

/-- Finite circle data, shared by the FTC and direct-sum arguments. -/
structure CircleData (v dv : Family) : Prop where
  bounded : ∀q t,Unit t→qabs (v q t)≤1
  increment : ∀q a b,Unit a→Unit b→a≤b→
    qabs (v q b-v q a)≤80*((b-a)+delta q)
  residual : ∀q a b,Unit a→Unit b→a≤b→
    qabs (v q b-v q a-(b-a)*dv q a)≤20000*((b-a)*(b-a)+delta q)

def sine : Family := fun q t=>CartwrightClockBounds.s t q
def cosine : Family := fun q t=>CartwrightClockBounds.c t q
def sineDerivative : Family := fun q t=>p q*CartwrightClockBounds.c t q
def cosineDerivative : Family := fun q t=> -(p q*CartwrightClockBounds.s t q)

theorem sine_data : CircleData sine sineDerivative where
  bounded := by
    intro q t ht
    have h:=ClockTrigonometry.sample_bounds t q
    rw [sine,qabs_eq_self_of_nonneg h.2.2.1]
    exact h.2.2.2
  increment := by
    intro q a b ha hb hab
    have h:=sine_distance ha hb q
    rw [qabs_eq_self_of_nonneg (by grind : 0≤b-a)] at h
    have he:=Rat.le_of_lt (ClosedArctanInverse.meshRadius_pos q)
    change qabs (s b q-s a q)≤_
    grind
  residual := by
    intro q a b ha hb hab
    have h:=sine_step_error ha hb hab q
    have hsq:=rat_square_nonneg_basic (b-a)
    have he:=Rat.le_of_lt (ClosedArctanInverse.meshRadius_pos q)
    change qabs (s b q-s a q-(b-a)*(p q*c a q))≤_
    rw [←Rat.mul_assoc]
    grind

theorem cosine_data : CircleData cosine cosineDerivative where
  bounded := by
    intro q t ht
    have h:=ClockTrigonometry.sample_bounds t q
    rw [cosine,qabs_eq_self_of_nonneg h.1]
    exact h.2.1
  increment := by
    intro q a b ha hb hab
    have h:=cosine_distance ha hb q
    rw [qabs_eq_self_of_nonneg (by grind : 0≤b-a)] at h
    have he:=Rat.le_of_lt (ClosedArctanInverse.meshRadius_pos q)
    change qabs (c b q-c a q)≤_
    grind
  residual := by
    intro q a b ha hb hab
    have h:=cosine_step_error ha hb hab q
    change qabs (c b q-c a q-(b-a)*(-(p q*s a q)))≤_
    have he : c b q-c a q-(b-a)*(-(p q*s a q))=c b q-c a q+(b-a)*p q*s a q := by grind
    rw [he];exact h

/-- The product rule supplies, rather than assumes, the FTC certificate. -/
def product {f df : Rat → Rat} (F : FiniteFirstOrderCalculus.Data f df)
    {g dg : Family} (G : CircleData g dg) :
    Certificate (fun q t=>f t*g q t) (fun q t=>df t*g q t+f t*dg q t) where
  coefficient:=F.remainder+80*F.slope+20000*F.size
  nonnegative:=by
    have h1:=F.remainder_nonnegative;have h2:=F.slope_nonnegative;have h3:=F.size_nonnegative;grind
  residual:=by
    intro q a b ha hb hab
    have h0 : 0≤b-a := by grind
    have h1 : b-a≤1 := by have ha0:=ha.1;have hb1:=hb.2;grind
    have d0:=Rat.le_of_lt (ClosedArctanInverse.meshRadius_pos q)
    have sq0:=Rat.mul_nonneg h0 h0
    have eF:=F.error a b ha hb hab
    have bG:=G.bounded q b hb
    have dG:=G.increment q a b ha hb hab
    have eG:=G.residual q a b ha hb hab
    have bF:=F.value_bound a ha
    have dF:=F.slope_bound a ha
    have hE : qabs ((f b-f a-(b-a)*df a)*g q b)≤F.remainder*(b-a)*(b-a) := by
      rw [qabs_mul]
      have h := Rat.mul_le_mul_of_nonneg_left bG (qabs_nonneg (f b-f a-(b-a)*df a))
      grind
    have hD : qabs ((b-a)*df a*(g q b-g q a))≤80*F.slope*((b-a)*(b-a)+delta q) := by
      rw [qabs_mul,qabs_mul,qabs_eq_self_of_nonneg h0]
      have hh0:=Rat.mul_le_mul_of_nonneg_left dF h0
      have hh1:=Rat.mul_le_mul_of_nonneg_right hh0 (qabs_nonneg (g q b-g q a))
      have hh2:=Rat.mul_le_mul_of_nonneg_left dG (Rat.mul_nonneg h0 F.slope_nonnegative)
      have hsmall:=Rat.mul_le_mul_of_nonneg_right h1 (Rat.mul_nonneg F.slope_nonnegative d0)
      grind
    have hF : qabs (f a*(g q b-g q a-(b-a)*dg q a))≤20000*F.size*((b-a)*(b-a)+delta q) := by
      rw [qabs_mul]
      have hh1:=Rat.mul_le_mul_of_nonneg_right bF (qabs_nonneg (g q b-g q a-(b-a)*dg q a))
      have hh2:=Rat.mul_le_mul_of_nonneg_left eG F.size_nonnegative
      grind
    have ht1:=qabs_add_le ((f b-f a-(b-a)*df a)*g q b) ((b-a)*df a*(g q b-g q a))
    have ht2:=qabs_add_le (((f b-f a-(b-a)*df a)*g q b)+((b-a)*df a*(g q b-g q a)))
      (f a*(g q b-g q a-(b-a)*dg q a))
    have he : ((f b-f a-(b-a)*df a)*g q b)+((b-a)*df a*(g q b-g q a))+
      f a*(g q b-g q a-(b-a)*dg q a)=
      f b*g q b-f a*g q a-(b-a)*(df a*g q a+f a*dg q a) := by grind
    rw [he] at ht2
    have he0:=Rat.mul_nonneg F.remainder_nonnegative d0
    grind

end ComputableAnalysis.UniformGridFTC
