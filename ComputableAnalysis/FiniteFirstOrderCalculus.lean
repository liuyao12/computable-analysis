import ComputableAnalysis.CartwrightDerivativeBounds

/-!
# First-order finite certificates on the unit interval

A quadratic remainder is data sufficient for finite FTC estimates. Polynomial
products are certified by finite algebra. No primitive endpoint identity or
completed real line is included in these hypotheses.
-/
namespace ComputableAnalysis.FiniteFirstOrderCalculus
open CartwrightClockBounds

structure Data (f df : Rat → Rat) where
  size : Rat
  slope : Rat
  remainder : Rat
  size_nonnegative : 0≤size
  slope_nonnegative : 0≤slope
  remainder_nonnegative : 0≤remainder
  value_bound : ∀x,Unit x→qabs (f x)≤size
  slope_bound : ∀x,Unit x→qabs (df x)≤slope
  error : ∀a b,Unit a→Unit b→a≤b→
    qabs (f b-f a-(b-a)*df a)≤remainder*(b-a)*(b-a)

theorem lipschitz {f df : Rat → Rat} (D : Data f df) {a b : Rat}
    (ha : Unit a) (hb : Unit b) (hab : a≤b) :
    qabs (f b-f a)≤(D.slope+D.remainder)*(b-a) := by
  have hh0 : 0≤b-a := by grind
  have hh1 : b-a≤1 := by have h0:=ha.1;have h1:=hb.2;grind
  have he:=D.error a b ha hb hab
  have hd:=D.slope_bound a ha
  have htri:=qabs_add_le (f b-f a-(b-a)*df a) ((b-a)*df a)
  rw [show f b-f a-(b-a)*df a+(b-a)*df a=f b-f a by grind,
    qabs_mul,qabs_eq_self_of_nonneg hh0] at htri
  have hm:=Rat.mul_le_mul_of_nonneg_left hd hh0
  have hh:=Rat.mul_le_mul_of_nonneg_left hh1 (Rat.mul_nonneg D.remainder_nonnegative hh0)
  grind

/-- Product differentiation with a finite quadratic remainder. -/
def product {f df g dg : Rat → Rat} (F : Data f df) (G : Data g dg) :
    Data (fun x=>f x*g x) (fun x=>df x*g x+f x*dg x) where
  size := F.size*G.size
  slope := F.slope*G.size+F.size*G.slope
  remainder := F.remainder*G.size+F.slope*(G.slope+G.remainder)+F.size*G.remainder
  size_nonnegative := Rat.mul_nonneg F.size_nonnegative G.size_nonnegative
  slope_nonnegative := Rat.add_nonneg (Rat.mul_nonneg F.slope_nonnegative G.size_nonnegative)
    (Rat.mul_nonneg F.size_nonnegative G.slope_nonnegative)
  remainder_nonnegative := Rat.add_nonneg
    (Rat.add_nonneg (Rat.mul_nonneg F.remainder_nonnegative G.size_nonnegative)
      (Rat.mul_nonneg F.slope_nonnegative (Rat.add_nonneg G.slope_nonnegative G.remainder_nonnegative)))
    (Rat.mul_nonneg F.size_nonnegative G.remainder_nonnegative)
  value_bound := by
    intro x hx
    rw [qabs_mul]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (F.value_bound x hx) (qabs_nonneg (g x)))
      (Rat.mul_le_mul_of_nonneg_left (G.value_bound x hx) F.size_nonnegative)
  slope_bound := by
    intro x hx
    have ht:=qabs_add_le (df x*g x) (f x*dg x)
    rw [qabs_mul,qabs_mul] at ht
    have h1:=Rat.mul_le_mul_of_nonneg_right (F.slope_bound x hx) (qabs_nonneg (g x))
    have h2:=Rat.mul_le_mul_of_nonneg_left (G.value_bound x hx) F.slope_nonnegative
    have h3:=Rat.mul_le_mul_of_nonneg_right (F.value_bound x hx) (qabs_nonneg (dg x))
    have h4:=Rat.mul_le_mul_of_nonneg_left (G.slope_bound x hx) F.size_nonnegative
    grind
  error := by
    intro a b ha hb hab
    have h0 : 0≤b-a := by grind
    have hsq0:=Rat.mul_nonneg h0 h0
    have ef:=F.error a b ha hb hab
    have eg:=G.error a b ha hb hab
    have lg:=lipschitz G ha hb hab
    have bf:=F.value_bound a ha
    have bg:=G.value_bound b hb
    have dF:=F.slope_bound a ha
    have efg : qabs ((f b-f a-(b-a)*df a)*g b)≤F.remainder*G.size*(b-a)*(b-a) := by
      rw [qabs_mul]
      have h1:=Rat.mul_le_mul_of_nonneg_right ef (qabs_nonneg (g b))
      have h2:=Rat.mul_le_mul_of_nonneg_left bg
        (Rat.mul_nonneg (Rat.mul_nonneg F.remainder_nonnegative h0) h0)
      grind
    have dfg : qabs ((b-a)*df a*(g b-g a))≤F.slope*(G.slope+G.remainder)*(b-a)*(b-a) := by
      rw [qabs_mul,qabs_mul,qabs_eq_self_of_nonneg h0]
      have h1:=Rat.mul_le_mul_of_nonneg_left dF h0
      have h2:=Rat.mul_le_mul_of_nonneg_right h1 (qabs_nonneg (g b-g a))
      have h3:=Rat.mul_le_mul_of_nonneg_left lg (Rat.mul_nonneg h0 F.slope_nonnegative)
      grind
    have feg : qabs (f a*(g b-g a-(b-a)*dg a))≤F.size*G.remainder*(b-a)*(b-a) := by
      rw [qabs_mul]
      have h1:=Rat.mul_le_mul_of_nonneg_right bf (qabs_nonneg (g b-g a-(b-a)*dg a))
      have h2:=Rat.mul_le_mul_of_nonneg_left eg F.size_nonnegative
      grind
    have ht1:=qabs_add_le ((f b-f a-(b-a)*df a)*g b) ((b-a)*df a*(g b-g a))
    have ht2:=qabs_add_le (((f b-f a-(b-a)*df a)*g b)+((b-a)*df a*(g b-g a)))
      (f a*(g b-g a-(b-a)*dg a))
    have he : ((f b-f a-(b-a)*df a)*g b)+((b-a)*df a*(g b-g a))+
      (f a*(g b-g a-(b-a)*dg a))=
      f b*g b-f a*g a-(b-a)*(df a*g a+f a*dg a) := by grind
    rw [he] at ht2
    grind

def constant (c : Rat) : Data (fun _=>c) (fun _=>0) where
  size:=qabs c
  slope:=0
  remainder:=0
  size_nonnegative:=qabs_nonneg c
  slope_nonnegative:=Rat.le_refl
  remainder_nonnegative:=Rat.le_refl
  value_bound:=fun _ _=>Rat.le_refl
  slope_bound:=by intros;decide +kernel
  error:=by intro a b _ _ _; simp only [Rat.sub_self,Rat.mul_zero,Rat.zero_mul];decide +kernel

def coordinate : Data (fun x=>x) (fun _=>1) where
  size:=1
  slope:=1
  remainder:=0
  size_nonnegative:=by decide +kernel
  slope_nonnegative:=by decide +kernel
  remainder_nonnegative:=Rat.le_refl
  value_bound:=by intro x hx; rw [qabs_eq_self_of_nonneg hx.1];exact hx.2
  slope_bound:=by intros;decide +kernel
  error:=by intro a b _ _ _; simp only [Rat.mul_one,Rat.sub_self,Rat.zero_mul];decide +kernel

def quadratic : Data (fun x=>1-x*x) (fun x=> -2*x) where
  size:=1
  slope:=2
  remainder:=1
  size_nonnegative:=by decide +kernel
  slope_nonnegative:=by decide +kernel
  remainder_nonnegative:=by decide +kernel
  value_bound:=by
    intro x hx
    have hh:=Rat.mul_le_mul_of_nonneg_left hx.2 hx.1
    have hz:=Rat.mul_nonneg hx.1 hx.1
    rw [qabs_eq_self_of_nonneg (by grind : 0≤1-x*x)]
    grind
  slope_bound:=by
    intro x hx
    rw [qabs_mul,qabs_eq_self_of_nonneg hx.1]
    have hz : qabs (-2:Rat)=2 := by decide +kernel
    rw [hz]
    have h:=Rat.mul_le_mul_of_nonneg_left hx.2 (by decide +kernel : (0:Rat)≤2)
    grind
  error:=by
    intro a b _ _ hab
    have he : (1-b*b)-(1-a*a)-(b-a)*(-2*a) = -((b-a)*(b-a)) := by grind
    rw [he,qabs_neg,qabs_eq_self_of_nonneg (rat_square_nonneg_basic _),Rat.one_mul]
    exact Rat.le_refl

end ComputableAnalysis.FiniteFirstOrderCalculus

namespace ComputableAnalysis.CartwrightMoments
open FiniteFirstOrderCalculus

def weightDerivative : Nat → Rat → Rat
  | 0 => fun _=>0
  | n+1 => fun t=> -2*((n+1:Nat):Rat)*t*weight n t

def weightData (n : Nat) : Data (weight n) (weightDerivative n) := by
  induction n with
  | zero =>
    have hf : weight 0=(fun _=>1) := by funext t;exact Rat.pow_zero _
    rw [hf];exact constant 1
  | succ n ih =>
    have hh:=product ih quadratic
    have hf : (fun t=>weight n t*(1-t*t))=weight (n+1) := by funext t; exact (Rat.pow_succ _ _).symm
    have hd : (fun t=>weightDerivative n t*(1-t*t)+weight n t*(-2*t))=weightDerivative (n+1) := by
      funext t
      cases n with
      | zero => simp only [weightDerivative,weight,Rat.pow_zero]; grind
      | succ n => simp only [weightDerivative,weight,Rat.pow_succ,Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel];grind
    rw [hf,hd] at hh
    exact hh

def auxWeight (n : Nat) (t : Rat) : Rat := t*weight n t

def auxDerivative (n : Nat) (t : Rat) : Rat := weight n t+t*weightDerivative n t

def auxData (n : Nat) : Data (auxWeight n) (auxDerivative n) := by
  have h:=product coordinate (weightData n)
  change Data (fun x=>x*weight n x) (fun x=>weight n x+x*weightDerivative n x)
  simpa only [Rat.one_mul] using h

theorem derivative_weight_succ (n : Nat) (t : Rat) :
    weightDerivative (n+1) t= -2*((n+1:Nat):Rat)*auxWeight n t := by
  unfold weightDerivative auxWeight
  grind

theorem derivative_aux_zero (t : Rat) : auxDerivative 0 t=1 := by
  simp only [auxDerivative,weight,weightDerivative,Rat.pow_zero,Rat.mul_zero,Rat.add_zero]

theorem derivative_aux_succ (n : Nat) (t : Rat) :
    auxDerivative (n+1) t=(2*((n+1:Nat):Rat)+1)*weight (n+1) t-
      2*((n+1:Nat):Rat)*weight n t := by
  unfold auxDerivative weightDerivative weight
  rw [Rat.pow_succ]
  grind

end ComputableAnalysis.CartwrightMoments
