import ComputableAnalysis.RationalLipschitzIntegral
import ComputableAnalysis.UnitPowerCalculus

/-! Integer beta integrals are independently computed by rational dyadic sums.
Their exact polynomial samples have no evaluation error; a proved Lipschitz
constant m+n controls the subdivision schedule even across the single turn. -/
namespace ComputableAnalysis.BetaIntegral
open ClosedArctanInverse CartwrightMoments UnitPowerCalculus IntervalSelections
open RationalLipschitzIntegral FiniteSampleCalculus

def integrand (m n : Nat) (x : Rat) : Rat := x^m*(1-x)^n

theorem complement_unit {x : Rat} (hx : Unit x) : Unit (1-x) := by
  have h0:=hx.1;have h1:=hx.2;constructor <;> grind only

theorem integrand_unit (m n : Nat) {x : Rat} (hx : Unit x) : Unit (integrand m n x) := by
  have a:=power_unit hx m;have b:=power_unit (complement_unit hx) n
  have h:=Rat.mul_le_mul_of_nonneg_right a.2 b.1
  exact ⟨Rat.mul_nonneg a.1 b.1,by unfold integrand;grind only⟩

theorem integrand_lipschitz (m n : Nat) : Lipschitz (integrand m n) ((m+n:Nat):Rat) := by
  intro x y hx hy
  have h1:=power_difference hx hy m
  have h2:=power_difference (complement_unit hx) (complement_unit hy) n
  have he : (1-x)-(1-y)= -(x-y) := by grind only
  rw [he,qabs_neg] at h2
  have h3:=mul_abs_bound (by decide : (0:Rat)≤1) (abs_le_unit (power_unit (complement_unit hx) n)) h1
  have h4:=mul_abs_bound (by decide : (0:Rat)≤1) (abs_le_unit (power_unit hy m)) h2
  have ht:=qabs_add_le ((1-x)^n*(x^m-y^m)) (y^m*((1-x)^n-(1-y)^n))
  have eqn : (1-x)^n*(x^m-y^m)+y^m*((1-x)^n-(1-y)^n)=integrand m n x-integrand m n y := by
    unfold integrand;grind only
  rw [eqn] at ht
  simp only [Rat.natCast_add]
  grind only

def data (m n : Nat) : RationalLipschitzIntegral.Data where
  sample := integrand m n
  range := fun _ hx=>integrand_unit m n hx
  constant := m+n
  bound := integrand_lipschitz m n

def integral (m n : Nat) : RealRaw := RationalLipschitzIntegral.raw (data m n)
def sample (m n q : Nat) : Rat := RationalLipschitzIntegral.centre (data m n) q

theorem integral_valid (m n : Nat) : (integral m n).Valid := RationalLipschitzIntegral.valid (data m n)
theorem sample_mem (m n q : Nat) : InBox (sample m n q) ((integral m n).compute q) :=
  RationalLipschitzIntegral.contains_future (data m n) q q (Nat.le_refl q)

theorem mesh_error (m n d q : Nat) (hdq : d≤q) :
    qabs (sample m n q-MonotoneAverage.left (integrand m n) 0 1 d)≤((m+n:Nat):Rat)*meshRadius d :=
  RationalLipschitzIntegral.mesh_error (integrand m n) ((m+n:Nat):Rat) Rat.natCast_nonneg
    (integrand_lipschitz m n) d q hdq


/-- Exact rational samples leave only the subdivision error. -/
theorem integral_width (m n k : Nat) : ((integral m n).compute k).width ≤
    2*((m+n:Nat):Rat)*meshRadius k := by
  have h:=RationalLipschitzIntegral.width (data m n) k
  change ((integral m n).compute k).width ≤ 2*(((m+n:Nat):Rat)*meshRadius k) at h
  simpa only [Rat.mul_assoc] using h

/-- Rational arithmetic endpoint, recursively specified before any integral theorem. -/
def value (m : Nat) : Nat → Rat
  | 0 => 1/((m+1:Nat):Rat)
  | n+1 => ((n+1:Nat):Rat)/((m+n+2:Nat):Rat)*value m n

/-- The common native computational proposition. -/
def Statement (m n : Nat) : Prop := (integral m n).Equiv (RealRaw.ofRat (value m n))

/-- A purely arithmetic interpretation of the recurrence endpoint. -/
private theorem factorial_cast_step (k : Nat) :
    (factorial (k+1):Rat)=((k+1:Nat):Rat)*(factorial k:Rat) := by
  rw [factorial,Rat.natCast_mul]

theorem factorial_value (m : Nat) : (n : Nat) →
    (factorial (m+n+1):Rat)*value m n=(factorial m:Rat)*(factorial n:Rat)
  | 0 => by
    have hp : 0<((m+1:Nat):Rat) := (Rat.natCast_pos).2 (by omega)
    have hc:=Rat.mul_inv_cancel ((m+1:Nat):Rat) (Rat.ne_of_gt hp)
    rw [show m+0+1=m+1 by omega,factorial_cast_step,value]
    change (((m+1:Nat):Rat)*(factorial m:Rat))*(1/((m+1:Nat):Rat))=(factorial m:Rat)*1
    simp only [Rat.div_def,Rat.one_mul]
    grind only
  | n+1 => by
    have ih:=factorial_value m n
    have hp : 0<((m+n+2:Nat):Rat) := (Rat.natCast_pos).2 (by omega)
    have hc:=Rat.mul_inv_cancel ((m+n+2:Nat):Rat) (Rat.ne_of_gt hp)
    rw [show m+(n+1)+1=(m+n+1)+1 by omega,factorial_cast_step,factorial_cast_step n,value]
    have hcast : (((m+n+1)+1:Nat):Rat)=((m+n+2:Nat):Rat) := by congr 1 <;> omega
    rw [hcast]
    simp only [Rat.div_def]
    grind only

end ComputableAnalysis.BetaIntegral
