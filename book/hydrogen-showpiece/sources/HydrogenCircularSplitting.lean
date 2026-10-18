import ComputableAnalysis.HydrogenCircularComputations

/-! Exact cancellation-free splitting for the constructed circular-channel
energies. It is valid at every coupling, including zero, and invariant under
input names. The radial solutions are constructed in HydrogenCircularRadial;
Cartesian lifting is constructed in HydrogenCircularCartesianState; operator
classification remains a separate obligation. -/
namespace ComputableAnalysis.HydrogenCircularSplitting
open ComputableCoefficient QuotientBridge PositiveRootArithmetic HydrogenCoupling HydrogenCircularComputations
set_option autoImplicit false
set_option maxHeartbeats 1000000
local instance : Lean.Grind.CommRing ComplexRawQuotient.Value := ComplexRawQuotient.instCommRingValue
local instance (n : Nat) : OfNat ComplexRawQuotient.Value n :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).ofNat n
local instance : NatCast ComplexRawQuotient.Value :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).natCast

variable (k : Nat) (hk : 0<k) (A : Coupling)

def angularSum : Value := Value.add (HydrogenCircularComputations.exponent k hk A) (angular k)
def principalSquare : Value := Value.mul (angular (k+1)) (angular (k+1))
def energySum : Value := Value.add (upperEnergy k A) (lowerEnergy k hk A)
def denominator : Value := Value.mul (Value.mul (Value.mul (angularSum k hk A) (principalSquare k))
  (denominatorSquared k hk A)) (energySum k hk A)

private theorem mul_positive (x y : Value) (hx : ∀ n,0<(x.real.compute n).lo) (hy : ∀ n,0<(y.real.compute n).lo) (n : Nat) :
    0<((Value.mul x y).real.compute n).lo := by
  rw [mul_compute_nonnegative _ _ (fun n => Rat.le_of_lt (hx n)) (fun n => Rat.le_of_lt (hy n)) n]
  exact Rat.mul_pos (hx n) (hy n)

theorem angular_sum_positive (n : Nat) : 0<((angularSum k hk A).real.compute n).lo := by
  have h := exponent_positive k hk A n
  have hn : 0<(k:Rat) := Rat.natCast_pos.mpr hk
  change 0<((HydrogenCircularComputations.exponent k hk A).real.compute n).lo+(k:Rat)
  grind only

theorem energy_sum_positive (n : Nat) : 0<((energySum k hk A).real.compute n).lo := by
  have h := upper_energy_positive k A n
  have h' := lower_energy_positive k hk A n
  change 0<((upperEnergy k A).real.compute n).lo+((lowerEnergy k hk A).real.compute n).lo
  grind only

theorem denominator_positive (n : Nat) : 0<((denominator k hk A).real.compute n).lo :=
  mul_positive _ _ (mul_positive _ _ (mul_positive _ _ (angular_sum_positive k hk A)
    (mul_positive (angular (k+1)) (angular (k+1))
      (fun _ => by change (0:Rat)<((k+1:Nat):Rat);exact Rat.natCast_pos.mpr (Nat.zero_lt_succ k))
      (fun _ => by change (0:Rat)<((k+1:Nat):Rat);exact Rat.natCast_pos.mpr (Nat.zero_lt_succ k))))
    (fun n => by have h := denominator_squared_lower k hk A n;change 0<((denominatorSquared k hk A).real.compute n).lo;grind only))
    (energy_sum_positive k hk A) n

def inverse : Value := Value.positiveInv (denominator k hk A) 0 (denominator_positive k hk A 0)
def coefficient : Value := Value.mul (Value.rational 2) (inverse k hk A)
def splitting : Value := Value.sub (upperEnergy k A) (lowerEnergy k hk A)

theorem principal_identity : (angular (k+1)).real.preferred.Equiv (Value.add (angular k) (Value.rational 1)).real.preferred := by
  apply Value.equiv_of_samples _ _ 0
  intro m hm s hs
  change ((k+1:Nat):Rat)=(k:Rat)+1
  rw [Rat.natCast_add]
  rfl

private theorem splitting_algebra (s t u H L D N K : ComplexRawQuotient.Value)
    (hN : N=K+1) (hS : s*s+u=K*K) (hT : t*t+u=N*N)
    (hD : D=(s+1)*(s+1)+u) (hH : H*H*(N*N)=t*t) (hL : L*L*D=(s+1)*(s+1)) :
    (H-L)*((s+K)*(N*N)*D*(H+L))=2*u*u := by
  have hGap : N*N-D=2*(K-s) := by grind only
  have hCancel : (s+K)*(K-s)=u := by grind only
  have hEq : (H*H-L*L)*(N*N)*D=t*t*D-(s+1)*(s+1)*(N*N) := by
    clear hGap hCancel hN hS hT hD
    grind only
  have hInner : t*t*D-(s+1)*(s+1)*(N*N)=u*(N*N-D) := by
    clear hH hL hEq hCancel hGap hN hS
    grind only
  calc
    _ = (s+K)*((H*H-L*L)*(N*N)*D) := by grind only
    _ = (s+K)*(u*(N*N-D)) := by rw [hEq,hInner]
    _ = 2*u*u := by rw [hGap];grind only

/-- Multiplying by the constructed denominator exposes the exact second
power of the squared coupling, before any reciprocal cancellation. -/
theorem cleared_identity :
    (Value.mul (splitting k hk A) (denominator k hk A)).real.preferred.Equiv
      (Value.mul (Value.rational 2) (Value.mul A.value A.value)).real.preferred := by
  have hN := quotient_eq (principal_identity k)
  have hS := quotient_eq (indicial k hk A)
  have hT := quotient_eq (indicial (k+1) (Nat.zero_lt_succ k) A)
  have hD := quotient_eq (HydrogenCircularComputations.denominator_square k hk A)
  have hI := quotient_eq (y := Value.rational 1) (positiveInv_identity (HydrogenCircularComputations.denominator k hk A) 0
    (HydrogenCircularComputations.denominator_positive k hk A 0))
  have hJ := quotient_eq (y := Value.rational 1) (upper_inverse_identity k)
  simp only [quotient_add,quotient_mul,quotient_one] at hN hS hT hD hI hJ
  change quotient (HydrogenCircularComputations.denominator k hk A)*quotient (denominatorInverse k hk A)=1 at hI
  have hiSq := congrArg (fun x : ComplexRawQuotient.Value => x*x) hI
  have hjSq := congrArg (fun x : ComplexRawQuotient.Value => x*x) hJ
  have hLSq : quotient (lowerEnergy k hk A)*quotient (lowerEnergy k hk A)*quotient (denominatorSquared k hk A)=
      quotient (shifted k hk A)*quotient (shifted k hk A) := by
    have hRe : (quotient (HydrogenCircularComputations.denominator k hk A)*quotient (denominatorInverse k hk A))*
      (quotient (HydrogenCircularComputations.denominator k hk A)*quotient (denominatorInverse k hk A))=
      (quotient (HydrogenCircularComputations.denominator k hk A)*quotient (HydrogenCircularComputations.denominator k hk A))*
      (quotient (denominatorInverse k hk A)*quotient (denominatorInverse k hk A)) := by grind only
    rw [hRe,hD] at hiSq
    simp only [lowerEnergy,quotient_mul]
    grind only
  have hHSq : quotient (upperEnergy k A)*quotient (upperEnergy k A)*(quotient (angular (k+1))*quotient (angular (k+1)))=
      quotient (HydrogenCircularComputations.exponent (k+1) (Nat.zero_lt_succ k) A)*
      quotient (HydrogenCircularComputations.exponent (k+1) (Nat.zero_lt_succ k) A) := by
    simp only [upperEnergy,quotient_mul]
    grind only
  have hDef : quotient (denominatorSquared k hk A)=
      (quotient (HydrogenCircularComputations.exponent k hk A)+1)*(quotient (HydrogenCircularComputations.exponent k hk A)+1)+quotient A.value := by
    simp only [denominatorSquared,shifted,quotient_add,quotient_mul,quotient_one]
    rfl
  simp only [shifted,quotient_add,quotient_one] at hLSq
  have hAlg := splitting_algebra _ _ _ _ _ _ _ _ hN hS hT hDef hHSq hLSq
  apply raw_equiv_of_quotient_eq
  simp only [splitting,denominator,angularSum,principalSquare,energySum,quotient_add,quotient_sub,quotient_mul]
  have hTwo : quotient (Value.rational 2)=2 := rfl
  rw [hTwo]
  grind only

/-- Exact rationalization of the actual circular-channel energy difference.
The coefficient is computed even at zero coupling. -/
theorem splitting_identity : (splitting k hk A).real.preferred.Equiv
    (Value.mul (Value.mul A.value A.value) (coefficient k hk A)).real.preferred := by
  have h := quotient_eq (cleared_identity k hk A)
  have hi := quotient_eq (y := Value.rational 1) (positiveInv_identity (denominator k hk A) 0 (denominator_positive k hk A 0))
  simp only [quotient_mul,quotient_one] at h hi
  change quotient (denominator k hk A)*quotient (inverse k hk A)=1 at hi
  apply raw_equiv_of_quotient_eq
  simp only [coefficient,quotient_mul]
  have hm := congrArg (fun x : ComplexRawQuotient.Value => x*quotient (inverse k hk A)) h
  have hc : (quotient (splitting k hk A)*quotient (denominator k hk A))*quotient (inverse k hk A)=quotient (splitting k hk A) := by
    rw [ComplexRawQuotient.mul_assoc,hi]
    grind only
  rw [hc] at hm
  exact hm.trans (by grind only)

theorem coefficient_positive (n : Nat) : 0<((coefficient k hk A).real.compute n).lo :=
  mul_positive _ _ (fun _ => by change (0:Rat)<2;decide +kernel)
    (Order.positiveInv_zero_positive (denominator k hk A) (denominator_positive k hk A 0)) n

/-- Different names for the same coupling give the same computed splitting
and rationalized coefficient. -/
theorem splitting_congr (A' : Coupling) (h : A.squared.preferred.Equiv A'.squared.preferred) :
    (splitting k hk A).real.preferred.Equiv (splitting k hk A').real.preferred := by
  apply raw_equiv_of_quotient_eq
  have hU := quotient_eq (upper_energy_congr k A A' h)
  have hL := quotient_eq (lower_energy_congr k hk A A' h)
  simp only [splitting,quotient_sub]
  rw [hU,hL]

theorem coefficient_congr (A' : Coupling) (h : A.squared.preferred.Equiv A'.squared.preferred) :
    (coefficient k hk A).real.preferred.Equiv (coefficient k hk A').real.preferred := by
  have hs := add_congr (exponent_congr k hk A A' h) (Value.equiv_refl (angular k))
  have hD := add_congr (Value.mul_congr
    (add_congr (exponent_congr k hk A A' h) (Value.equiv_refl (Value.rational 1)))
    (add_congr (exponent_congr k hk A A' h) (Value.equiv_refl (Value.rational 1)))) (A.value_equiv A' h)
  have hE := add_congr (upper_energy_congr k A A' h) (lower_energy_congr k hk A A' h)
  have hd := Value.mul_congr (Value.mul_congr (Value.mul_congr hs (Value.equiv_refl (principalSquare k))) hD) hE
  exact Value.mul_congr (Value.equiv_refl _) (positiveInv_congr hd 0 0 (denominator_positive k hk A 0) (denominator_positive k hk A' 0))

end ComputableAnalysis.HydrogenCircularSplitting
