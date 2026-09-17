import ComputableAnalysis.BetaLaws

/-! Polynomial FTC proves the beta recurrence. All quadrature algorithms and
convergence certificates were supplied independently in BetaData. -/
namespace ComputableAnalysis.BetaIntegral
open ClosedArctanInverse RationalSampleLimits IntervalSelections
open FiniteSampleCalculus UnitPowerCalculus

private def complementModel : Model (fun x _=>1-x) (fun _ _=> -1) :=
  ((Model.const 1).sub Model.identity).congr (fun _ _=>rfl) (by intro x q;grind only)

def primitive (m n : Nat) (x : Rat) : Rat := integrand (m+1) (n+1) x
def derivative (m n : Nat) (x : Rat) : Rat :=
  ((m+1:Nat):Rat)*integrand m (n+1) x-((n+1:Nat):Rat)*integrand (m+1) n x

def primitiveModel (m n : Nat) : Model (fun x _=>primitive m n x) (fun x _=>derivative m n x) := by
  apply ((modelPower Model.identity (m+1)).mul (modelPower complementModel (n+1))).congr
  · intro x q;rfl
  · intro x q
    change (((m+1:Nat):Rat)*x^m*1)*(1-x)^(n+1)+x^(m+1)*
      (((n+1:Nat):Rat)*(1-x)^n*(-1))=derivative m n x
    unfold derivative integrand
    grind only

private theorem primitive_endpoints (m n : Nat) : primitive m n 1=0 ∧ primitive m n 0=0 := by
  unfold primitive integrand
  rw [show (1:Rat)-1=0 by decide +kernel,show (1:Rat)-0=1 by decide +kernel,
    FiniteRationalPowers.zero_pow (by omega : 0<n+1),FiniteRationalPowers.zero_pow (by omega : 0<m+1),Rat.mul_zero,Rat.zero_mul]
  exact ⟨rfl,rfl⟩

private theorem base_law (m : Nat) :
    Close (fun q=>((m+1:Nat):Rat)*sample m 0 q) (fun _=>1) := by
  let F : Model (fun x _=>x^(m+1)) (fun x _=>((m+1:Nat):Rat)*integrand m 0 x) :=
    (modelPower Model.identity (m+1)).congr (fun _ _=>rfl) (by
      intro x q;change ((m+1:Nat):Rat)*x^m*1=_
      simp only [integrand,Rat.pow_zero,Rat.mul_one])
  have h:=chosen_samples_FTC F (fun q=>((m+1:Nat):Rat)*sample m 0 q)
    (((m+1:Nat):Rat)*(m:Rat)) (Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg) (by
      intro d q hdq
      have hc : 0≤((m+1:Nat):Rat) := Rat.natCast_nonneg
      have ht:=mul_abs_bound hc (by rw [qabs_eq_self_of_nonneg hc];exact Rat.le_refl) (mesh_error m 0 d q hdq)
      rw [MonotoneAverage.left_mul]
      have he : ((m+1:Nat):Rat)*(sample m 0 q-MonotoneAverage.left (integrand m 0) 0 1 d)=
        ((m+1:Nat):Rat)*sample m 0 q-((m+1:Nat):Rat)*MonotoneAverage.left (integrand m 0) 0 1 d := by grind only
      rw [he] at ht
      simpa only [Nat.add_zero,Rat.mul_assoc] using ht)
  simpa only [FiniteRationalPowers.one_pow,FiniteRationalPowers.zero_pow (by omega : 0<m+1),
    show (1:Rat)-0=1 by decide +kernel] using h

private theorem parts_law (m n : Nat) : Small (fun q=>
    ((m+1:Nat):Rat)*sample m (n+1) q-((n+1:Nat):Rat)*sample (m+1) n q) := by
  let A : Rat:=((m+1:Nat):Rat)
  let B : Rat:=((n+1:Nat):Rat)
  have hA : 0≤A := Rat.natCast_nonneg
  have hB : 0≤B := Rat.natCast_nonneg
  have h:=chosen_samples_FTC (primitiveModel m n)
    (fun q=>A*sample m (n+1) q-B*sample (m+1) n q)
    (A*((m+(n+1):Nat):Rat)+B*(((m+1)+n:Nat):Rat))
    (Rat.add_nonneg (Rat.mul_nonneg hA Rat.natCast_nonneg) (Rat.mul_nonneg hB Rat.natCast_nonneg)) (by
      intro d q hdq
      have h1:=mul_abs_bound hA (by rw [qabs_eq_self_of_nonneg hA];exact Rat.le_refl) (mesh_error m (n+1) d q hdq)
      have h2:=mul_abs_bound hB (by rw [qabs_eq_self_of_nonneg hB];exact Rat.le_refl) (mesh_error (m+1) n d q hdq)
      have ht:=qabs_sub_le (A*(sample m (n+1) q-MonotoneAverage.left (integrand m (n+1)) 0 1 d))
        (B*(sample (m+1) n q-MonotoneAverage.left (integrand (m+1) n) 0 1 d))
      unfold derivative
      rw [MonotoneAverage.left_sub,MonotoneAverage.left_mul,MonotoneAverage.left_mul]
      change qabs (A*sample m (n+1) q-B*sample (m+1) n q-
        (A*MonotoneAverage.left (integrand m (n+1)) 0 1 d-B*MonotoneAverage.left (integrand (m+1) n) 0 1 d))≤_
      have he : A*(sample m (n+1) q-MonotoneAverage.left (integrand m (n+1)) 0 1 d)-
        B*(sample (m+1) n q-MonotoneAverage.left (integrand (m+1) n) 0 1 d)=
        A*sample m (n+1) q-B*sample (m+1) n q-
        (A*MonotoneAverage.left (integrand m (n+1)) 0 1 d-B*MonotoneAverage.left (integrand (m+1) n) 0 1 d) := by grind only
      rw [he] at ht
      grind only)
  have e:=primitive_endpoints m n
  have ht : Close (fun q=>A*sample m (n+1) q-B*sample (m+1) n q) (fun _=>0) := by
    simpa only [e.1,e.2,Rat.sub_self] using h
  exact small_of_close_zero ht

theorem sample_decomposition (m n q : Nat) : sample m n q=sample m (n+1) q+sample (m+1) n q := by
  change MonotoneAverage.left (integrand m n) 0 1 q=
    MonotoneAverage.left (integrand m (n+1)) 0 1 q+MonotoneAverage.left (integrand (m+1) n) 0 1 q
  rw [←MonotoneAverage.left_add]
  have he : integrand m n=(fun x=>integrand m (n+1) x+integrand (m+1) n x) := by
    funext x;simp only [integrand,Rat.pow_succ];grind only
  rw [he]

theorem step_viaFTC (m n : Nat) : Small (stepResidual m n) := by
  have h:=parts_law m n
  have he : (fun q=>((m+1:Nat):Rat)*sample m (n+1) q-((n+1:Nat):Rat)*sample (m+1) n q)=stepResidual m n := by
    funext q;unfold stepResidual
    rw [sample_decomposition m n q]
    simp only [Rat.natCast_add,Rat.natCast_ofNat]
    grind only
  rw [he] at h;exact h

theorem lawsViaFTC : Laws := ⟨base_law,step_viaFTC⟩
theorem evaluation_viaFTC (m n : Nat) : Statement m n := evaluation_of_laws lawsViaFTC m n
theorem factorial_viaFTC (m n : Nat) : FactorialStatement m n := factorial_of_laws lawsViaFTC m n

end ComputableAnalysis.BetaIntegral
