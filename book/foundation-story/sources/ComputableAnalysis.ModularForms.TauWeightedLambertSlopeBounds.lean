import ComputableAnalysis.ModularForms.TauWeightedLambertSlope

/-! Summable bounds for actual weighted Lambert derivatives in arbitrary degree. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The weighted monomial slope times the actual Lambert derivative. -/
def weightedLambertSlope (q : Scalar) (R : Rat) (k : Nat) (hR : 0≤R)
    (hl : 4*R≤(1:Rat)/2) (hq : Small q.val R) (N : Nat) : Scalar :=
  let d := lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius R N)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
    (nomePowerScalar_small q R hR hq N)
  ⟨scaleRat (((N+1:Nat):Rat)^(k+1)) (mul (LocalODE.power q.val N) d.val),
    scaleRat_valid (mul_valid (LocalODE.power_valid _ q.property N) d.property)⟩

/-- A summable polynomial-times-geometric bound for the literal slope. -/
theorem weightedLambertSlope_bound (q : Scalar) (R : Rat) (k : Nat) (hR : 0≤R)
    (hl : 4*R≤(1:Rat)/2) (hq : Small q.val R) (N : Nat) :
    Small (weightedLambertSlope q R k hR hl hq N).val
      (64*((N+1:Nat):Rat)^(k+1)*(2*R)^N) := by
  have hg := nomeGeometricSum_bound (nomePowerScalar q N) (nomePowerRadius R N)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
    (nomePowerScalar_small q R hR hq N)
  have hv := nomeGeometricSum_valid (nomePowerScalar q N) (nomePowerRadius R N)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
    (nomePowerScalar_small q R hR hq N)
  have hd := Small.mul hv hv (by decide +kernel : (0:Rat)≤4) (by decide +kernel : (0:Rat)≤4) hg hg
  have hp := LocalODE.power_small q.val q.property R hR hq N
  have hm := Small.mul (LocalODE.power_valid _ q.property N)
    (lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius R N)
      (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hl N)
      (nomePowerScalar_small q R hR hq N)).property
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hR))
    (by decide +kernel : (0:Rat)≤2*4*4) hp hd
  have hs := LocalODE.small_scale
    (Rat.pow_nonneg (n := k+1) (Rat.natCast_nonneg : (0:Rat)≤((N+1:Nat):Rat))) hm
  change Small (weightedLambertSlope q R k hR hl hq N).val
    (((N+1:Nat):Rat)^(k+1)*(2*(2*R)^N*(2*4*4))) at hs
  have he : ((N+1:Nat):Rat)^(k+1)*(2*(2*R)^N*(2*4*4))=
      64*((N+1:Nat):Rat)^(k+1)*(2*R)^N := by grind only
  rw [he] at hs
  exact hs

private theorem index_power_bound (N k : Nat) : ((N+1:Nat):Rat)^k≤((2:Rat)^k)^N := by
  have hi := lambertIndex_bound N
  have hx : 0≤((N+1:Nat):Rat) := Rat.natCast_nonneg
  have hy : 0≤(2:Rat)^N := Rat.pow_nonneg (by decide +kernel)
  have hp : ((N+1:Nat):Rat)^k≤((2:Rat)^N)^k := by
    induction k with
    | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
    | succ k ih =>
      rw [Rat.pow_succ,Rat.pow_succ]
      have h1 := Rat.mul_le_mul_of_nonneg_right ih hx
      have h2 := Rat.mul_le_mul_of_nonneg_left hi (Rat.pow_nonneg hy (n := k))
      exact Rat.le_trans h1 h2
  have he (n j : Nat) : ((2:Rat)^n)^j=((2:Rat)^j)^n := by
    have mulpow (a b : Rat) (m : Nat) : (a*b)^m=a^m*b^m := by
      induction m with
      | zero => simp only [Rat.pow_zero]; grind only
      | succ m ih => rw [Rat.pow_succ,ih,Rat.pow_succ,Rat.pow_succ]; grind only
    induction n with
    | zero => simp only [Rat.pow_zero]; induction j with
      | zero => rfl
      | succ j ih => rw [Rat.pow_succ,ih]; grind only
    | succ n ih => rw [Rat.pow_succ,mulpow,ih,Rat.pow_succ]
  rw [he] at hp
  exact hp

private theorem product_power (a b : Rat) (N : Nat) : a^N*b^N=(a*b)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero]; grind only
  | succ N ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ]; grind only

/-- Pure geometric bound, summable whenever its explicit ratio is below one. -/
theorem weightedLambertSlope_geometric_bound (q : Scalar) (R : Rat) (k : Nat) (hR : 0≤R)
    (hl : 4*R≤(1:Rat)/2) (hq : Small q.val R) (N : Nat) :
    Small (weightedLambertSlope q R k hR hl hq N).val (64*(2^(k+1)*(2*R))^N) := by
  have h := weightedLambertSlope_bound q R k hR hl hq N
  have hi := Rat.mul_le_mul_of_nonneg_right (index_power_bound N (k+1))
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤2) hR) : 0≤(2*R)^N)
  rw [product_power] at hi
  have hm := Rat.mul_le_mul_of_nonneg_left hi (by decide +kernel : (0:Rat)≤64)
  apply h.mono
  grind only

/-- The actual weighted derivative inherits the literal slope's geometric estimate. -/
theorem tauWeightedLambertDerivative_bound (q : Scalar) (hq : tauEulerNomeDomain q) (k N : Nat) :
    Small ((tauWeightedLambertMap_holomorphic k N).derivative q hq).val
      (64*(2^(k+1)*(2*(1/1024:Rat)))^N) :=
  Small.congr (weightedLambertSlope q (1/1024) k (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) N).property
    ((tauWeightedLambertMap_holomorphic k N).derivative q hq).property
    (equiv_symm (tauWeightedLambertSlope_actual q hq k N))
    (weightedLambertSlope_geometric_bound q (1/1024) k (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) N)

/-- The slope candidate respects represented equality and independent radii. -/
theorem weightedLambertSlope_congr (q w : Scalar) (R S : Rat) (k : Nat)
    (hR : 0≤R) (hS : 0≤S) (hlR : 4*R≤(1:Rat)/2) (hlS : 4*S≤(1:Rat)/2)
    (hq : Small q.val R) (hw : Small w.val S) (he : q.val.Equiv w.val) (N : Nat) :
    (weightedLambertSlope q R k hR hlR hq N).val.Equiv
      (weightedLambertSlope w S k hS hlS hw N).val := by
  have hd := lambertDiskDerivative_congr (nomePowerScalar q N) (nomePowerScalar w N)
    (nomePowerRadius R N) (nomePowerRadius S N)
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_nonneg S hS N)
    (nomePowerRadius_local R hR hlR N) (nomePowerRadius_local S hS hlS N)
    (nomePowerScalar_small q R hR hq N) (nomePowerScalar_small w S hS hw N)
    (LocalODE.power_congr q.val w.val q.property w.property he (N+1))
  exact scaleRat_equiv (mul_equiv (LocalODE.power_valid _ q.property N)
    (LocalODE.power_valid _ w.property N)
    (lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius R N)
      (nomePowerRadius_nonneg R hR N) (nomePowerRadius_local R hR hlR N)
      (nomePowerScalar_small q R hR hq N)).property
    (lambertDiskDerivative (nomePowerScalar w N) (nomePowerRadius S N)
      (nomePowerRadius_nonneg S hS N) (nomePowerRadius_local S hS hlS N)
      (nomePowerScalar_small w S hS hw N)).property
    (LocalODE.power_congr q.val w.val q.property w.property he N) hd)

end ComputableAnalysis.ModularForms
