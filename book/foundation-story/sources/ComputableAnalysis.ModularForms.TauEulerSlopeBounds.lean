import ComputableAnalysis.ModularForms.TauEulerFactorDerivative

/-! Uniform geometric majorants for the actual degree-24 Euler-factor slopes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem factor_power_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/512) (hq : Small q.val r) (N : Nat) :
    Small (LocalODE.power (sub one (LocalODE.power q.val (N+1))) 23) 2 := by
  have h := tauEulerFactor_power_deviation_bound q r hr hrMax hq N 23 (by decide +kernel)
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤2 by decide +kernel)
  have hp := tauEulerGeometricPower_le_first (2*r) ht (Rat.le_trans hmax (by decide +kernel)) N
  have h46 := Rat.mul_le_mul_of_nonneg_left hp (show (0:Rat)≤46 by decide +kernel)
  have h46r := Rat.mul_le_mul_of_nonneg_left hmax (show (0:Rat)≤46 by decide +kernel)
  have hbound : 46*(2*r)^(N+1)≤1 := by
    have hh : 46*(2*r)≤1 := Rat.le_trans h46r (by decide +kernel)
    exact Rat.le_trans h46 hh
  have ho : one.Valid := ofQComplex_valid _
  have hone : Small one 1 := by
    simpa only [LocalODE.power,Rat.pow_zero] using
      LocalODE.power_small zero (ofQComplex_valid _) 0 Rat.le_refl (Small.zero Rat.le_refl) 0
  let P := LocalODE.power (sub one (LocalODE.power q.val (N+1))) 23
  have hP : P.Valid := LocalODE.power_valid _ (sub_valid ho (LocalODE.power_valid _ q.property (N+1))) 23
  have he : (add (sub P one) one).Equiv P := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid hP ho) ho) (hright := hP)
    let p := ComplexRawQuotient.ofRaw P hP
    change (p-1)+1=p
    grind only
  have hs := Small.congr (add_valid (sub_valid hP ho) ho) hP he (LocalODE.small_add h hone)
  apply hs.mono
  change 2*((23:Nat):Rat)*(2*r)^(N+1)+1≤2
  have hc : (2:Rat)*((23:Nat):Rat)=46 := by decide +kernel
  rw [hc]
  grind only

/-- The actual executable slope has a polynomial-times-geometric majorant. -/
theorem tauEulerFactorSlope_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/512) (hq : Small q.val r) (N : Nat) :
    Small (tauEulerFactorSlope q N).val (96*((N+1:Nat):Rat)*(2*r)^N) := by
  have hp := LocalODE.power_small _ q.property r hr hq N
  have hs := LocalODE.small_scale (Rat.natCast_nonneg : 0≤((N+1:Nat):Rat)) hp
  have hd := SeriesLimitLaws.small_neg hs
  have hf := factor_power_bound q r hr hrMax hq N
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hD : 0≤((N+1:Nat):Rat)*(2*r)^N := Rat.mul_nonneg Rat.natCast_nonneg (Rat.pow_nonneg ht)
  have hm := Small.mul
    (LocalODE.power_valid _ (sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ q.property _)) 23)
    (neg_valid (scaleRat_valid (LocalODE.power_valid _ q.property N)))
    (show (0:Rat)≤2 by decide +kernel) hD hf hd
  have h := LocalODE.small_scale (show (0:Rat)≤24 by decide +kernel) hm
  apply h.mono
  grind only

private theorem index_geometric_bound (N : Nat) : ((N+1:Nat):Rat)≤(2:Rat)^N := by
  induction N with
  | zero => change (1:Rat)≤1; exact Rat.le_refl
  | succ N ih =>
    have hn : 0≤(N:Rat) := Rat.natCast_nonneg
    have hh := Rat.mul_le_mul_of_nonneg_left ih (show (0:Rat)≤2 by decide +kernel)
    rw [Rat.pow_succ]
    simp only [Rat.natCast_add,show ((1:Nat):Rat)=1 by rfl] at *
    grind only

private theorem product_power_identity (t : Rat) (N : Nat) :
    (2:Rat)^N*t^N=(2*t)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero,Rat.mul_one]
  | succ N ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ]; grind only

/-- A pure geometric majorant for the actual Euler-factor derivative. -/
theorem tauEulerFactorSlope_geometric_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/512) (hq : Small q.val r) (N : Nat) :
    Small (tauEulerFactorSlope q N).val (96*(4*r)^N) := by
  have h := tauEulerFactorSlope_bound q r hr hrMax hq N
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hi := Rat.mul_le_mul_of_nonneg_right (index_geometric_bound N) (Rat.pow_nonneg ht : 0≤(2*r)^N)
  rw [product_power_identity] at hi
  have h96 := Rat.mul_le_mul_of_nonneg_left hi (show (0:Rat)≤96 by decide +kernel)
  apply h.mono
  have he : (2:Rat)*(2*r)=4*r := by grind only
  rw [he] at h96
  grind only

theorem tauEulerFactor_actual_derivative_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/512) (hq : Small q.val r) (N : Nat) :
    Small ((tauMapPower_holomorphic (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) 24).derivative q trivial).val
      (96*(4*r)^N) :=
  Small.congr (tauEulerFactorSlope q N).property
    ((tauMapPower_holomorphic (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) 24).derivative q trivial).property
    (equiv_symm (tauEulerFactorSlope_actual q N))
    (tauEulerFactorSlope_geometric_bound q r hr hrMax hq N)

theorem tauEulerFactorSlope_majorant_shrinks (r : Rat) (hr : 0≤r) (hrMax : r≤(1:Rat)/512) :
    ShrinksToZero (fun N => 96*(4*r)^N) := by
  have hq : 0≤4*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤4 by decide +kernel)
  have h := LocalODE.tail_bound_shrinks 24 (4*r) (by decide +kernel) hq
    (Rat.le_trans hmax (by decide +kernel))
  simpa only [show (4:Rat)*24=96 by decide +kernel] using h

end ComputableAnalysis.ModularForms
