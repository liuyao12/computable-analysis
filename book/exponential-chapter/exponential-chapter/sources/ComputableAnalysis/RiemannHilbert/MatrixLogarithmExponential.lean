import ComputableAnalysis.RiemannHilbert.MatrixLogarithmExponentialEstimates

/-! The general near-identity exponential–logarithm identity. The actual
exponential of the Taylor field and identity plus the parameter times the
operator satisfy the same justified uniform ODE and initial condition. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixLogarithm
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField
variable {n : Nat}
set_option maxHeartbeats 2000000

theorem exponential_ode_remainder (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (eps H : QPos) (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z)
    (hH : H.val ≤ (exponentialDelta eps).val) (hzw : Small (sub z.val w.val) H.val)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound (UniformSegment.remainder (slope E hE hsmall)
      (fun v hv => (exponential E hE hsmall v hv).eval x) w z hw hz) ((eps.val*H.val)*B) :=
  bound_congr (Fiber.sub_congr (Setoid.refl _)
    (Fiber.scale_congr (equiv_refl _ (sub_valid z.property w.property))
      (Setoid.symm (exponential_slope_commutes E hE hsmall w hw x))))
    (exponential_uniform_remainder E hE hsmall eps H w z hw hz hH hzw B hB x hx)

theorem identityPlus_slope (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (w : Scalar) (hw : interior radius.val w) (x : Fiber n) :
    (slope E hE hsmall w hw).eval ((identityPlus E w).eval x) ≈ E.eval x :=
  Setoid.trans ((resolvent E hE hsmall w hw).congr
    (identityPlus_intertwines E E E hE (fun _ => Setoid.refl _) w x))
    (resolvent_right E hE hsmall w hw (E.eval x))

theorem identityPlus_remainder_zero (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (w z : Scalar) (hw : interior radius.val w) (hz : interior radius.val z) (x : Fiber n) :
    UniformSegment.remainder (slope E hE hsmall) (fun v _ => (identityPlus E v).eval x) w z hw hz ≈ Fiber.zero n := by
  apply Setoid.trans (Fiber.sub_congr (Setoid.refl _)
    (Fiber.scale_congr (equiv_refl _ (sub_valid z.property w.property)) (identityPlus_slope E hE hsmall w hw x)))
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Fiber.sub (Fiber.sub ((identityPlus E z).eval x) ((identityPlus E w).eval x))
      (Fiber.scale ⟨sub z.val w.val,sub_valid z.property w.property⟩ (E.eval x))).property i)
    (hright := ofQComplex_valid _)
  let X := ComplexRawQuotient.ofRaw (x.val i) (x.property i)
  let Y := ComplexRawQuotient.ofRaw ((E.eval x).val i) ((E.eval x).property i)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  change ((X+Z*Y)-(X+W*Y))-(Z-W)*Y=0
  grind only

theorem identityPlus_bound (E : ValueMap (Fiber n) (Fiber n)) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((identityPlus E z).eval x) ((9/8 : Rat)*B) := by
  have hs := bound_add hx (bound_scale (c := z) (by decide +kernel)
    (Rat.mul_nonneg (by decide +kernel : (0 : Rat) ≤ contraction) hB) (interior_bound radius.val z hz) (hsmall B hB x hx))
  have he : B+2*radius.val*(contraction*B)=(9/8 : Rat)*B := by
    have hq : 2*radius.val*contraction=(1/8 : Rat) := by decide +kernel
    grind only
  rw [he] at hs
  exact hs

theorem exponential_initial (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E) :
    (exponential E hE hsmall ⟨zero,ofQComplex_valid _⟩ (interior_zero radius.val radius.property)).Equiv ValueMap.identity := by
  let Z := ValueMap.zeroBetween n n
  have hZ := ValueMap.zeroBetween_linear n n
  intro x
  exact Setoid.trans (MatrixExponential.value_congr _ Z
    (parameterValue_linear E hE hsmall _ (interior_zero radius.val radius.property)) hZ
    (parameterValue_initial E hsmall) _ _ (equiv_refl _ MatrixExponential.operatorUnit.property) x x (Setoid.refl _))
    (Setoid.trans (MatrixExponential.value_nilpotent Z hZ (fun _ => Setoid.refl _) MatrixExponential.operatorUnit x)
      (Setoid.trans (Fiber.add_congr (Setoid.refl _) (Fiber.scale_zero _)) (Fiber.add_zero x)))

theorem identityPlus_initial (E : ValueMap (Fiber n) (Fiber n)) :
    (identityPlus E ⟨zero,ofQComplex_valid _⟩).Equiv ValueMap.identity :=
  fun x => Setoid.trans (Fiber.add_congr (Setoid.refl _) (Fiber.zero_scale (E.eval x))) (Fiber.add_zero x)

/-- Exponentiating the actual Taylor matrix sum gives identity plus zE
throughout its parameter domain, for every represented small linear E. -/
theorem exponential_identityPlus (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E)
    (z : Scalar) (hz : interior radius.val z) : (exponential E hE hsmall z hz).Equiv (identityPlus E z) := by
  intro x
  let p : Scalar := ⟨zero,ofQComplex_valid _⟩
  have hp := interior_zero radius.val radius.property
  let B := LocalSystem.initialBound x
  have hB := LocalSystem.initialBound_nonneg x
  let f : UniformSegment.Field (n := n) (interior radius.val) := fun v hv => (exponential E hE hsmall v hv).eval x
  let g : UniformSegment.Field (n := n) (interior radius.val) := fun v _ => (identityPlus E v).eval x
  have hW : Small (AffineSegment.displacement p z).val radius.val :=
    Small.congr z.property (AffineSegment.displacement p z).property (equiv_symm (MatrixExponential.offset_zero z))
      (interior_bound radius.val z hz)
  have hfrem : ∀ (eps H : QPos) w v hw hv,
      H.val ≤ (exponentialDelta (inputError B hB eps)).val → Small (sub v.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (slope E hE hsmall) f w v hw hv) (eps.val*H.val) := by
    intro eps H w v hw hv hH hvw
    have hs := exponential_ode_remainder E hE hsmall (inputError B hB eps) H w v hw hv hH hvw B hB x (LocalSystem.initialBound_valid x)
    have hb := Rat.mul_le_mul_of_nonneg_right (inputError_bound B hB eps) (Rat.le_of_lt H.property)
    intro i
    exact (hs i).mono (by grind only)
  have hgrem : ∀ (eps H : QPos) w v hw hv, H.val ≤ (1 : Rat) → Small (sub v.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (slope E hE hsmall) g w v hw hv) (eps.val*H.val) := by
    intro eps H w v hw hv _ _
    exact bound_congr (Setoid.symm (identityPlus_remainder_zero E hE hsmall w v hw hv x))
      (bound_zero _ (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property)))
  exact UniformSegment.equal (interior radius.val) p z hp hz (MatrixExponential.disc_affine_mem radius p z hp hz)
    radius hW (slope E hE hsmall) f g (1/8) (exponentialBound*B) ((9/8)*B)
    (by decide +kernel) (by decide +kernel) (Rat.mul_nonneg exponentialBound_nonneg hB)
    (Rat.mul_nonneg (by decide +kernel) hB)
    (fun w v hw hv hwv => exponential_congr E hE hsmall w v hw hv hwv x)
    (fun w v _ _ hwv => identityPlus_congr E E (ValueMap.equiv_refl E) w v hwv x)
    (Setoid.trans (exponential_initial E hE hsmall x) (Setoid.symm (identityPlus_initial E x)))
    (fun v hv => exponential_bound E hE hsmall v hv B hB x (LocalSystem.initialBound_valid x))
    (fun v hv => identityPlus_bound E hsmall v hv B hB x (LocalSystem.initialBound_valid x))
    (slope_linear E hE hsmall) (slope_bound E hE hsmall)
    (fun eps => exponentialDelta (inputError B hB eps)) (fun _ => ⟨1,by decide +kernel⟩) hfrem hgrem

theorem exponential_value (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (hsmall : SmallOperator E) :
    (MatrixExponential.value (value E hsmall) (value_linear E hE hsmall) unit).Equiv (identityPlus E unit) :=
  exponential_identityPlus E hE hsmall unit unit_mem

end ComputableAnalysis.RiemannHilbert.MatrixLogarithm
