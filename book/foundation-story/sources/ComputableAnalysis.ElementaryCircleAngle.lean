import ComputableAnalysis.ModularForms.GeometricQuarterTurn

/-! The geometric angle of a rational circle chart, justified by finite Euler
meshes and finite rectangle sums. No inverse identity is assumed as data. -/
namespace ComputableAnalysis.ElementaryCircleAngle
open ComplexRaw RiemannHilbert FunctionTheory ArctanGeometry ModularForms
open GeometricRotationODE SeriesLimitLaws
set_option maxHeartbeats 1000000

structure UnitSlope where
  val : Rat
  nonnegative : 0 ≤ val
  le_one : val ≤ 1

def step (t : UnitSlope) (N : Nat) : Rat := t.val*geometricMeshStep N

theorem step_bounds (t : UnitSlope) (N : Nat) : 0 ≤ step t N ∧ step t N ≤ geometricMeshStep N := by
  have hh := Rat.le_of_lt (geometricMeshStep_positive N)
  exact ⟨Rat.mul_nonneg t.nonnegative hh,by
    have h := Rat.mul_le_mul_of_nonneg_right t.le_one hh
    simpa only [step,Rat.one_mul] using h⟩
theorem step_identity (t : UnitSlope) (N : Nat) : ((N+1:Nat):Rat)*step t N=t.val := by
  unfold step
  have h := geometricMeshStep_identity N
  grind only

theorem meshStep_le_one (N : Nat) : geometricMeshStep N ≤ 1 := by
  have hc := geometricMeshStep_identity N
  have hn : (1:Rat) ≤ ((N+1:Nat):Rat) := by exact_mod_cast Nat.succ_pos N
  have hm := Rat.mul_le_mul_of_nonneg_right hn (Rat.le_of_lt (geometricMeshStep_positive N))
  grind only

theorem time_bounds (t : UnitSlope) (N k : Nat) (hk : k ≤ N+1) :
    0 ≤ (k:Rat)*step t N ∧ (k:Rat)*step t N ≤ 1 := by
  have hc : (k:Rat) ≤ ((N+1:Nat):Rat) := by exact_mod_cast hk
  have hm := Rat.mul_le_mul_of_nonneg_right hc (step_bounds t N).1
  rw [step_identity] at hm
  exact ⟨Rat.mul_nonneg (by exact_mod_cast Nat.zero_le k) (step_bounds t N).1,
    Rat.le_trans hm t.le_one⟩

def mesh (t : UnitSlope) (N : Nat) : Nat → QComplex
  | 0 => QComplex.one
  | k+1 => geometricRotationEulerAt ((k:Rat)*step t N) (step t N) (mesh t N k)

theorem mesh_error (t : UnitSlope) (N k : Nat) (hk : k ≤ N+1) :
    qabs ((mesh t N k).re-(pointComplex ((k:Rat)*step t N)).re) ≤ geometricEulerMeshError N k ∧
    qabs ((mesh t N k).im-(pointComplex ((k:Rat)*step t N)).im) ≤ geometricEulerMeshError N k := by
  induction k with
  | zero =>
    change qabs (QComplex.one.re-(pointComplex ((0:Rat)*step t N)).re)≤0 ∧
      qabs (QComplex.one.im-(pointComplex ((0:Rat)*step t N)).im)≤0
    rw [Rat.zero_mul,pointComplex_zero]
    constructor <;> rw [Rat.sub_self] <;> decide +kernel
  | succ k ih =>
    have hp := ih (by omega)
    have ht := time_bounds t N k (by omega)
    have hn := time_bounds t N (k+1) hk
    have he : ((k+1:Nat):Rat)*step t N=(k:Rat)*step t N+step t N := by
      rw [Rat.natCast_add]; grind
    rw [he] at hn
    have hb := geometricRotationEulerAt_error_step ((k:Rat)*step t N) (step t N)
      (mesh t N k) (geometricEulerMeshError N k) ht.1 ht.2 hn.1 hn.2
      (geometricEulerMeshError_nonnegative N k) hp.1 hp.2
    rw [qabs_eq_self_of_nonneg (step_bounds t N).1] at hb
    have hs := step_bounds t N
    have hE := geometricEulerMeshError_nonnegative N k
    have hm := rat_mul_le_mul_of_nonneg hs.1 hs.2 hs.1 hs.2
    change qabs ((geometricRotationEulerAt ((k:Rat)*step t N) (step t N)
      (mesh t N k)).re-(pointComplex (((k+1:Nat):Rat)*step t N)).re)≤_ ∧
      qabs ((geometricRotationEulerAt ((k:Rat)*step t N) (step t N)
      (mesh t N k)).im-(pointComplex (((k+1:Nat):Rat)*step t N)).im)≤_
    rw [he]
    simp only [geometricEulerMeshError]
    have ha := Rat.mul_le_mul_of_nonneg_right hs.2 hE
    constructor <;> grind only

def angle (t : UnitSlope) (N : Nat) : Nat → Rat
  | 0 => 0
  | k+1 => step t N*(2/(1+((k:Rat)*step t N)*((k:Rat)*step t N)))+angle t N k

def angleScalar (t : UnitSlope) (N k : Nat) : Scalar :=
  ⟨ofQComplex ⟨0,angle t N k⟩,ofQComplex_valid _⟩

def product (t : UnitSlope) (N : Nat) : Nat → ComplexRaw
  | 0 => ofQComplex QComplex.one
  | k+1 => mul (entireExponentialValue
      (geometricAngularIncrement ((k:Rat)*step t N) (step t N))).val (product t N k)

theorem product_valid (t : UnitSlope) (N k : Nat) : (product t N k).Valid := by
  induction k with
  | zero => exact ofQComplex_valid _
  | succ k ih => exact mul_valid (entireExponentialValue _).property ih

theorem angleScalar_succ (t : UnitSlope) (N k : Nat) :
    (add (geometricAngularIncrement ((k:Rat)*step t N) (step t N)).val
      (angleScalar t N k).val).Equiv (angleScalar t N (k+1)).val := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  simp only [geometricAngularIncrement,angleScalar,angle,add,ofQComplex,
    QBox.add,QBox.point,QComplex.add,QBox.Overlaps,QComplex.le_def]
  constructor <;> constructor <;> grind

theorem product_angle (t : UnitSlope) (N k : Nat) :
    (product t N k).Equiv (entireExponentialValue (angleScalar t N k)).val := by
  induction k with
  | zero => exact equiv_symm entireExponential_zero
  | succ k ih =>
    let x := geometricAngularIncrement ((k:Rat)*step t N) (step t N)
    let a := angleScalar t N k
    let b : Scalar := ⟨add x.val a.val,add_valid x.property a.property⟩
    have hm := mul_equiv (entireExponentialValue x).property (entireExponentialValue x).property
      (product_valid t N k) (entireExponentialValue a).property
      (equiv_refl _ (entireExponentialValue x).property) ih
    exact equiv_trans (product_valid t N (k+1))
      (mul_valid (entireExponentialValue x).property (entireExponentialValue a).property)
      (entireExponentialValue (angleScalar t N (k+1))).property hm
      (equiv_trans (mul_valid (entireExponentialValue x).property (entireExponentialValue a).property)
        (entireExponentialValue b).property (entireExponentialValue (angleScalar t N (k+1))).property
        (entireExponential_addition x a)
        (entireExponentialValue_congr b (angleScalar t N (k+1)) (angleScalar_succ t N k)))

theorem angle_bounds (t : UnitSlope) (N k : Nat) :
    0 ≤ angle t N k ∧ angle t N k ≤ 2*(k:Rat)*step t N := by
  induction k with
  | zero => simp [angle]
  | succ k ih =>
    have hh := (step_bounds t N).1
    have hn := geometricRotationSpeed_nonnegative ((k:Rat)*step t N)
    have hu := Rat.le_trans (self_le_qabs (2/(1+((k:Rat)*step t N)*((k:Rat)*step t N))))
      (geometricRotationSpeed_bound ((k:Rat)*step t N))
    have hpn := Rat.mul_nonneg hh hn
    have hpu := Rat.mul_le_mul_of_nonneg_left hu hh
    simp only [angle,Rat.natCast_add]
    have hone : ((1:Nat):Rat)=1 := by decide
    rw [hone]
    constructor <;> grind only

theorem angle_small (t : UnitSlope) (N k : Nat) (hk : k ≤ N+1) :
    Small (angleScalar t N k).val 2 := by
  obtain ⟨hl,hb⟩ := angle_bounds t N k
  have ht := time_bounds t N k hk
  refine ⟨?_,?_,?_,?_⟩
  · intro n m; change (-2:Rat) ≤ 0; decide
  · intro n m; change (0:Rat) ≤ 2; decide
  · intro n m; change -2 ≤ angle t N k; grind only
  · intro n m; change angle t N k ≤ 2; grind only

theorem product_small (t : UnitSlope) (N k : Nat) (hk : k ≤ N+1) :
    Small (product t N k) geometricExponentialPrefixBound := by
  let z := angleScalar t N k
  let e := (entireExponentialValue z).val
  let l := add (ofQComplex QComplex.one) z.val
  have hz := angle_small t N k hk
  have hchart : (exponentialChart geometricFactorRadius).domain z :=
    ⟨2,by decide,by decide,hz⟩
  have hr := entireExponential_linear_error geometricFactorRadius z hchart 2 (by decide) hz
  have hone : Small (ofQComplex QComplex.one) 1 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro n m; change (-1:Rat) ≤ 1; decide
    · intro n m; change (1:Rat) ≤ 1; decide
    · intro n m; change (-1:Rat) ≤ 0; decide
    · intro n m; change (0:Rat) ≤ 1; decide
  have hl : Small l 3 := by
    have hb := LocalODE.small_add hone hz
    have hc : (1:Rat)+2=3 := by decide +kernel
    rw [hc] at hb
    exact hb
  have he : (add (sub e l) l).Equiv e := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid (entireExponentialValue z).property
        (add_valid (ofQComplex_valid _) z.property)) (add_valid (ofQComplex_valid _) z.property))
      (hright := (entireExponentialValue z).property)
    change (ComplexRawQuotient.ofRaw e (entireExponentialValue z).property +
      -ComplexRawQuotient.ofRaw l (add_valid (ofQComplex_valid _) z.property)) +
      ComplexRawQuotient.ofRaw l (add_valid (ofQComplex_valid _) z.property) =
      ComplexRawQuotient.ofRaw e (entireExponentialValue z).property
    grind only
  have hb := LocalODE.small_add hr hl
  have hval := Small.congr
    (add_valid (sub_valid (entireExponentialValue z).property (add_valid (ofQComplex_valid _) z.property))
      (add_valid (ofQComplex_valid _) z.property)) (entireExponentialValue z).property he hb
  have hconst : exponentialQuadraticConstant geometricFactorRadius*(2:Rat)^2+3=
      geometricExponentialPrefixBound := by
    unfold geometricExponentialPrefixBound
    simp only [Rat.pow_succ,Rat.pow_zero]
    grind only
  rw [hconst] at hval
  exact Small.congr (entireExponentialValue z).property (product_valid t N k)
    (equiv_symm (product_angle t N k)) hval

def cells (t : UnitSlope) (N : Nat) : Nat → List (Rat × Rat)
  | 0 => []
  | k+1 => cells t N k ++
      [((k:Rat)*step t N,((k+1:Nat):Rat)*step t N)]

theorem cells_covers (t : UnitSlope) (N k : Nat) :
    CoversInterval 0 ((k:Rat)*step t N) (cells t N k) := by
  induction k with
  | zero => simp [cells,CoversInterval]
  | succ k ih =>
    apply CoversInterval.append ih
    have hh := (step_bounds t N).1
    have hc : (k:Rat) ≤ ((k+1:Nat):Rat) := by exact_mod_cast Nat.le_succ k
    exact ⟨rfl,Rat.mul_le_mul_of_nonneg_right hc hh,rfl⟩

theorem cells_endpoint_covers (t : UnitSlope) (N : Nat) :
    CoversInterval 0 t.val (cells t N (N+1)) := by
  have h := cells_covers t N (N+1)
  rw [step_identity] at h
  exact h

theorem angle_eq_upper_rectangles (t : UnitSlope) (N k : Nat) :
    angle t N k = 2*integralUpperSum (cells t N k) := by
  induction k with
  | zero => simp [angle,cells,integralUpperSum]
  | succ k ih =>
    simp only [angle,cells,integralUpperSum_append,
      integralUpperSum,integralUpperStep,integralKernel]
    rw [ih]
    have hc : ((k+1:Nat):Rat)=(k:Rat)+1 := by
      rw [Rat.natCast_add]
      have h1 : ((1:Nat):Rat)=1 := by decide +kernel
      rw [h1]
    rw [hc]
    simp only [Rat.div_def]
    grind only

theorem cells_squareSum (t : UnitSlope) (N k : Nat) :
    intervalSquareSum (cells t N k) =
      (k:Rat)*step t N*step t N := by
  induction k with
  | zero => simp [cells,intervalSquareSum]
  | succ k ih =>
    have happ (xs ys : List (Rat × Rat)) :
        intervalSquareSum (xs++ys)=intervalSquareSum xs+intervalSquareSum ys := by
      induction xs with
      | nil => simp [intervalSquareSum]; grind only
      | cons p ps hps => simp only [List.cons_append,intervalSquareSum,hps]; grind only
    rw [cells,happ,ih]
    simp only [intervalSquareSum,Rat.natCast_add]
    have h1 : ((1:Nat):Rat)=1 := by decide +kernel
    rw [h1]
    grind only

theorem rectangles_endpoint_width (t : UnitSlope) (N : Nat) :
    (integralSumInterval (cells t N (N+1))).width ≤ 2*geometricMeshStep N := by
  have hc := cells_endpoint_covers t N
  have hb := integralSumInterval_width_le_two_squareSum _
    (CoversInterval.unit (by decide) t.le_one hc)
  rw [cells_squareSum] at hb
  rw [step_identity] at hb
  have hs := step_bounds t N
  have hm := Rat.mul_le_mul_of_nonneg_right t.le_one hs.1
  grind only

theorem rectangles_sector_overlap (t : UnitSlope) (N n : Nat) :
    QInterval.Overlaps (integralSumInterval (cells t N (N+1)))
      (positiveLoopComputeAtStage t.val n) := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval t.nonnegative n]
  exact integralSumInterval_overlaps_geometricSumInterval_of_covers (by decide) _ _
    (cells_endpoint_covers t N)
    (arctanAreaLoopState_intervals_covers t.nonnegative n)


def twiceArctangent (t : UnitSlope) : RealRaw := RealRaw.scaleRat 2 (arctanGeom t.val)
theorem twiceArctangent_valid (t : UnitSlope) : (twiceArctangent t).Valid :=
  RealRaw.scaleRat_valid (arctanGeom_valid_on_unit t.nonnegative t.le_one)
def imaginaryAngle (t : UnitSlope) : Scalar :=
  ⟨imaginaryAxis (twiceArctangent t),
    imaginaryAxis_valid (twiceArctangent_valid t)⟩

theorem twiceArctangent_compute (t : UnitSlope) (n : Nat) :
    (twiceArctangent t).compute n =
      {lo := 2*(positiveLoopComputeAtStage t.val n).lo,
       hi := 2*(positiveLoopComputeAtStage t.val n).hi} := by
  have he : (arctanGeom t.val).compute n = positiveLoopComputeAtStage t.val n := by
    by_cases hz : t.val = 0
    · rw [hz,positiveLoopComputeAtStage_zero]; rfl
    · exact arctanGeom_nonneg_compute_eq hz t.nonnegative n
  simp [twiceArctangent,RealRaw.scaleRat,RealRaw.scaleRatCompute,he,
    show (0:Rat)≤2 by decide]

theorem angle_target_error (t : UnitSlope) (N : Nat) :
    Small (sub (angleScalar t N (N+1)).val (imaginaryAngle t).val)
      (4*geometricMeshStep N) := by
  have hh := Rat.le_of_lt (geometricMeshStep_positive N)
  have hw := rectangles_endpoint_width t N
  have ha := angle_eq_upper_rectangles t N (N+1)
  have hov (n : Nat) := rectangles_sector_overlap t N n
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m <;>
    simp only [sub,add,neg,angleScalar,imaginaryAngle,
      imaginaryAxis,ofQComplex,QBox.add,QBox.neg,QBox.point,QComplex.add,QComplex.neg,
      realPart,imagPart,RealRaw.ofRat,Rat.neg_zero,Rat.add_zero,Rat.zero_add]
  · change -(4*geometricMeshStep N) ≤ 0; grind only
  · change (0:Rat) ≤ 4*geometricMeshStep N
    exact Rat.mul_nonneg (by decide) hh
  · change -(4*geometricMeshStep N) ≤ angle t N (N+1)+ -((twiceArctangent t).compute m).lo
    rw [twiceArctangent_compute,ha]
    have ho := (hov m).2
    change (positiveLoopComputeAtStage t.val m).lo ≤ integralUpperSum (cells t N (N+1)) at ho
    grind only
  · change angle t N (N+1)+ -((twiceArctangent t).compute n).hi ≤ 4*geometricMeshStep N
    rw [twiceArctangent_compute,ha]
    have ho := (hov n).1
    change integralLowerSum (cells t N (N+1)) ≤ (positiveLoopComputeAtStage t.val n).hi at ho
    change integralUpperSum (cells t N (N+1))-integralLowerSum (cells t N (N+1)) ≤ 2*geometricMeshStep N at hw
    grind only

theorem imaginaryAngle_small (t : UnitSlope) : Small (imaginaryAngle t).val 2 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m; change (-2:Rat) ≤ 0; decide
  · intro n m; change (0:Rat) ≤ 2; decide
  · intro n m; change (-2:Rat) ≤ ((twiceArctangent t).compute m).hi
    rw [twiceArctangent_compute]
    have hn := arctanIntegralRectangleCompute_lower_nonnegative t.nonnegative m
    have hov := arctanAreaLoop_integralSum_overlaps_positiveLoop t.nonnegative m
    change (arctanIntegralRectangleCompute t.val m).lo ≤ (positiveLoopComputeAtStage t.val m).hi ∧
      (positiveLoopComputeAtStage t.val m).lo ≤ (arctanIntegralRectangleCompute t.val m).hi at hov
    grind only
  · intro n m; change ((twiceArctangent t).compute n).lo ≤ (2:Rat)
    rw [twiceArctangent_compute]
    have hb := arctanIntegralRectangleCompute_upper_le_input t.nonnegative n
    have hov := arctanAreaLoop_integralSum_overlaps_positiveLoop t.nonnegative n
    change (arctanIntegralRectangleCompute t.val n).lo ≤ (positiveLoopComputeAtStage t.val n).hi ∧
      (positiveLoopComputeAtStage t.val n).lo ≤ (arctanIntegralRectangleCompute t.val n).hi at hov
    have ht := t.le_one
    grind only


theorem angle_exponential_target_error (t : UnitSlope) (N : Nat) :
    Small (sub (entireExponentialValue (angleScalar t N (N+1))).val
      (entireExponentialValue (imaginaryAngle t)).val)
      (4*exponentialQuadraticConstant geometricFactorRadius*geometricMeshStep N) := by
  have hb := entireExponential_lipschitz geometricFactorRadius
    (imaginaryAngle t) (angleScalar t N (N+1))
    ⟨2,by decide,by decide,imaginaryAngle_small t⟩
    ⟨2,by decide,by decide,angle_small t N (N+1) (Nat.le_refl _)⟩
    (4*geometricMeshStep N)
    (Rat.mul_nonneg (by decide) (Rat.le_of_lt (geometricMeshStep_positive N)))
    (angle_target_error t N)
  have he : 16*exponentialBudget (exponentialRatio geometricFactorRadius)*
      (exponentialRatio geometricFactorRadius)^2*(4*geometricMeshStep N)=
      4*exponentialQuadraticConstant geometricFactorRadius*geometricMeshStep N := by
    unfold exponentialQuadraticConstant
    grind only
  rw [he] at hb
  exact hb

theorem mesh_factor (t : UnitSlope) (N k : Nat) :
    (mul (geometricEulerFactor ((k:Rat)*step t N) (step t N)).val
      (ofQComplex (mesh t N k))).Equiv (ofQComplex (mesh t N (k+1))) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  change (QBox.mul (QBox.point ⟨1,step t N*
    (2/(1+((k:Rat)*step t N)*((k:Rat)*step t N)))⟩)
    (QBox.point (mesh t N k))).Overlaps (QBox.point (mesh t N (k+1)))
  rw [QBox.mul_point,geometricEulerFactor_step]
  exact ⟨⟨Rat.le_refl,Rat.le_refl⟩,⟨Rat.le_refl,Rat.le_refl⟩⟩
theorem product_mesh_error (t : UnitSlope) (N k : Nat) (hk : k ≤ N+1) :
    Small (sub (product t N k) (ofQComplex (mesh t N k)))
      (geometricExponentialErrorScale*geometricEulerMeshError N k) := by
  induction k with
  | zero =>
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m <;>
      simp [product,mesh,geometricEulerMeshError,
        sub,add,neg,ofQComplex,QBox.add,QBox.neg,QBox.point,QComplex.add,QComplex.neg,QComplex.one,
        realPart,imagPart,RealRaw.ofRat] <;> grind only
  | succ k ih =>
    have hkn : k ≤ N+1 := by omega
    have hE := Rat.mul_nonneg geometricExponentialErrorScale_nonnegative
      (geometricEulerMeshError_nonnegative N k)
    have hb := geometricExponentialProduct_error_step ((k:Rat)*step t N)
      (step t N) (geometricExponentialErrorScale*geometricEulerMeshError N k)
      geometricExponentialPrefixBound (product t N k)
      (ofQComplex (mesh t N k)) (product_valid t N k)
      (ofQComplex_valid _) ((step_bounds t N).1) (Rat.le_trans (step_bounds t N).2 (meshStep_le_one N))
      hE geometricExponentialPrefixBound_nonnegative (ih hkn)
      (product_small t N k hkn)
    have he := FunctionTheory.sub_congr
      (equiv_refl _ (product_valid t N (k+1))) (mesh_factor t N k)
    have hv := Small.congr
      (sub_valid (product_valid t N (k+1))
        (mul_valid (geometricEulerFactor _ _).property (ofQComplex_valid _)))
      (sub_valid (product_valid t N (k+1)) (ofQComplex_valid _)) he hb
    apply hv.mono
    have hh := (step_bounds t N).1
    have hstep := step_bounds t N
    have hmul := rat_mul_le_mul_of_nonneg hstep.1 hstep.2 hstep.1 hstep.2
    have hEbound := Rat.mul_le_mul_of_nonneg_right hstep.2 hE
    have htail := Rat.mul_le_mul_of_nonneg_left hmul geometricExponentialErrorScale_nonnegative
    have htail_nonneg := Rat.mul_nonneg geometricExponentialErrorScale_nonnegative
      (Rat.mul_nonneg (Rat.le_of_lt (geometricMeshStep_positive N))
        (Rat.le_of_lt (geometricMeshStep_positive N)))
    have hs := Rat.mul_nonneg (Rat.mul_nonneg geometricExponentialErrorScale_nonnegative hh) hh
    simp only [geometricEulerMeshError]
    unfold geometricExponentialErrorScale at *
    grind only

theorem meshError_rate (N : Nat) :
    geometricEulerMeshError (geometricConvergenceMesh N) (geometricConvergenceMesh N+1) ≤
      geometricEulerEndpointRate N := by
  have ha := geometricEulerMesh_amplification_bound N
  have hh := Rat.le_of_lt (geometricMeshStep_positive (geometricConvergenceMesh N))
  have hm := Rat.mul_le_mul_of_nonneg_left
    (show (1+2*geometricMeshStep (geometricConvergenceMesh N))^(geometricConvergenceMesh N+1)-1 ≤ 15 by
      grind only) (Rat.mul_nonneg (show (0:Rat)≤6 by decide) hh)
  rw [geometricEulerMeshError_closed]
  unfold geometricEulerEndpointRate
  grind only

theorem product_endpoint_error (t : UnitSlope) (N : Nat) :
    Small (sub (product t (geometricConvergenceMesh N) (geometricConvergenceMesh N+1))
      (ofQComplex (mesh t (geometricConvergenceMesh N) (geometricConvergenceMesh N+1))))
      (geometricExponentialEndpointRate N) :=
  (product_mesh_error t _ _ (Nat.le_refl _)).mono
    (Rat.mul_le_mul_of_nonneg_left (meshError_rate N) geometricExponentialErrorScale_nonnegative)

theorem mesh_endpoint_small (t : UnitSlope) (N : Nat) :
    Small (sub (ofQComplex (mesh t (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)))
      (ofQComplex (pointComplex t.val))) (geometricEulerEndpointRate N) := by
  obtain ⟨hr,hi⟩ := mesh_error t (geometricConvergenceMesh N) (geometricConvergenceMesh N+1) (Nat.le_refl _)
  rw [step_identity] at hr hi
  have hb := meshError_rate N
  have lr := neg_qabs_le_self ((mesh t (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).re-(pointComplex t.val).re)
  have ur := self_le_qabs ((mesh t (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).re-(pointComplex t.val).re)
  have li := neg_qabs_le_self ((mesh t (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).im-(pointComplex t.val).im)
  have ui := self_le_qabs ((mesh t (geometricConvergenceMesh N) (geometricConvergenceMesh N+1)).im-(pointComplex t.val).im)
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m <;>
    simp only [sub,add,neg,ofQComplex,QBox.add,QBox.neg,QBox.point,QComplex.add,QComplex.neg,
      realPart,imagPart,RealRaw.ofRat] <;> grind only
theorem exponential_twiceArctangent (t : UnitSlope) :
    (entireExponentialValue (imaginaryAngle t)).val.Equiv
      (ofQComplex (pointComplex t.val)) := by
  let f := (entireExponentialValue
    (imaginaryAngle t)).val
  let c := exponentialQuadraticConstant geometricFactorRadius
  let s := c+geometricExponentialErrorScale+1
  have hc : 0 ≤ c := exponentialQuadraticConstant_nonnegative _
  have hs : 0 ≤ s := Rat.add_nonneg (Rat.add_nonneg hc geometricExponentialErrorScale_nonnegative) (by decide)
  have hrate := shrinks_scale geometricEulerEndpointRate geometricEulerEndpointRate_shrinks s hs
  apply equiv_of_small_sub_zero
  apply small_closed (sub f (ofQComplex (pointComplex t.val))) 0
    (fun N => s*geometricEulerEndpointRate N) hrate
  intro N
  let j := geometricConvergenceMesh N
  let p := product t j (j+1)
  let q := ofQComplex (mesh t j (j+1))
  have hp := product_valid t j (j+1)
  have hq := ofQComplex_valid (mesh t j (j+1))
  have hangle := angle_exponential_target_error t j
  have hfp := Small.congr
    (sub_valid (entireExponentialValue (angleScalar t j (j+1))).property (entireExponentialValue _).property)
    (sub_valid hp (entireExponentialValue _).property)
    (FunctionTheory.sub_congr (equiv_symm (product_angle t j (j+1)))
      (equiv_refl _ (entireExponentialValue _).property)) hangle
  have hpf := small_neg hfp
  have hsym : (neg (sub p f)).Equiv (sub f p) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid hp (entireExponentialValue _).property))
      (hright := sub_valid (entireExponentialValue _).property hp)
    change -(ComplexRawQuotient.ofRaw p hp + -ComplexRawQuotient.ofRaw f (entireExponentialValue _).property) =
      ComplexRawQuotient.ofRaw f (entireExponentialValue _).property + -ComplexRawQuotient.ofRaw p hp
    grind only
  have hfirst := Small.congr (neg_valid (sub_valid hp (entireExponentialValue _).property))
    (sub_valid (entireExponentialValue _).property hp) hsym hpf
  have hb := LocalODE.small_add (LocalODE.small_add hfirst (product_endpoint_error t N))
    (mesh_endpoint_small t N)
  have hid := difference_via f (ofQComplex (pointComplex t.val)) p q
    (entireExponentialValue _).property (ofQComplex_valid _) hp hq
  have hfinal := Small.congr
    (add_valid (add_valid (sub_valid (entireExponentialValue _).property hp) (sub_valid hp hq))
      (sub_valid hq (ofQComplex_valid _)))
    (sub_valid (entireExponentialValue _).property (ofQComplex_valid _)) (equiv_symm hid) hb
  apply hfinal.mono
  have hh := Rat.le_of_lt (geometricMeshStep_positive j)
  have hm := Rat.mul_nonneg hc hh
  unfold geometricExponentialEndpointRate geometricEulerEndpointRate
  dsimp [s,c,j] at *
  grind only

end ComputableAnalysis.ElementaryCircleAngle
