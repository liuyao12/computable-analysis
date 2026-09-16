import ComputableAnalysis.CartwrightTheorem

/-!
# A second analytic route: discrete integration by parts

This route uses the exact finite product-sum identity and bounds its three
terms separately. It never calls the general FTC, its product certificate,
or the FTC-derived integration-by-parts lemmas.
-/
namespace ComputableAnalysis.CartwrightDirect
open CartwrightClockBounds CartwrightMoments CartwrightFiniteSums FiniteRiemannAlgebra
open RationalErrorCalculus CartwrightIntegrationByParts UniformGridFTC

private theorem stieltjes_as_sum (f g : Nat → Rat) (N : Nat) :
    leftStieltjesSum f g N=sum (fun j=>f j*(g (j+1)-g j)) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [leftStieltjesSum,sum_succ,ih]

private theorem variation_as_sum (f g : Nat → Rat) (N : Nat) :
    quadraticVariationSum f g N=sum (fun j=>(f (j+1)-f j)*(g (j+1)-g j)) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [quadraticVariationSum,sum_succ,ih]

private theorem bounded_mul {a b A B : Rat} (ha : qabs a≤A) (hb : qabs b≤B) (hA : 0≤A) :
    qabs (a*b)≤A*B := by
  rw [qabs_mul]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ha (qabs_nonneg b))
    (Rat.mul_le_mul_of_nonneg_left hb hA)

/-- Control the three contributions in the exact discrete product identity. -/
private theorem cell_estimates {f df : Rat → Rat} {g dg : Family}
    (F : FiniteFirstOrderCalculus.Data f df) (G : CircleData g dg)
    (k j : Nat) (hj : j<cells k) :
    let a:=grid k j
    let b:=grid k (j+1)
    let q:=sampleStage k
    let h:=step k
    let E:=h*h+delta q
    qabs (f a*(g q b-g q a)-h*(f a*dg q a))≤20000*F.size*E ∧
    qabs (g q a*(f b-f a)-h*(df a*g q a))≤F.remainder*E ∧
    qabs ((f b-f a)*(g q b-g q a))≤80*(F.slope+F.remainder)*E := by
  have ha:=grid_unit k j (by omega);have hb:=grid_unit k (j+1) (by omega)
  have hstep:=grid_step k j
  have hpos:=step_pos k
  have hab : grid k j≤grid k (j+1) := by grind
  have hh1 : step k≤1 := by rw [step_eq];exact delta_le_one k
  have hdelta:=Rat.le_of_lt (ClosedArctanInverse.meshRadius_pos (sampleStage k))
  have hF:=F.value_bound _ ha
  have hG:=G.bounded (sampleStage k) _ ha
  have erG:=G.residual (sampleStage k) _ _ ha hb hab
  have erF:=F.error _ _ ha hb hab
  have incF:=FiniteFirstOrderCalculus.lipschitz F ha hb hab
  have incG:=G.increment (sampleStage k) _ _ ha hb hab
  rw [hstep] at erG erF incF incG
  dsimp only
  constructor
  · rw [show f (grid k j)*(g (sampleStage k) (grid k (j+1))-g (sampleStage k) (grid k j))-
      step k*(f (grid k j)*dg (sampleStage k) (grid k j))=
      f (grid k j)*(g (sampleStage k) (grid k (j+1))-g (sampleStage k) (grid k j)-step k*dg (sampleStage k) (grid k j)) by grind]
    have h:=bounded_mul hF erG F.size_nonnegative
    grind
  constructor
  · rw [show g (sampleStage k) (grid k j)*(f (grid k (j+1))-f (grid k j))-
      step k*(df (grid k j)*g (sampleStage k) (grid k j))=
      g (sampleStage k) (grid k j)*(f (grid k (j+1))-f (grid k j)-step k*df (grid k j)) by grind]
    have h:=bounded_mul hG erF (by decide +kernel)
    have hpad:=Rat.mul_nonneg F.remainder_nonnegative hdelta
    grind
  · have hL:=Rat.add_nonneg F.slope_nonnegative F.remainder_nonnegative
    have h:=bounded_mul incF incG (Rat.mul_nonneg hL (Rat.le_of_lt hpos))
    have hsmall:=Rat.mul_le_mul_of_nonneg_right hh1 hdelta
    have hmul:=Rat.mul_le_mul_of_nonneg_left hsmall (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤80) hL)
    grind

/-- A finite identity and three error sums, rather than an application of FTC. -/
theorem discrete_parts {f df : Rat → Rat} {g dg : Family}
    (F : FiniteFirstOrderCalculus.Data f df) (G : CircleData g dg) :
    Near (riemann (fun q t=>df t*g q t+f t*dg q t)) (endpoint (fun q t=>f t*g q t)) := by
  let K : Rat:=20000*F.size+F.remainder+80*(F.slope+F.remainder)
  have hK : 0≤K := by
    have hs:=F.size_nonnegative;have hd:=F.slope_nonnegative;have he:=F.remainder_nonnegative
    dsimp [K];grind
  apply Near.symm
  apply Near.geometric (2*K) (Rat.mul_nonneg (by decide +kernel) hK)
  intro k
  let f' : Nat→Rat:=fun j=>f (grid k j)
  let g' : Nat→Rat:=fun j=>g (sampleStage k) (grid k j)
  let A : Nat→Rat:=fun j=>f' j*(g' (j+1)-g' j)-step k*(f' j*dg (sampleStage k) (grid k j))
  let B : Nat→Rat:=fun j=>g' j*(f' (j+1)-f' j)-step k*(df (grid k j)*g' j)
  let V : Nat→Rat:=fun j=>(f' (j+1)-f' j)*(g' (j+1)-g' j)
  have hA:=sum_bound (N:=cells k) (f:=A) (fun j hj=>(cell_estimates F G k j hj).1)
  have hB:=sum_bound (N:=cells k) (f:=B) (fun j hj=>(cell_estimates F G k j hj).2.1)
  have hV:=sum_bound (N:=cells k) (f:=V) (fun j hj=>(cell_estimates F G k j hj).2.2)
  have hsum:=qabs_add_le (sum A (cells k)+sum B (cells k)) (sum V (cells k))
  have hab:=qabs_add_le (sum A (cells k)) (sum B (cells k))
  have identity:=finiteIntegrationByParts_withVariation f' g' (cells k)
  rw [stieltjes_as_sum,stieltjes_as_sum,variation_as_sum] at identity
  have he : endpoint (fun q t=>f t*g q t) k-riemann (fun q t=>df t*g q t+f t*dg q t) k=
      sum A (cells k)+sum B (cells k)+sum V (cells k) := by
    have hpoint : (fun j=>step k*(df (grid k j)*g' j+f' j*dg (sampleStage k) (grid k j)))=
        (fun j=>step k*(f' j*dg (sampleStage k) (grid k j))+step k*(df (grid k j)*g' j)) := by funext j;grind
    unfold A B
    rw [sum_sub,sum_sub]
    change _ = _
    unfold riemann endpoint
    change f 1*g (sampleStage k) 1-f 0*g (sampleStage k) 0-
        sum (fun j=>step k*(df (grid k j)*g' j+f' j*dg (sampleStage k) (grid k j))) (cells k)=_
    rw [hpoint,sum_add]
    have hfirst : f' (cells k)*g' (cells k)-f' 0*g' 0=f 1*g (sampleStage k) 1-f 0*g (sampleStage k) 0 := by
      dsimp [f',g'];rw [grid_last,grid_zero]
    rw [hfirst] at identity
    dsimp [V]
    grind
  rw [he]
  have hstage:=Rat.mul_le_mul_of_nonneg_left (stage_error k) hK
  dsimp [K] at hstage
  grind

theorem sine_parts {f df : Rat → Rat} (F : FiniteFirstOrderCalculus.Data f df) :
    Near (fun k=>frequencySample k*cosineSum f k+sineSum df k) (fun _=>f 1) := by
  have h:=discrete_parts F sine_data
  have he : riemann (fun q t=>df t*UniformGridFTC.sine q t+f t*UniformGridFTC.sineDerivative q t)=
      (fun k=>frequencySample k*cosineSum f k+sineSum df k) := by
    funext k
    unfold riemann UniformGridFTC.sine UniformGridFTC.sineDerivative frequencySample cosineSum sineSum
    unfold riemann
    rw [←sum_mul,←sum_add]
    apply sum_congr;intro j hj;grind
  rw [he] at h
  exact Near.trans h (sine_boundary f)

theorem cosine_parts {f df : Rat → Rat} (F : FiniteFirstOrderCalculus.Data f df) :
    Near (fun k=>cosineSum df k-frequencySample k*sineSum f k) (fun _=> -(f 0)) := by
  have h:=discrete_parts F cosine_data
  have he : riemann (fun q t=>df t*UniformGridFTC.cosine q t+f t*UniformGridFTC.cosineDerivative q t)=
      (fun k=>cosineSum df k-frequencySample k*sineSum f k) := by
    funext k
    unfold riemann UniformGridFTC.cosine UniformGridFTC.cosineDerivative frequencySample cosineSum sineSum
    unfold riemann
    rw [←sum_mul,←sum_sub]
    apply sum_congr;intro j hj;grind
  rw [he] at h
  exact Near.trans h (cosine_boundary f)

/-- The direct route supplies the same moment laws, without invoking FTC. -/
theorem laws : CartwrightMomentRecurrence.Laws :=
  CartwrightMomentRecurrence.laws_of_parts (fun _ _ D=>sine_parts D) (fun _ _ D=>cosine_parts D)

theorem moment_viaInequalities (n : Nat) : CartwrightTheorem.MomentStatement n := CartwrightTheorem.moment_of_laws laws n

theorem pi_squared_viaInequalities : CartwrightTheorem.PiSquaredStatement := CartwrightTheorem.pi_squared_of_laws laws

end ComputableAnalysis.CartwrightDirect
