import ComputableAnalysis.ClosedCosineIntegral
import ComputableAnalysis.PositiveIntervalInverse

/-!
# A pi-free cosine quadrature on the first-quadrant chart

Every numerical cosine sample is a nested-radical rotation. Fixed meshes are
retained while their sample precision increases. The error allowance is
explicit and contains no numerical pi. The closed arctangent integral
theorem is used only to prove the result, not by the quadrature program.
-/
namespace ComputableAnalysis
namespace DyadicCosineIntegral
open ClosedArctanInverse SinPiIntegral IntervalSelections

private theorem le_of_slack {a b : Rat} (h : ∀ eps : QPos, a <=b+eps.val) : a <=b := by
  by_cases hab : a <=b
  · exact hab
  · let eps : QPos:=⟨(a-b)/2,by rw [Rat.div_def]; exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide))⟩
    have hh:=h eps
    dsimp [eps] at hh
    simp only [Rat.div_def] at hh
    grind

def fixedMesh (d : Nat) : RealRaw :=
  Integral.finiteRawSum ((List.range (2^d)).map (fun j=>
    RealRaw.scaleRat (mesh 0 (1/2) (2^d)) (DyadicTrigonometry.powerCosine d j)))

theorem fixedMesh_valid (d : Nat) : (fixedMesh d).Valid := by
  apply Integral.finiteRawSum_valid
  intro X hX
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hX
  exact RealRaw.scaleRat_valid (DyadicTrigonometry.powers_valid d j).1

private theorem point_angle (d j : Nat) :
    2*leftPoint 0 (1/2) (2^d) j=DyadicTrigonometry.gridAngle d j := by
  have hp:=Nat.two_pow_pos d
  have hcast : ((2^d : Nat) : Rat)=(2 : Rat)^d := by simp
  simp only [leftPoint,mesh,if_neg (Nat.ne_of_gt hp),Rat.zero_add,
    DyadicTrigonometry.gridAngle,DyadicTrigonometry.angle,meshRadius,hcast,Rat.div_def,Rat.one_mul]
  grind

theorem fixedMesh_equiv (d : Nat) :
    (fixedMesh d).Equiv (CosineFTC.fixedMesh provider 0 (1/2) (2^d-1)) := by
  have hm : 2^d-1+1=2^d := by have hp:=Nat.two_pow_pos d; omega
  unfold fixedMesh CosineFTC.fixedMesh
  rw [hm]
  apply Integral.finiteRawSum_equiv_of_forall
  · apply Integral.finiteRawListEquiv_map_of_forall
    intro j hj
    have hjm:=List.mem_range.mp hj
    apply RealRaw.scaleRat_equiv
    have hx:=CosineFTC.grid_onHalf (a:=0) (b:=1/2)
      ⟨by decide +kernel,by decide +kernel⟩ ⟨by decide +kernel,by decide +kernel⟩
      (by decide +kernel) (Nat.two_pow_pos d) (Nat.le_of_lt hjm)
    unfold CosineFTC.cosine
    rw [dif_pos hx]
    change (DyadicTrigonometry.powerCosine d j).Equiv
      (ClockTrigonometry.cosine (2*leftPoint 0 (1/2) (2^d) j))
    rw [point_angle]
    exact (DyadicTrigonometry.powers_equiv d j (Nat.le_of_lt hjm)).1
  · intro X hX
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp hX
    exact RealRaw.scaleRat_valid (DyadicTrigonometry.powers_valid d j).1
  · intro X hX
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp hX
    exact RealRaw.scaleRat_valid (CosineFTC.cosine_valid provider _)

def error (d : Nat) : Rat := 1000*meshRadius d

theorem error_shrinks : ShrinksToZero error := by
  apply shrinksToZero_of_natOverSuccBound (C:=1000)
  intro n
  have h:=Rat.mul_le_mul_of_nonneg_left (meshRadius_le n) (by decide : (0 : Rat) <=1000)
  simpa only [error,Rat.div_def,Rat.one_mul,show ((1000 : Nat) : Rat)=1000 by decide +kernel] using h

private theorem error_eq_old (d : Nat) : CosineFTC.error 0 (1/2) (2^d-1)=error d := by
  have hm : 2^d-1+1=2^d := by have hp:=Nat.two_pow_pos d; omega
  have hcast : ((2^d : Nat) : Rat)=(2 : Rat)^d := by simp
  simp only [CosineFTC.error,hm,error,meshRadius,hcast,Rat.div_def,Rat.one_mul]
  grind

private theorem expanded_transfer {X Y Z : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (h : X.Equiv Y) (r : Rat)
    (hover : ∀ q t, (QInterval.expand (Y.compute q) r).Overlaps (Z.compute t)) :
    ∀ n t, (QInterval.expand (X.compute n) r).Overlaps (Z.compute t) := by
  intro n t
  have all:=RealRaw.allStagesOverlap_of_equiv hX hY h
  have hbounds : ∀ eps : QPos,
      (X.compute n).lo-r <=(Z.compute t).hi+eps.val ∧
      (Z.compute t).lo <=(X.compute n).hi+r+eps.val := by
    intro eps
    obtain ⟨m,hm⟩:=hY.2.2 eps
    have w:=hm m (Nat.le_refl m)
    have ov:=(RealRaw.compareAt_overlap_iff _ _ n m).1 (all n m)
    have hz:=hover m t
    unfold QInterval.expand QInterval.Overlaps QInterval.width at *
    constructor <;> grind
  exact ⟨le_of_slack (fun eps=>(hbounds eps).1),le_of_slack (fun eps=>(hbounds eps).2)⟩

def endpoint : RealRaw := CosineFTC.endpoint provider 0 (1/2)

theorem endpoint_valid : endpoint.Valid := CosineFTC.endpoint_valid provider 0 (1/2)

theorem fixedMesh_overlaps (d q t : Nat) :
    (QInterval.expand ((fixedMesh d).compute q) (error d)).Overlaps (endpoint.compute t) := by
  apply expanded_transfer (fixedMesh_valid d) (CosineFTC.fixedMesh_valid provider 0 (1/2) (2^d-1))
    (fixedMesh_equiv d) (error d) (n:=q) (t:=t)
  intro q t
  have h:=CosineFTC.fixedMesh_overlaps_endpoint provider
    (a:=0) (b:=1/2) ⟨by decide +kernel,by decide +kernel⟩
    ⟨by decide +kernel,by decide +kernel⟩ (by decide +kernel) (2^d-1) q t
  rw [error_eq_old] at h
  exact h

/-- Literal dyadic cosine integration, not a disguised endpoint evaluator. -/
def integral : RealRaw := Integral.Dovetail.raw fixedMesh error

theorem integral_valid : integral.Valid :=
  Integral.Dovetail.raw_valid fixedMesh_valid endpoint_valid error_shrinks fixedMesh_overlaps

theorem integral_equiv_endpoint : integral.Equiv endpoint :=
  Integral.Dovetail.raw_equiv_endpoint fixedMesh_overlaps

theorem integral_equiv_reciprocalPi : integral.Equiv reciprocalPiRaw := by
  have ho : ClosedCosineIntegral.quarterIntegral.Equiv endpoint := by
    have h:=ClosedCosineIntegral.viaFTC 0 (1/2)
      ⟨by decide +kernel,by decide +kernel⟩ ⟨by decide +kernel,by decide +kernel⟩ (by decide +kernel)
    simpa only [ClosedCosineIntegral.quarterIntegral,ClosedCosineIntegral.integral,endpoint,CosineFTC.endpoint,CosineFTC.sine,
      dif_pos (show GeometricSineDerivative.OnHalf 0 from ⟨by decide +kernel,by decide +kernel⟩),
      dif_pos (show GeometricSineDerivative.OnHalf (1/2) from ⟨by decide +kernel,by decide +kernel⟩)] using h
  exact RealRaw.equiv_trans integral_valid endpoint_valid reciprocalPiRaw_valid integral_equiv_endpoint
    (RealRaw.equiv_trans endpoint_valid ClosedCosineIntegral.quarterIntegral_valid reciprocalPiRaw_valid
      (RealRaw.equiv_symm ho) ClosedCosineIntegral.quarterIntegral_equiv_reciprocalPi)

end DyadicCosineIntegral
end ComputableAnalysis
