import ComputableAnalysis.TrigSquareVariable
import ComputableAnalysis.RationalLipschitzLift

/-! Periodic assembly of the variable-endpoint formula. The integer part is
computed only for rational samples, never by a discontinuous real-floor oracle. -/
namespace ComputableAnalysis.TrigSquareGlobal
open ClosedArctanInverse ClockTrigonometry CartwrightMoments FiniteSampleCalculus
open RationalSampleLimits IntervalSelections MonotoneAverage

abbrev P := CosineSquare.primitiveSample

def phase (y : Rat) : Rat := y-(y.floor:Rat)
theorem phase_unit (y : Rat) : Unit (phase y) := by
  have h0:=Rat.floor_le y
  have h1:=Rat.lt_floor_add_one y
  rw [Rat.intCast_add] at h1
  change y<(y.floor:Rat)+1 at h1
  unfold phase;constructor <;> grind only

def pieceSample (k : Int) (t : Rat) (q : Nat) : Rat :=
  (k:Rat)/2+if k%2=0 then P t q else t-P t q

def sample (y : Rat) (q : Nat) : Rat := pieceSample y.floor (phase y) q

def piece (k : Int) (t : Rat) : RealRaw :=
  (RealRaw.ofRat ((k:Rat)/2)) + if k%2=0 then TrigSquareVariable.endpoint t
    else (RealRaw.ofRat t)-TrigSquareVariable.endpoint t

def endpoint (y : Rat) : RealRaw := piece y.floor (phase y)

theorem piece_valid (k : Int) (t : Rat) (ht : Unit t) : (piece k t).Valid := by
  unfold piece
  apply RealRaw.add_valid (RealRaw.ofRat_valid _)
  split
  · exact TrigSquareVariable.endpoint_valid t ht
  · exact RealRaw.sub_valid (RealRaw.ofRat_valid _) (TrigSquareVariable.endpoint_valid t ht)

theorem endpoint_valid (y : Rat) : (endpoint y).Valid := piece_valid _ _ (phase_unit y)

theorem piece_mem (k : Int) (t : Rat) (ht : Unit t) (q : Nat) :
    InBox (pieceSample k t q) ((piece k t).compute q) := by
  unfold pieceSample piece
  split
  · exact ClockTrigonometry.add_mem (rat_mem _ _) (TrigSquareVariable.endpoint_mem t ht q)
  · exact ClockTrigonometry.add_mem (rat_mem _ _)
      (sub_mem (rat_mem _ _) (TrigSquareVariable.endpoint_mem t ht q))

theorem sample_mem (y : Rat) (q : Nat) : InBox (sample y q) ((endpoint y).compute q) :=
  piece_mem _ _ (phase_unit y) q

def bound : Rat := CosineSquare.primitiveModel.slopeBound+CosineSquare.primitiveModel.errorBound+3

theorem bound_ge_three : 3≤bound := by
  have h:=CosineSquare.primitiveModel.slopeBound_nonneg
  have g:=CosineSquare.primitiveModel.errorBound_nonneg
  unfold bound;grind only

theorem piece_increment (k : Int) {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a≤b) :
    ∃ N, ∀ q, N≤q → qabs (pieceSample k b q-pieceSample k a q)≤bound*(b-a) := by
  by_cases he : a=b
  · subst b;refine ⟨0,fun q hq=>?_⟩
    rw [Rat.sub_self,Rat.sub_self,Rat.mul_zero];exact (by decide +kernel : qabs (0:Rat)≤0)
  have hp : a<b := by grind only
  obtain ⟨N,hN⟩:=CosineSquare.primitiveModel.increment_eventual a b ha hb hp
  refine ⟨N,fun q hq=>?_⟩
  have h:=hN q hq
  have ht:=qabs_sub_le (b-a) (P b q-P a q)
  rw [qabs_eq_self_of_nonneg (by grind : 0≤b-a)] at ht
  have hn : 0≤b-a := by grind only
  unfold pieceSample
  split
  · have he : ((k:Rat)/2+P b q)-((k:Rat)/2+P a q)=P b q-P a q := by grind only
    rw [he];unfold bound;grind only
  · have he : ((k:Rat)/2+(b-P b q))-((k:Rat)/2+(a-P a q))=(b-a)-(P b q-P a q) := by grind only
    rw [he];unfold bound;grind only

theorem initial_close (k : Int) : Close (pieceSample k 0) (fun _=>(k:Rat)/2) := by
  unfold pieceSample
  split
  · have h:=close_add (close_refl (fun _=>(k:Rat)/2)) (close_zero_of_small TrigSquareVariable.initial_zero)
    simpa only [Rat.add_zero] using h
  · have h:=close_sub (close_refl (fun _=>(k:Rat)/2)) (close_zero_of_small TrigSquareVariable.initial_zero)
    have he : ∀ q, (k:Rat)/2+(0-P 0 q)=(k:Rat)/2-P 0 q := by intros;grind only
    simpa only [he,show ∀ a:Rat,a-0=a by intros;grind] using h

theorem final_close (k : Int) : Close (pieceSample k 1) (fun _=>(k:Rat)/2+1/2) := by
  have h : Close (P 1) (fun _=>(1/2:Rat)) := by
    have hh:=close_add CosineSquare.primitive_endpoints_close (close_zero_of_small TrigSquareVariable.initial_zero)
    simpa only [show ∀ a b:Rat,(a-b)+b=a by intros;grind,Rat.add_zero] using hh
  unfold pieceSample
  split
  · exact close_add (close_refl _) h
  · have hh:=close_add (close_refl (fun _=>(k:Rat)/2)) (close_sub (close_refl (fun _=>(1:Rat))) h)
    simpa only [show (1:Rat)-1/2=1/2 by decide +kernel] using hh

theorem seam_close (k : Int) : Close (pieceSample k 1) (pieceSample (k+1) 0) := by
  have he : (k:Rat)/2+1/2=((k+1:Int):Rat)/2 := by rw [Rat.intCast_add];simp only [Rat.div_def];grind only
  exact close_trans (by simpa only [he] using final_close k) (close_symm (initial_close (k+1)))

/-- The bounded oscillatory correction, before any integral evaluation. -/
theorem correction_bound (y : Rat) (q : Nat) : qabs (sample y q-y/2)≤1 := by
  have hb:=ClockTrigonometry.sample_bounds (phase y) q
  have hr:=CosineSquare.reciprocalSample_unit q
  have hρ : qabs (CosineSquare.reciprocalSample q)≤1 := by rw [qabs_eq_self_of_nonneg hr.1];exact hr.2
  have hs : qabs (s (phase y) q)≤1 := by rw [qabs_eq_self_of_nonneg hb.2.2.1];exact hb.2.2.2
  have hc : qabs (c (phase y) q)≤1 := by rw [qabs_eq_self_of_nonneg hb.1];exact hb.2.1
  have h:=mul_abs_bound (by decide +kernel : (0:Rat)≤1) hρ
    (by simpa only [Rat.one_mul] using mul_abs_bound (by decide +kernel : (0:Rat)≤1) hs hc)
  unfold sample pieceSample P CosineSquare.primitiveSample
  split
  · have he : (y.floor:Rat)/2+(phase y/2+CosineSquare.reciprocalSample q*s (phase y) q*c (phase y) q)-y/2=
        CosineSquare.reciprocalSample q*(s (phase y) q*c (phase y) q) := by unfold phase;simp only [Rat.div_def];grind only
    rw [he];simpa only [Rat.one_mul] using h
  · have he : (y.floor:Rat)/2+(phase y-(phase y/2+CosineSquare.reciprocalSample q*s (phase y) q*c (phase y) q))-y/2=
        -(CosineSquare.reciprocalSample q*(s (phase y) q*c (phase y) q)) := by unfold phase;simp only [Rat.div_def];grind only
    rw [he,qabs_neg];simpa only [Rat.one_mul] using h

theorem ordered_sample_difference {a b : Rat} (hab : a≤b) (eps : QPos) :
    ∃ N, ∀ q, N≤q → qabs (sample b q-sample a q)≤bound*(b-a)+eps.val := by
  have hfloor:=Rat.floor_monotone hab
  have ha:=phase_unit a;have hb:=phase_unit b
  by_cases he : a.floor=b.floor
  · have hp : phase a≤phase b := by unfold phase;rw [he];grind only
    obtain ⟨N,hN⟩:=piece_increment a.floor ha hb hp
    refine ⟨N,fun q hq=>?_⟩
    have h:=hN q hq
    have hphase : phase b-phase a=b-a := by unfold phase;rw [he];grind only
    rw [hphase] at h
    change qabs (pieceSample b.floor (phase b) q-pieceSample a.floor (phase a) q)≤_
    rw [←he];have heps:=eps.property;grind only
  by_cases hnext : b.floor=a.floor+1
  · obtain ⟨N,hN⟩:=piece_increment a.floor ha ⟨by decide,by decide⟩ ha.2
    obtain ⟨M,hM⟩:=piece_increment b.floor ⟨by decide,by decide⟩ hb hb.1
    obtain ⟨L,hL⟩:=seam_close a.floor eps
    refine ⟨max N (max M L),fun q hq=>?_⟩
    have h1:=hN q (by omega);have h2:=hM q (by omega);have h3:=hL q (by omega)
    have ht1:=qabs_add_le (pieceSample b.floor (phase b) q-pieceSample b.floor 0 q)
      (pieceSample b.floor 0 q-pieceSample a.floor 1 q)
    have ht2:=qabs_add_le ((pieceSample b.floor (phase b) q-pieceSample b.floor 0 q)+
      (pieceSample b.floor 0 q-pieceSample a.floor 1 q)) (pieceSample a.floor 1 q-pieceSample a.floor (phase a) q)
    have hseam : qabs (pieceSample b.floor 0 q-pieceSample a.floor 1 q)≤eps.val := by
      rw [hnext,show pieceSample (a.floor+1) 0 q-pieceSample a.floor 1 q= -(pieceSample a.floor 1 q-pieceSample (a.floor+1) 0 q) by grind,qabs_neg]
      exact h3
    have hphase : (1-phase a)+phase b=b-a := by
      unfold phase;rw [hnext,Rat.intCast_add];change (1-(a-(a.floor:Rat)))+(b-((a.floor:Rat)+1))=b-a;grind only
    have heq : ((pieceSample b.floor (phase b) q-pieceSample b.floor 0 q)+
      (pieceSample b.floor 0 q-pieceSample a.floor 1 q))+(pieceSample a.floor 1 q-pieceSample a.floor (phase a) q)=sample b q-sample a q := by unfold sample;grind only
    rw [heq] at ht2
    have hzero : phase b-0=phase b := by grind
    rw [hzero] at h2
    have hc : bound*(1-phase a)+bound*phase b=bound*(b-a) := by rw [←Rat.mul_add,hphase]
    grind only
  · have hf : a.floor+2≤b.floor := by omega
    have hfc : ((a.floor+2:Int):Rat)≤(b.floor:Rat) := Rat.intCast_le_intCast.mpr hf
    have hfa:=Rat.lt_floor_add_one a
    have hfb:=Rat.floor_le b
    rw [Rat.intCast_add] at hfc hfa
    have hgap : 1≤b-a := by change (a.floor:Rat)+2≤(b.floor:Rat) at hfc;change a<(a.floor:Rat)+1 at hfa;grind only
    refine ⟨0,fun q hq=>?_⟩
    have h1:=correction_bound a q;have h2:=correction_bound b q
    have ht1:=qabs_sub_le (sample b q-b/2) (sample a q-a/2)
    have ht2:=qabs_add_le ((sample b q-b/2)-(sample a q-a/2)) ((b-a)/2)
    have heq : ((sample b q-b/2)-(sample a q-a/2))+(b-a)/2=sample b q-sample a q := by simp only [Rat.div_def];grind only
    rw [heq,qabs_eq_self_of_nonneg (by simp only [Rat.div_def];grind : 0≤(b-a)/2)] at ht2
    have hB:=Rat.mul_le_mul_of_nonneg_right bound_ge_three (by grind : 0≤b-a)
    have heps:=eps.property
    simp only [Rat.div_def] at ht2
    grind only

theorem sample_difference (a b : Rat) (eps : QPos) :
    ∃ N, ∀ q, N≤q → qabs (sample a q-sample b q)≤bound*qabs (a-b)+eps.val := by
  rcases (Rat.le_total (a:=a) (b:=b)) with hab | hba
  · obtain ⟨N,hN⟩:=ordered_sample_difference hab eps
    refine ⟨N,fun q hq=>?_⟩
    rw [show sample a q-sample b q= -(sample b q-sample a q) by grind,qabs_neg,
      show qabs (a-b)=b-a by unfold qabs;split <;> grind]
    exact hN q hq
  · obtain ⟨N,hN⟩:=ordered_sample_difference hba eps
    refine ⟨N,fun q hq=>?_⟩
    rw [qabs_eq_self_of_nonneg (by grind : 0≤a-b)]
    exact hN q hq

def endpointData : RationalLipschitzLift.Data where
  raw := endpoint
  valid := endpoint_valid
  bound := bound
  bound_nonneg := by have h:=bound_ge_three;grind
  lipschitz := by
    intro a b n m
    apply endpoint_le_of_eventually (endpoint_valid a) (endpoint_valid b)
      (sample a) (sample b) (sample_mem a) (sample_mem b) _ _ n m
    intro eps
    obtain ⟨N,hN⟩:=sample_difference a b eps
    exact ⟨N,fun q hq=>by have h:=hN q hq;have h1:=self_le_qabs (sample a q-sample b q);grind only⟩

/-- A whole half-period is itself computed by rectangles. -/
def wholeCell : RealRaw := TrigSquareVariable.integral 1 ⟨by decide +kernel,by decide +kernel⟩

theorem wholeCell_valid : wholeCell.Valid := TrigSquareVariable.integral_valid _ _

theorem endpoint_one : (TrigSquareVariable.endpoint 1).Equiv (RealRaw.ofRat (1/2)) := by
  have h : Close (P 1) (fun _=>(1/2:Rat)) := by
    have hh:=close_add CosineSquare.primitive_endpoints_close (close_zero_of_small TrigSquareVariable.initial_zero)
    simpa only [show ∀ a b:Rat,(a-b)+b=a by intros;grind,Rat.add_zero] using hh
  exact equiv_of_close (TrigSquareVariable.endpoint_valid 1 ⟨by decide,by decide⟩) (RealRaw.ofRat_valid _)
    (P 1) (fun _=>1/2) (TrigSquareVariable.endpoint_mem 1 ⟨by decide,by decide⟩) (rat_mem _) h

theorem wholeCell_value : wholeCell.Equiv (RealRaw.ofRat (1/2)) :=
  RealRaw.equiv_trans wholeCell_valid (TrigSquareVariable.endpoint_valid 1 ⟨by decide,by decide⟩)
    (RealRaw.ofRat_valid _) (TrigSquareVariable.definite_integral 1 ⟨by decide,by decide⟩) endpoint_one

theorem scale_constant (a b : Rat) : (RealRaw.scaleRat a (RealRaw.ofRat b)).Equiv (RealRaw.ofRat (a*b)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute,RealRaw.ofRat]
  split <;> exact ⟨Rat.le_refl,Rat.le_refl⟩

/-- The genuine local square integrand: alternate cosine and sine charts. -/
def cellDensity (k : Int) (t : Rat) (q : Nat) : Rat :=
  if k%2=0 then CosineSquare.sample t q else SineSquare.sample t q

def cellIntegral (k : Int) (t : Rat) (ht : Unit t) : RealRaw :=
  if k%2=0 then TrigSquareVariable.integral t ht else TrigSquareVariable.sineIntegral t ht

theorem cellIntegral_valid (k : Int) (t : Rat) (ht : Unit t) : (cellIntegral k t ht).Valid := by
  unfold cellIntegral;split
  · exact TrigSquareVariable.integral_valid _ _
  · exact TrigSquareVariable.sineIntegral_valid _ _

/-- Each assembled cell contains literal rectangle sums of the correct density,
including the odd cells. This is independent of any endpoint-value theorem. -/
theorem cell_quadrature (k : Int) (t : Rat) (ht : Unit t) (q : Nat) :
    InBox (t*left (fun u=>cellDensity k (t*u) q) 0 1 q) ((cellIntegral k t ht).compute q) := by
  unfold cellIntegral cellDensity
  split
  · simpa only [TrigSquareVariable.sumSample,if_pos ‹k%2=0›] using TrigSquareVariable.sumSample_mem t ht q
  · simpa only [TrigSquareVariable.sineSumSample,if_neg ‹¬k%2=0›] using TrigSquareVariable.sineSumSample_mem t ht q

/-- Every complete cell has the same integral; thus multiplication by the
signed number of complete cells compresses their finite sum. -/
theorem whole_cell_agreement (k : Int) :
    (cellIntegral k 1 ⟨by decide +kernel,by decide +kernel⟩).Equiv wholeCell := by
  unfold cellIntegral
  split
  · exact RealRaw.equiv_refl _ wholeCell_valid
  · have h:=RealRaw.sub_equiv (RealRaw.ofRat_valid 1) (RealRaw.ofRat_valid 1)
      wholeCell_valid (RealRaw.ofRat_valid (1/2))
      (RealRaw.equiv_refl _ (RealRaw.ofRat_valid _)) wholeCell_value
    have hrat : (RealRaw.ofRat 1-RealRaw.ofRat (1/2)).Equiv (RealRaw.ofRat (1/2)) := by
      intro n
      apply (RealRaw.compareAt_overlap_iff _ _ n n).2
      exact (by decide +kernel : (1:Rat)-1/2≤1/2 ∧ (1:Rat)/2≤1-1/2)
    exact RealRaw.equiv_trans (TrigSquareVariable.sineIntegral_valid 1 ⟨by decide,by decide⟩)
      (RealRaw.ofRat_valid _) wholeCell_valid
      (RealRaw.equiv_trans (TrigSquareVariable.sineIntegral_valid 1 ⟨by decide,by decide⟩)
        (RealRaw.sub_valid (RealRaw.ofRat_valid _) (RealRaw.ofRat_valid _)) (RealRaw.ofRat_valid _) h hrat)
      (RealRaw.equiv_symm wholeCell_value)

/-- Signed full-cell contributions, then the actual variable partial-cell
quadrature. Odd cells use the complementary sine-square rectangle sums. -/
def integralAt (y : Rat) : RealRaw :=
  (RealRaw.scaleRat (y.floor:Rat) wholeCell) +
    if y.floor%2=0 then TrigSquareVariable.integral (phase y) (phase_unit y)
    else (RealRaw.ofRat (phase y))-TrigSquareVariable.integral (phase y) (phase_unit y)

theorem integralAt_valid (y : Rat) : (integralAt y).Valid := by
  unfold integralAt
  apply RealRaw.add_valid (RealRaw.scaleRat_valid wholeCell_valid)
  split
  · exact TrigSquareVariable.integral_valid _ _
  · exact RealRaw.sub_valid (RealRaw.ofRat_valid _) (TrigSquareVariable.integral_valid _ _)

theorem rational_definite_integral_of_local
    (localLaw : ∀ t (ht : Unit t), (TrigSquareVariable.integral t ht).Equiv (TrigSquareVariable.endpoint t))
    (y : Rat) : (integralAt y).Equiv (endpoint y) := by
  have wholeCell_value : wholeCell.Equiv (RealRaw.ofRat (1/2)) :=
    RealRaw.equiv_trans wholeCell_valid (TrigSquareVariable.endpoint_valid 1 ⟨by decide,by decide⟩)
      (RealRaw.ofRat_valid _) (localLaw 1 ⟨by decide,by decide⟩) endpoint_one
  have hcell : (RealRaw.scaleRat (y.floor:Rat) wholeCell).Equiv (RealRaw.ofRat ((y.floor:Rat)/2)) := by
    have h:=RealRaw.equiv_trans (RealRaw.scaleRat_valid wholeCell_valid)
      (RealRaw.scaleRat_valid (RealRaw.ofRat_valid (1/2))) (RealRaw.ofRat_valid _)
      (RealRaw.scaleRat_equiv (r:=(y.floor:Rat)) wholeCell_value) (scale_constant (y.floor:Rat) (1/2))
    simpa only [Rat.div_def,Rat.one_mul] using h
  unfold integralAt endpoint piece
  apply RealRaw.add_equiv (RealRaw.scaleRat_valid wholeCell_valid) (RealRaw.ofRat_valid _)
  · split
    · exact TrigSquareVariable.integral_valid _ _
    · exact RealRaw.sub_valid (RealRaw.ofRat_valid _) (TrigSquareVariable.integral_valid _ _)
  · split
    · exact TrigSquareVariable.endpoint_valid (phase y) (phase_unit y)
    · exact RealRaw.sub_valid (RealRaw.ofRat_valid _) (TrigSquareVariable.endpoint_valid (phase y) (phase_unit y))
  · exact hcell
  · split
    · exact localLaw _ _
    · exact RealRaw.sub_equiv (RealRaw.ofRat_valid _) (RealRaw.ofRat_valid _)
        (TrigSquareVariable.integral_valid _ _) (TrigSquareVariable.endpoint_valid (phase y) (phase_unit y))
        (RealRaw.equiv_refl _ (RealRaw.ofRat_valid _)) (localLaw _ _)

theorem rational_definite_integral (y : Rat) : (integralAt y).Equiv (endpoint y) :=
  rational_definite_integral_of_local TrigSquareVariable.definite_integral y

theorem rational_definite_integral_via_Euler (y : Rat) : (integralAt y).Equiv (endpoint y) :=
  rational_definite_integral_of_local TrigSquareVariable.definite_integral_via_Euler y

def integralData : RationalLipschitzLift.Data :=
  endpointData.transport integralAt integralAt_valid rational_definite_integral

def integralDataEuler : RationalLipschitzLift.Data :=
  endpointData.transport integralAt integralAt_valid rational_definite_integral_via_Euler

/-- The oriented integral from zero to any represented real endpoint x.
Only rational approximations are folded into periods. -/
def cosineIntegral (x : RealRaw) : RealRaw :=
  RealRaw.scaleRat (1/2) (integralData.extend (RealRaw.scaleRat 2 x))

/-- Independent continuous evaluation of x/2+sin(2*pi*x)/(4*pi), using the
geometric quarter-turn sine/cosine and parity to evaluate the oscillation. -/
def cosineClosedForm (x : RealRaw) : RealRaw :=
  RealRaw.scaleRat (1/2) (endpointData.extend (RealRaw.scaleRat 2 x))

def sineIntegral (x : RealRaw) : RealRaw := x-cosineIntegral x
def sineClosedForm (x : RealRaw) : RealRaw := x-cosineClosedForm x

theorem cosineIntegral_valid (x : RealRaw) (hx : x.Valid) : (cosineIntegral x).Valid :=
  RealRaw.scaleRat_valid (integralData.extend_valid _ (RealRaw.scaleRat_valid hx))

theorem cosineClosedForm_valid (x : RealRaw) (hx : x.Valid) : (cosineClosedForm x).Valid :=
  RealRaw.scaleRat_valid (endpointData.extend_valid _ (RealRaw.scaleRat_valid hx))

theorem sineIntegral_valid (x : RealRaw) (hx : x.Valid) : (sineIntegral x).Valid :=
  RealRaw.sub_valid hx (cosineIntegral_valid x hx)

theorem sineClosedForm_valid (x : RealRaw) (hx : x.Valid) : (sineClosedForm x).Valid :=
  RealRaw.sub_valid hx (cosineClosedForm_valid x hx)

/-- Main cosine-square formula: no rationality, sign, chart, or partition
hypothesis is imposed on the supplied valid endpoint. -/
theorem cosine_definite_integral (x : RealRaw) (hx : x.Valid) :
    (cosineIntegral x).Equiv (cosineClosedForm x) :=
  RealRaw.scaleRat_equiv (integralData.congr endpointData rational_definite_integral
    (RealRaw.scaleRat 2 x) (RealRaw.scaleRat_valid hx))

theorem sine_definite_integral (x : RealRaw) (hx : x.Valid) :
    (sineIntegral x).Equiv (sineClosedForm x) :=
  RealRaw.sub_equiv hx hx (cosineIntegral_valid x hx) (cosineClosedForm_valid x hx)
    (RealRaw.equiv_refl _ hx) (cosine_definite_integral x hx)

/-- A second value proof, using exponential integration for the local pieces. -/
theorem cosine_definite_integral_via_Euler (x : RealRaw) (hx : x.Valid) :
    (cosineIntegral x).Equiv (cosineClosedForm x) :=
  RealRaw.scaleRat_equiv (integralDataEuler.congr endpointData rational_definite_integral_via_Euler
    (RealRaw.scaleRat 2 x) (RealRaw.scaleRat_valid hx))

theorem sine_definite_integral_via_Euler (x : RealRaw) (hx : x.Valid) :
    (sineIntegral x).Equiv (sineClosedForm x) :=
  RealRaw.sub_equiv hx hx (cosineIntegral_valid x hx) (cosineClosedForm_valid x hx)
    (RealRaw.equiv_refl _ hx) (cosine_definite_integral_via_Euler x hx)

theorem cosine_representation_equiv {x y : RealRaw} (hx : x.Valid) (hy : y.Valid) (h : x.Equiv y) :
    (cosineIntegral x).Equiv (cosineIntegral y) :=
  RealRaw.scaleRat_equiv (integralData.representation_equiv (RealRaw.scaleRat_valid hx)
    (RealRaw.scaleRat_valid hy) (RealRaw.scaleRat_equiv h))

theorem sine_representation_equiv {x y : RealRaw} (hx : x.Valid) (hy : y.Valid) (h : x.Equiv y) :
    (sineIntegral x).Equiv (sineIntegral y) :=
  RealRaw.sub_equiv hx hy (cosineIntegral_valid x hx) (cosineIntegral_valid y hy) h
    (cosine_representation_equiv hx hy h)

/-- The folded double-angle sine sample, from the original geometric circle. -/
def doubleSineSample (y : Rat) (q : Nat) : Rat :=
  if y.floor%2=0 then 2*s (phase y) q*c (phase y) q else -(2*s (phase y) q*c (phase y) q)

theorem closed_form_sample (x : Rat) (q : Nat) : sample (2*x) q/2=
    x/2+CosineSquare.reciprocalSample q*doubleSineSample (2*x) q/4 := by
  unfold sample pieceSample P CosineSquare.primitiveSample doubleSineSample
  split <;> unfold phase <;> simp only [Rat.div_def] <;> grind only

theorem endpoint_integer (k : Int) : (endpoint (k:Rat)).Equiv (RealRaw.ofRat ((k:Rat)/2)) := by
  have ht : phase (k:Rat)=0 := by unfold phase;rw [Rat.floor_intCast,Rat.sub_self]
  apply equiv_of_close (endpoint_valid _) (RealRaw.ofRat_valid _)
    (sample (k:Rat)) (fun _=>(k:Rat)/2) (sample_mem _) (rat_mem _)
  have he : sample (k:Rat)=pieceSample k 0 := by
    funext q
    unfold sample
    rw [Rat.floor_intCast,ht]
  rw [he]
  exact initial_close k

theorem cosine_half_integer (k : Int) :
    (cosineIntegral (RealRaw.ofRat ((k:Rat)/2))).Equiv (RealRaw.ofRat ((k:Rat)/4)) := by
  have hv:=RealRaw.ofRat_valid ((k:Rat)/2)
  have hinput : (RealRaw.scaleRat 2 (RealRaw.ofRat ((k:Rat)/2))).Equiv (RealRaw.ofRat (k:Rat)) := by
    have h:=scale_constant 2 ((k:Rat)/2)
    have he : (2:Rat)*((k:Rat)/2)=(k:Rat) := by simp only [Rat.div_def];grind only
    simpa only [he] using h
  have hr:=endpointData.representation_equiv (RealRaw.scaleRat_valid hv) (RealRaw.ofRat_valid _) hinput
  have hrat:=endpointData.at_rational (k:Rat)
  have h1:=RealRaw.equiv_trans (endpointData.extend_valid _ (RealRaw.scaleRat_valid hv))
    (endpointData.extend_valid _ (RealRaw.ofRat_valid _)) (endpoint_valid _) hr hrat
  have h2:=RealRaw.equiv_trans (endpointData.extend_valid _ (RealRaw.scaleRat_valid hv))
    (endpoint_valid _) (RealRaw.ofRat_valid _) h1 (endpoint_integer k)
  have h3:=RealRaw.scaleRat_equiv (r:=1/2) h2
  have he : (1/2:Rat)*((k:Rat)/2)=(k:Rat)/4 := by simp only [Rat.div_def];grind only
  have h4:=RealRaw.equiv_trans (cosineClosedForm_valid _ hv) (RealRaw.scaleRat_valid (RealRaw.ofRat_valid _))
    (RealRaw.ofRat_valid _) h3 (by simpa only [he] using scale_constant (1/2) ((k:Rat)/2))
  exact RealRaw.equiv_trans (cosineIntegral_valid _ hv) (cosineClosedForm_valid _ hv)
    (RealRaw.ofRat_valid _) (cosine_definite_integral _ hv) h4

theorem sine_half_integer (k : Int) :
    (sineIntegral (RealRaw.ofRat ((k:Rat)/2))).Equiv (RealRaw.ofRat ((k:Rat)/4)) := by
  have hv:=RealRaw.ofRat_valid ((k:Rat)/2)
  have h:=RealRaw.sub_equiv hv hv (cosineIntegral_valid _ hv) (RealRaw.ofRat_valid _)
    (RealRaw.equiv_refl _ hv) (cosine_half_integer k)
  apply RealRaw.equiv_trans (sineIntegral_valid _ hv) (RealRaw.sub_valid hv (RealRaw.ofRat_valid _))
    (RealRaw.ofRat_valid _) h
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change (k:Rat)/2-(k:Rat)/4≤(k:Rat)/4 ∧ (k:Rat)/4≤(k:Rat)/2-(k:Rat)/4
  simp only [Rat.div_def];constructor <;> grind only

end ComputableAnalysis.TrigSquareGlobal
