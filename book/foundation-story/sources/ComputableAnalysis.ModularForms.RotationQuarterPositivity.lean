import ComputableAnalysis.ModularForms.RepresentedRotationAgreement

/-! Finite rational positivity evidence for rotations on the quarter-turn angle range. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem rotationQuarterGrid_positive : ∀ j : Fin 65,
    (3:Rat)/4≤(RotationSeries.uniformRotationBox (1+(j.val:Rat)/64) 0).lo.im := by
  decide +kernel

theorem rotationQuarter_rational_grid (T : Rat) (hl : 1≤T) (hu : T≤2) :
    ∃ j : Fin 65, qabs (T-(1+(j.val:Rat)/64))≤(1:Rat)/64 := by
  let i := (64*(T-1)).floor
  have hf := Rat.floor_le (64*(T-1))
  have ht := Rat.lt_floor_add_one (64*(T-1))
  change (i:Rat)≤64*(T-1) at hf
  change 64*(T-1)<((i+1:Int):Rat) at ht
  have hone : ((1:Int):Rat)=(1:Rat) := by decide +kernel
  rw [Rat.intCast_add,hone] at ht
  have hi0r : (-1:Rat)<(i:Rat) := by grind only
  have hi64r : (i:Rat)≤64 := by grind only
  have hi0 : 0≤i := by
    have hcast : ((-1:Int):Rat)=(-1:Rat) := by decide +kernel
    have hc : ((-1:Int):Rat)<(i:Rat) := by rw [hcast]; exact hi0r
    have hh : (-1:Int)<i := by exact_mod_cast hc
    omega
  have hi64 : i≤64 := by exact_mod_cast hi64r
  let j : Fin 65 := ⟨i.toNat,by omega⟩
  have hc : (j.val:Rat)=(i:Rat) := by
    have h : (j.val:Int)=i := by change (i.toNat:Int)=i; omega
    exact_mod_cast h
  refine ⟨j,?_⟩
  rw [hc]
  have he : 0≤T-(1+(i:Rat)/64) := by grind only
  rw [qabs_eq_self_of_nonneg he]
  grind only

theorem rotationQuarter_rational_positive (T : Rat) (hl : 1≤T) (hu : T≤2) :
    (1:Rat)/2≤(RotationSeries.uniformRotationBox T 0).lo.im := by
  obtain ⟨j,hj⟩ := rotationQuarter_rational_grid T hl hu
  let U : Rat := 1+(j.val:Rat)/64
  have hU : qabs U≤2 := by
    have hn : (j.val:Rat)≤64 := by exact_mod_cast (show j.val≤64 by omega)
    have hp : 0≤(j.val:Rat) := Rat.natCast_nonneg
    have hpos : 0≤U := by dsimp [U]; grind only
    rw [qabs_eq_self_of_nonneg hpos]
    dsimp [U]
    grind only
  have hT : qabs T≤2 := by
    have hp : 0≤T := by grind only
    rw [qabs_eq_self_of_nonneg hp]
    exact hu
  have hc := RotationSeries.uniformRotationBox_contained_expand_of_input_near T U (1/64) hT hU 0 hj
  have hg := rotationQuarterGrid_positive j
  simp only [QBox.NestedIn,QComplex.le_def,QBox.expand] at hc
  have hh := hc.1.2
  change (RotationSeries.uniformRotationBox U 0).lo.im-16*((1:Rat)/64)≤
    (RotationSeries.uniformRotationBox T 0).lo.im at hh
  change (3:Rat)/4≤(RotationSeries.uniformRotationBox U 0).lo.im at hg
  generalize (RotationSeries.uniformRotationBox U 0).lo.im=a at hh hg
  generalize (RotationSeries.uniformRotationBox T 0).lo.im=b at hh ⊢
  grind only

theorem rotationQuarter_represented_positive (A : RotationLift.HalfPiInput) :
    (RotationLift.HalfPiInput.rotation A).imagPart.Pos := by
  let T := (A.raw.compute 127).midpoint
  have hw := A.valid.1 127
  have ho : (A.raw.compute 127).lo≤(A.raw.compute 127).hi := by
    change 0≤(A.raw.compute 127).hi-(A.raw.compute 127).lo at hw
    grind only
  have hm := QInterval.midpoint_mem ho
  have hl : 1≤T := Rat.le_trans (A.bounds 127).1 hm.1
  have hu : T≤2 := Rat.le_trans hm.2 (A.bounds 127).2
  have hp := rotationQuarter_rational_positive T hl hu
  have hn := (RotationSeries.uniformRotationExpRaw_valid T (A.midpoint_qabs_le_two 127)).2.1
    0 127 (by omega)
  have hcan : (1:Rat)/2≤((RotationLift.HalfPiInput.rotationCandidate A).compute 127).lo.im :=
    Rat.le_trans hp hn.2.2.1
  have hwidth := A.width_le_two_div_succ 127
  have hrad : RotationLift.HalfPiInput.rotationRadius A 127≤(1:Rat)/4 := by
    change 16*(A.raw.compute 127).width≤(1:Rat)/4
    have he : (2:Rat)/((127+1:Nat):Rat)=(1:Rat)/64 := by decide +kernel
    rw [he] at hwidth
    generalize (A.raw.compute 127).width=w at hwidth ⊢
    grind only
  have hc := QBox.intersection_contained_right
    (cauchyStabilizeCompute (RotationLift.HalfPiInput.rotationCandidate A).compute
      (RotationLift.HalfPiInput.rotationRadius A) 126)
    (QBox.expand ((RotationLift.HalfPiInput.rotationCandidate A).compute 127)
      (RotationLift.HalfPiInput.rotationRadius A 127))
  simp only [QBox.NestedIn,QComplex.le_def,QBox.expand] at hc
  have hlow := hc.1.2
  change ((RotationLift.HalfPiInput.rotationCandidate A).compute 127).lo.im-
    RotationLift.HalfPiInput.rotationRadius A 127≤((RotationLift.HalfPiInput.rotation A).compute 127).lo.im at hlow
  refine ⟨127,?_⟩
  change 0<((RotationLift.HalfPiInput.rotation A).compute 127).lo.im
  generalize ((RotationLift.HalfPiInput.rotationCandidate A).compute 127).lo.im=a at hcan hlow
  generalize RotationLift.HalfPiInput.rotationRadius A 127=r at hrad hlow
  generalize ((RotationLift.HalfPiInput.rotation A).compute 127).lo.im=b at hlow ⊢
  grind only

end ComputableAnalysis.ModularForms
