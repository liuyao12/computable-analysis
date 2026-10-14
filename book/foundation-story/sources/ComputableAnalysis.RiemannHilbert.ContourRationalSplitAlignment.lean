import ComputableAnalysis.RiemannHilbert.ContourRationalSplitMesh

/-! The executable rational split lattice aligns whole and subedge meshes
at every positive integer stage. Exact finite concatenation follows. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem intervalGridStep_of_width (I : QInterval) (K M : Nat) (u : Rat)
    (hK : 0<K) (hwidth : I.width=(K:Rat)*u) :
    intervalGridStep I (K*M)=u/(M:Rat) := by
  have hk := Rat.mul_inv_cancel (K:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hK))
  unfold intervalGridStep
  rw [hwidth,Rat.natCast_mul,Rat.div_def,Rat.inv_mul_rev,Rat.div_def]
  grind only

theorem rationalSplit_total_width (I : QInterval) (c : Rat) (hl : I.lo<c) (hr : c<I.hi) :
    I.width=((rationalSplitLeftCount I c+rationalSplitRightCount I c:Nat):Rat)*rationalSplitUnit I c := by
  have hL := rationalSplit_left_width I c hl
  have hR := rationalSplit_right_width I c hr
  rw [Rat.natCast_add]
  unfold QInterval.width
  grind only

theorem rationalSplit_mesh_alignment (I : QInterval) (c : Rat) (hl : I.lo<c) (hr : c<I.hi)
    (M : Nat) (hM : 0<M) :
    let L := rationalSplitLeftCount I c*M
    let R := rationalSplitRightCount I c*M
    intervalGridStep I (L+R)=intervalGridStep (splitIntervalLeft I c) L ∧
    intervalGridStep I (L+R)=intervalGridStep (splitIntervalRight I c) R ∧
    I.lo+(L:Rat)*intervalGridStep I (L+R)=c := by
  let L := rationalSplitLeftCount I c
  let R := rationalSplitRightCount I c
  let u := rationalSplitUnit I c
  have hL : 0<L := rationalSplitLeftCount_pos I c hl
  have hR : 0<R := rationalSplitRightCount_pos I c hr
  have htotal : L*M+R*M=(L+R)*M := (Nat.add_mul L R M).symm
  have hwL : (splitIntervalLeft I c).width=(L:Rat)*u := (rationalSplit_left_width I c hl).symm
  have hwR : (splitIntervalRight I c).width=(R:Rat)*u := (rationalSplit_right_width I c hr).symm
  have hsL := intervalGridStep_of_width (splitIntervalLeft I c) L M u hL hwL
  have hsR := intervalGridStep_of_width (splitIntervalRight I c) R M u hR hwR
  have hs : intervalGridStep I (L*M+R*M)=u/(M:Rat) := by
    rw [htotal]
    exact intervalGridStep_of_width I (L+R) M u (by omega) (rationalSplit_total_width I c hl hr)
  refine ⟨hs.trans hsL.symm,hs.trans hsR.symm, ?_⟩
  change I.lo+((L*M:Nat):Rat)*intervalGridStep I (L*M+R*M)=c
  rw [hs,Rat.natCast_mul,Rat.div_def]
  have hm := Rat.mul_inv_cancel (M:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  have hw := rationalSplit_left_width I c hl
  change (L:Rat)*u=c-I.lo at hw
  grind only

theorem rationalSplit_prefix_aligned (sample : Rat → Scalar) (I : QInterval) (c : Rat)
    (hl : I.lo<c) (hr : c<I.hi) (M : Nat) (hM : 0<M) :
    intervalGridPrefix sample I ((rationalSplitLeftCount I c+rationalSplitRightCount I c)*M) ≈
      scalarSum (intervalGridPrefix sample (splitIntervalLeft I c) (rationalSplitLeftCount I c*M))
        (intervalGridPrefix sample (splitIntervalRight I c) (rationalSplitRightCount I c*M)) := by
  have h := rationalSplit_mesh_alignment I c hl hr M hM
  have he := intervalGridPrefix_split_aligned sample I c (rationalSplitLeftCount I c*M)
    (rationalSplitRightCount I c*M) h.1 h.2.1 h.2.2
  simpa only [←Nat.add_mul] using he

end ComputableAnalysis.RiemannHilbert.RectangularContour
