import ComputableAnalysis.ModularForms.LatticeReciprocalComparison
import ComputableAnalysis.ModularForms.ImaginaryIdentity
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws
import ComputableAnalysis.ModularForms.CMLatticeRadius163

/-! Passing uniform rational shell bounds to actual represented reciprocals. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert ComplexRaw FunctionTheory LocalODE

def latticeRegionReciprocalConstant (R H eta : Rat) : Rat :=
  (2*eta*eta+2*R*R+1)*(1+R+H)/(eta*eta)

theorem latticeRegionReciprocalConstant_nonnegative (R H eta : Rat)
    (hR : 0≤R) (hH : 0≤H) (heta : 0<eta) :
    0≤latticeRegionReciprocalConstant R H eta := by
  have he2 := Rat.mul_pos heta heta
  have hR2 := Rat.mul_nonneg hR hR
  have hC : 0≤2*eta*eta+2*R*R+1 := by grind
  have hA : 0≤1+R+H := by grind
  exact Rat.mul_nonneg (Rat.mul_nonneg hC hA) (Rat.le_of_lt (Rat.inv_pos.mpr he2))

theorem latticeInverse_region_square_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) (r : Rat)
    (hr : 0<r) (hx : -r≤(u.x:Rat) ∧ (u.x:Rat)≤r)
    (hy : -r≤(u.y:Rat) ∧ (u.y:Rat)≤r)
    (hout : r≤(u.x:Rat) ∨ (u.x:Rat)≤ -r ∨ r≤(u.y:Rat) ∨ (u.y:Rat)≤ -r) :
    Small (latticeInverse z hz u hu).val (latticeRegionReciprocalConstant R H eta/r) := by
  let v := latticeVector z u
  let a := latticeInverse z hz u hu
  let B := boxCoordinateBound (a.val.compute 0)
  let C := latticeRegionReciprocalConstant R H eta/r
  have hB : 0≤B := boxCoordinateBound_nonneg _
  have hC : 0≤C := Rat.mul_nonneg (latticeRegionReciprocalConstant_nonnegative R H eta hR hH heta)
    (Rat.le_of_lt (Rat.inv_pos.mpr hr))
  have ha : Small a.val B := small_from_box a.val a.property 0
  let E := fun n => (v.val.compute (n+N)).width+
    (v.val.compute (n+N)).height
  have hE : ShrinksToZero E := by
    change ShrinksToZero (fun n => ((fun j => (v.val.compute j).width+(v.val.compute j).height) (n+N)))
    apply SeriesLimitLaws.shrinks_shift (fun j => (v.val.compute j).width+(v.val.compute j).height)
    apply RepresentedCauchySum.sum_shrinks
    · intro eps
      obtain ⟨N,hN⟩ := v.property.2.2 eps
      exact ⟨N,fun n hn => (hN n hn).1⟩
    · intro eps
      obtain ⟨N,hN⟩ := v.property.2.2 eps
      exact ⟨N,fun n hn => (hN n hn).2⟩
  apply SeriesLimitLaws.small_closed a.val C (fun n => (2*(2*B)*C)*E n)
    (SeriesLimitLaws.shrinks_scale E hE _
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.mul_nonneg (by decide) hB)) hC))
  intro n
  let k := n+N
  let q := (z.val.compute k).center
  have hq := QBox.center_mem (valid_ordered z.property k)
  have hn : N≤k := by omega
  have hqs := latticeRegion_sample z R eta N k hregion hn q hq
  have hh : q.im≤H := Rat.le_trans hq.2.2
    (Rat.le_trans (valid_nestedIn z.property hn).2.2 hheight)
  have hb := rationalLattice_box_reciprocal_bounds q (u.x:Rat) (u.y:Rat) r R H eta
    hr hR hH heta hx hy hqs.1 ⟨hqs.2,hh⟩ hout
  have hgeom := latticeRegion_sample_outside_square z R eta N k
    hR heta hregion hn q hq (u.x:Rat) (u.y:Rat) r (Rat.le_of_lt hr) hout
  have hN : rationalLatticeNorm q (u.x:Rat) (u.y:Rat)≠0 := by
    intro he
    rw [he] at hgeom
    have hpos := Rat.mul_pos
      (Rat.mul_pos (Rat.mul_pos heta
        heta) hr) hr
    grind
  obtain ⟨hw,heq⟩ := rationalLatticeInverse_represented q (u.x:Rat) (u.y:Rat) hN
  let w : Scalar := ⟨ofQComplex ⟨(u.x:Rat)+(u.y:Rat)*q.re,(u.y:Rat)*q.im⟩,ofQComplex_valid _⟩
  let s := RepresentedReciprocal.inverse w hw
  have hs : Small s.val C := by
    apply Small.congr (ofQComplex_valid _) s.property (equiv_symm heq)
    exact ⟨fun _ _ => hb.1.1,fun _ _ => hb.1.2,fun _ _ => hb.2.1,fun _ _ => hb.2.2⟩
  have hEn : 0≤E n := Rat.add_nonneg (v.property.1 k).1 (v.property.1 k).2
  have hv : Small (sub v.val w.val) (E n) := by
    apply BoxApproximation.point_error v k _ (E n) hEn
    · simpa only [v,latticeVector,SL2Z.affine,QComplex.add,QComplex.scaleRat,
        Rat.add_zero,Rat.add_comm] using integerAffine_contains u.y u.x z.val k q hq
    · have hh := (v.property.1 k).2
      change (v.val.compute k).width≤(v.val.compute k).width+(v.val.compute k).height
      grind
    · have hh := (v.property.1 k).1
      change (v.val.compute k).height≤(v.val.compute k).width+(v.val.compute k).height
      grind
  have hrev : (neg (sub v.val w.val)).Equiv (sub w.val v.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid v.property w.property))
      (hright := sub_valid w.property v.property)
    change -(ComplexRawQuotient.ofRaw v.val v.property-ComplexRawQuotient.ofRaw w.val w.property) =
      ComplexRawQuotient.ofRaw w.val w.property-ComplexRawQuotient.ofRaw v.val v.property
    grind
  have hve := Small.congr (neg_valid (sub_valid v.property w.property))
    (sub_valid w.property v.property) hrev (SeriesLimitLaws.small_neg hv)
  have hd := representedReciprocal_difference_small v w
    (latticeVector_nonzero z hz u hu) hw B C (E n) hB hC hEn ha hs
    hve
  have hd' : Small (sub a.val s.val) ((2*(2*B)*C)*E n) := by
    have he : 2*(2*B*E n)*C = (2*(2*B)*C)*E n := by grind
    rw [← he]
    exact hd
  exact Small.congr (add_valid s.property (sub_valid a.property s.property)) a.property
    (SeriesLimitLaws.add_difference a.val s.val a.property s.property)
    (small_add hs hd')

theorem latticeInverse_region_radius_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (N : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta N) (hheight : (z.val.compute N).hi.im≤H)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) :
    Small (latticeInverse z hz u hu).val
      (latticeRegionReciprocalConstant R H eta/(QuadraticOrder163.shellRadius u:Rat)) := by
  have hb := QuadraticOrder163.shellRadius_bounds u
  have hr : 0<(QuadraticOrder163.shellRadius u:Rat) := by
    exact_mod_cast QuadraticOrder163.shellRadius_positive u hu
  have castBound {a b : Int} (h : a≤b) : (a:Rat)≤(b:Rat) :=
    Rat.intCast_le_intCast.mpr h
  have hx : -(QuadraticOrder163.shellRadius u:Rat)≤(u.x:Rat) ∧
      (u.x:Rat)≤(QuadraticOrder163.shellRadius u:Rat) := by
    constructor
    · simpa only [Rat.intCast_neg,Rat.intCast_natCast] using castBound hb.1
    · simpa only [Rat.intCast_natCast] using castBound hb.2.1
  have hy : -(QuadraticOrder163.shellRadius u:Rat)≤(u.y:Rat) ∧
      (u.y:Rat)≤(QuadraticOrder163.shellRadius u:Rat) := by
    constructor
    · simpa only [Rat.intCast_neg,Rat.intCast_natCast] using castBound hb.2.2.1
    · simpa only [Rat.intCast_natCast] using castBound hb.2.2.2.1
  have ho : (QuadraticOrder163.shellRadius u:Rat)≤(u.x:Rat) ∨
      (u.x:Rat)≤ -(QuadraticOrder163.shellRadius u:Rat) ∨
      (QuadraticOrder163.shellRadius u:Rat)≤(u.y:Rat) ∨
      (u.y:Rat)≤ -(QuadraticOrder163.shellRadius u:Rat) := by
    rcases hb.2.2.2.2 with h|h|h|h
    · have he := congrArg (fun j : Int => (j:Rat)) h
      simp only [Rat.intCast_natCast] at he
      exact Or.inl (he ▸ Rat.le_refl)
    · have he := congrArg (fun j : Int => (j:Rat)) h
      simp only [Rat.intCast_neg,Rat.intCast_natCast] at he
      exact Or.inr (Or.inl (he ▸ Rat.le_refl))
    · have he := congrArg (fun j : Int => (j:Rat)) h
      simp only [Rat.intCast_natCast] at he
      exact Or.inr (Or.inr (Or.inl (he ▸ Rat.le_refl)))
    · have he := congrArg (fun j : Int => (j:Rat)) h
      simp only [Rat.intCast_neg,Rat.intCast_natCast] at he
      exact Or.inr (Or.inr (Or.inr (he ▸ Rat.le_refl)))
  exact latticeInverse_region_square_bound z hz R H eta N hR hH heta hregion hheight u hu _ hr hx hy ho

end ComputableAnalysis.ModularForms
