import ComputableAnalysis.RiemannHilbert.RelativeLogarithmScaling
import ComputableAnalysis.RiemannHilbert.ScalarTopology

/-! Executable rational changes of scale on arbitrary represented complex
inputs. Exact inverse, displacement, chart and open-neighborhood laws justify
local coordinate normalization without changing the represented scalar base. -/
namespace ComputableAnalysis.RiemannHilbert.RationalDilation
open ComplexRaw FunctionTheory LocalODE DomainFunctions NonzeroBoxSearch
open RadialLogarithmChains
set_option autoImplicit false

def unit (r : Rat) : Scalar := scale r DomainFunctions.oneScalar

theorem product (r : Rat) (z : Scalar) : scalarProduct (unit r) z≈scale r z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarProduct (unit r) z).property) (hright := (scale r z).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change ComplexRawQuotient.scaleRat r 1*Z=ComplexRawQuotient.scaleRat r Z
  exact (ComplexRawQuotient.scaleRat_mul r 1 Z).symm.trans
    (congrArg (ComplexRawQuotient.scaleRat r) (ComplexRawQuotient.one_mul Z))

theorem names (r : Rat) (z w : Scalar) (he : z≈w) : scale r z≈scale r w := scaleRat_equiv he

theorem undo (r : Rat) (hr : 0<r) (z : Scalar) : scale r⁻¹ (scale r z)≈z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scale r⁻¹ (scale r z)).property) (hright := z.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change ComplexRawQuotient.scaleRat r⁻¹ (ComplexRawQuotient.scaleRat r Z)=Z
  rw [ComplexRawQuotient.scaleRat_scaleRat,Rat.inv_mul_cancel r (Rat.ne_of_gt hr),ComplexRawQuotient.scaleRat_one]

theorem undo_right (r : Rat) (hr : 0<r) (z : Scalar) : scale r (scale r⁻¹ z)≈z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scale r (scale r⁻¹ z)).property) (hright := z.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change ComplexRawQuotient.scaleRat r (ComplexRawQuotient.scaleRat r⁻¹ Z)=Z
  rw [ComplexRawQuotient.scaleRat_scaleRat,Rat.mul_inv_cancel r (Rat.ne_of_gt hr),ComplexRawQuotient.scaleRat_one]

private theorem scale_neg (r : Rat) (Z : ComplexRawQuotient.Value) :
    ComplexRawQuotient.scaleRat r (-Z)= -(ComplexRawQuotient.scaleRat r Z) := by
  rw [ComplexRawQuotient.neg_eq_scaleRat_neg_one Z,ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.neg_scaleRat]
  congr 1
  grind only

theorem difference (r : Rat) (z w : Scalar) :
    (sub (scale r z).val (scale r w).val).Equiv (scaleRat r (sub z.val w.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scale r z).property (scale r w).property)
    (hright := scaleRat_valid (sub_valid z.property w.property))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  change ComplexRawQuotient.scaleRat r Z+ -(ComplexRawQuotient.scaleRat r W)=ComplexRawQuotient.scaleRat r (Z+ -W)
  rw [ComplexRawQuotient.scaleRat_add,scale_neg]

theorem displacement_bound (r : Rat) (hr : 0≤r) (z w : Scalar) (H : Rat)
    (hH : Small (sub z.val w.val) H) : Small (sub (scale r z).val (scale r w).val) (r*H) :=
  Small.congr (scaleRat_valid (sub_valid z.property w.property))
    (sub_valid (scale r z).property (scale r w).property) (equiv_symm (difference r z w)) (small_scale hr hH)

theorem interior_scale (r : Rat) (hr : 0<r) (R : Rat) (z : Scalar) (hz : interior R z) :
    interior (r*R) (scale r z) := by
  rcases hz with ⟨S,hS,hSR,hs⟩
  exact ⟨r*S,Rat.mul_nonneg (Rat.le_of_lt hr) hS,
    Rat.mul_lt_mul_of_pos_left hSR hr,small_scale (Rat.le_of_lt hr) hs⟩

theorem interior_unscale (r : Rat) (hr : 0<r) (R : Rat) (z : Scalar)
    (hz : interior (r*R) z) : interior R (scale r⁻¹ z) := by
  have h := interior_scale r⁻¹ (Rat.inv_pos.mpr hr) (r*R) z hz
  have he : r⁻¹*(r*R)=R := by rw [← Rat.mul_assoc,Rat.inv_mul_cancel r (Rat.ne_of_gt hr),Rat.one_mul]
  rw [he] at h
  exact h

def function (r : Rat) : DomainFunctions.Map where
  domain _ := True
  eval z _ := scale r z
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ he := names r z w he

def holomorphic (r : Rat) : Holomorphic (function r) :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ (unit r)).transfer (function r)
    (fun _ _ => trivial) ⟨fun _ _ => unitError,fun _ _ _ _ => trivial⟩
    (fun z _ => equiv_trans (scalarSum ⟨zero,ofQComplex_valid _⟩ (scalarProduct (unit r) z)).property
      (scalarProduct (unit r) z).property (scale r z).property
      (zero_add_equiv _ (scalarProduct (unit r) z).property) (product r z))

def interiorData (R : Rat) : ScalarTopology.OpenData (interior R) where
  invariant z w he := ⟨fun hz => Centered.interior_congr R z w he hz,
    fun hw => Centered.interior_congr R w z (equiv_symm he) hw⟩
  radius := interiorRadius R
  inside := interiorRadius_inside R

end ComputableAnalysis.RiemannHilbert.RationalDilation
