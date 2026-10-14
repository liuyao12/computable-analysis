import ComputableAnalysis.ModularForms.SquareContourVanishing
import ComputableAnalysis.ModularForms.DomainSegmentBisection

/-! Local uniqueness for an actual homogeneous scalar equation by rational contraction. -/
namespace ComputableAnalysis.ModularForms.HomogeneousLocalUniqueness
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 2000000

def Neighborhood (a : Scalar) (R : QPos) (z : Scalar) : Prop := Small (sub z.val a.val) R.val

theorem origin (a : Scalar) (R : QPos) : Neighborhood a R a := by
  exact Small.congr (ofQComplex_valid _) (sub_valid a.property a.property)
    (by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ofQComplex_valid _) (hright := sub_valid a.property a.property)
      let A := gridScalarValue a
      change (0:ScalarAlgebra.Value)=A-A
      grind only)
    (Small.zero (Rat.le_of_lt R.property))

theorem segment (a : Scalar) (R : QPos) (z : Scalar) (hz : Neighborhood a R z)
    (t : UnitInterval.Point) : Neighborhood a R (RepresentedAffineSegment.point a z t) :=
  RepresentedAffineSegment.offset_bound a a z t _ (origin a R) hz

variable (f : DomainFunctions.Map) (hf : Holomorphic f) (a : Scalar) (ha : f.domain a)
  (R : QPos) (hmem : ∀ z, Neighborhood a R z → f.domain z)
  (A : ∀ z, f.domain z → Scalar) (P : Rat) (hP : 0<P)
  (hshort : 8*P*R.val≤(1:Rat)/2)
  (hA : ∀ z hz, Small (A z (hmem z hz)).val P)
  (heq : ∀ z hz, (hf.derivative z hz).val.Equiv (mul (A z hz).val (f.eval z hz).val))
  (hzero : (f.eval a ha).val.Equiv zero)

include hf ha A P hP hshort hA heq hzero in
theorem contract (B : Rat) (hB : 0<B)
    (hb : ∀ z hz, Small (f.eval z (hmem z hz)).val B)
    (z : Scalar) (hz : Neighborhood a R z) :
    Small (f.eval z (hmem z hz)).val (B/2) := by
  let W := R
  let eps : QPos := ⟨2*P*B,Rat.mul_pos (Rat.mul_pos (by decide +kernel) hP) hB⟩
  let hdom := fun t => hmem _ (segment a R z hz t)
  have hder (t : UnitInterval.Point) :
      Small (sub (hf.derivative
        (RepresentedAffineSegment.point a z t) (hdom t)).val zero) eps.val := by
    let w := RepresentedAffineSegment.point a z t
    let hw := segment a R z hz t
    have hc := hA w hw
    have hm := Small.mul (A w (hdom t)).property
      (f.eval w (hdom t)).property (Rat.le_of_lt hP)
      (Rat.le_of_lt hB) hc (hb w hw)
    have hd := Small.congr
      (mul_valid (A w (hdom t)).property
        (f.eval w (hdom t)).property)
      (hf.derivative w (hdom t)).property
      (equiv_symm (heq w (hdom t))) hm
    have hs := SeriesLimitLaws.small_sub hd (Small.zero (by decide +kernel : (0:Rat)≤0))
    simpa only [Rat.add_zero] using hs
  have hr := domainSegment_remainder_bound f
    hf a z ⟨zero,ofQComplex_valid _⟩
    ha (hmem z hz) W eps hdom hz hder
  have he : (DomainFunctions.remainder f a
      ha ⟨zero,ofQComplex_valid _⟩ z (hmem z hz)).Equiv
      (f.eval z (hmem z hz)).val := by
    have h0 := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (f.eval a ha).property) (hright := ofQComplex_valid _) hzero
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _)
      (hright := (f.eval z (hmem z hz)).property)
    let F := gridScalarValue (f.eval z (hmem z hz))
    let Z := gridScalarValue (f.eval a ha)
    let X := gridScalarValue z
    let C := gridScalarValue a
    change Z=0 at h0
    change (F-Z)-0*(X-C)=F
    rw [h0]
    grind only
  have hs := Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (f.eval z (hmem z hz)).property he hr
  apply hs.mono
  have hm := Rat.mul_le_mul_of_nonneg_left hshort (Rat.le_of_lt hB)
  dsimp [eps]
  grind only

include hf ha A P hP hshort hA heq hzero in
theorem geometric_bound (B : QPos)
    (hb : ∀ z hz, Small (f.eval z (hmem z hz)).val B.val) (n : Nat) :
    ∀ z hz, Small (f.eval z (hmem z hz)).val (B.val*((1:Rat)/2)^n) := by
  induction n with
  | zero => intro z hz; simpa only [Rat.pow_zero,Rat.mul_one] using hb z hz
  | succ n ih =>
    intro z hz
    have hs := contract f hf a ha R hmem A P hP hshort hA heq hzero _
      (Rat.mul_pos B.property (Rat.pow_pos (by decide +kernel))) ih z hz
    have he : (B.val*((1:Rat)/2)^n)/2=B.val*((1:Rat)/2)^(n+1) := by
      rw [Rat.pow_succ,Rat.div_def]
      have hc : (2:Rat)⁻¹=(1:Rat)/2 := by decide +kernel
      rw [hc]
      grind only
    rw [he] at hs
    exact hs

include hf ha A P hP hshort hA heq hzero in
/-- A complete conditional uniqueness law for supplied actual holomorphic solutions.
The neighborhood, coefficient and initial bounds are genuine quantitative evidence. -/
theorem zero_on (B : QPos)
    (hb : ∀ z hz, Small (f.eval z (hmem z hz)).val B.val)
    (z : Scalar) (hz : Neighborhood a R z) : (f.eval z (hmem z hz)).val.Equiv zero := by
  have hbound : Small (f.eval z (hmem z hz)).val 0 := by
    apply SeriesLimitLaws.small_closed _ 0 (fun n => B.val*((1:Rat)/2)^n)
      (ComputableAnalysis.ModularForms.rational_half_geometric_shrinks B.val (Rat.le_of_lt B.property))
    intro n
    simpa only [Rat.zero_add] using geometric_bound f hf a ha R hmem A P hP hshort hA heq hzero B hb n z hz
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  have hs := SeriesLimitLaws.small_sub hbound (Small.zero (by decide +kernel : (0:Rat)≤0))
  simpa only [Rat.zero_add] using hs

end ComputableAnalysis.ModularForms.HomogeneousLocalUniqueness
