import ComputableAnalysis.RiemannHilbert.DomainComposition
import ComputableAnalysis.RiemannHilbert.EffectiveNeighborhood

/-! Local continuity and a coordinate Lipschitz bound are derived from a
supplied derivative remainder, with executable rational radii. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def scalarBound (d : Scalar) : Rat := LocalODE.boxCoordinateBound (d.val.compute 0)+1

theorem scalarBound_pos (d : Scalar) : 0 < scalarBound d := by
  have h := LocalODE.boxCoordinateBound_nonneg (d.val.compute 0)
  unfold scalarBound
  grind

theorem scalar_small (d : Scalar) : Small d.val (scalarBound d) :=
  (LocalODE.small_from_box d.val d.property 0).mono (by unfold scalarBound; grind)

def derivativeRate (d : Scalar) : QPos :=
  ⟨2*scalarBound d+1, by have h := scalarBound_pos d; grind⟩

def divideRadius (eps : QPos) (C : QPos) : QPos :=
  ⟨eps.val/C.val, by rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 C.property)⟩

theorem divideRadius_identity (eps C : QPos) : C.val*(divideRadius eps C).val=eps.val := by
  change C.val*(eps.val/C.val)=eps.val
  rw [Rat.div_def]
  have h := Rat.mul_inv_cancel C.val (Rat.ne_of_gt C.property)
  grind

def minRadius (r s : QPos) : QPos :=
  ⟨min r.val s.val, by have h1 := r.property; have h2 := s.property; grind⟩

theorem minRadius_left (r s : QPos) : (minRadius r s).val ≤ r.val := by unfold minRadius; grind

theorem minRadius_right (r s : QPos) : (minRadius r s).val ≤ s.val := by unfold minRadius; grind

def unitError : QPos := ⟨1, by decide +kernel⟩

theorem difference_remainder (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar)
    (z : Scalar) (hz : f.domain z) :
    (sub (f.eval z hz).val (f.eval a ha).val).Equiv
      (add (mul d.val (sub z.val a.val)) (remainder f a ha d z hz)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (f.eval z hz).property (f.eval a ha).property)
    (hright := add_valid (mul_valid d.property (sub_valid z.property a.property)) (remainder_valid _ _ _ _ _ _))
  let X := ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property
  let Y := ComplexRawQuotient.ofRaw (f.eval a ha).val (f.eval a ha).property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change X + -Y = D*(Z + -A) + ((X + -Y) + -(D*(Z + -A)))
  grind

theorem HasDerivativeAt.difference_bound {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasDerivativeAt f a ha d) (H : QPos) (z : Scalar) (hz : f.domain z)
    (hH : H.val ≤ (h.delta unitError).val) (hza : Small (sub z.val a.val) H.val) :
    Small (sub (f.eval z hz).val (f.eval a ha).val) ((derivativeRate d).val*H.val) := by
  have hr := h.estimate unitError H z hz hH hza
  have hd := Small.mul d.property (sub_valid z.property a.property)
    (Rat.le_of_lt (scalarBound_pos d)) (Rat.le_of_lt H.property) (scalar_small d) hza
  have hs := LocalODE.small_add hd hr
  have he : 2*scalarBound d*H.val+unitError.val*H.val=(derivativeRate d).val*H.val := by
    unfold unitError derivativeRate
    grind
  rw [he] at hs
  exact Small.congr (add_valid (mul_valid d.property (sub_valid z.property a.property)) (remainder_valid _ _ _ _ _ _))
    (sub_valid (f.eval z hz).property (f.eval a ha).property)
    (equiv_symm (difference_remainder f a ha d z hz)) hs

structure ContinuousAt (f : Map) (a : Scalar) (ha : f.domain a) where
  delta : QPos → QPos
  estimate : ∀ (eps : QPos) z hz, Small (sub z.val a.val) (delta eps).val →
    Small (sub (f.eval z hz).val (f.eval a ha).val) eps.val

def HasDerivativeAt.continuousAt {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasDerivativeAt f a ha d) : ContinuousAt f a ha where
  delta eps := minRadius (h.delta unitError) (divideRadius eps (derivativeRate d))
  estimate eps z hz hza := by
    let H := minRadius (h.delta unitError) (divideRadius eps (derivativeRate d))
    have hs := h.difference_bound H z hz (minRadius_left _ _) hza
    have hm := Rat.mul_le_mul_of_nonneg_left (minRadius_right (h.delta unitError) (divideRadius eps (derivativeRate d)))
      (Rat.le_of_lt (derivativeRate d).property)
    rw [divideRadius_identity] at hm
    exact hs.mono hm

def continuousOn_of_derivative (f : Map) (df : ∀ a, f.domain a → Scalar)
    (h : ∀ a ha, HasDerivativeAt f a ha (df a ha)) : ContinuousOn f.domain f.eval where
  delta a ha := (h a ha).continuousAt.delta
  estimate a ha := (h a ha).continuousAt.estimate

end ComputableAnalysis.RiemannHilbert.DomainFunctions
