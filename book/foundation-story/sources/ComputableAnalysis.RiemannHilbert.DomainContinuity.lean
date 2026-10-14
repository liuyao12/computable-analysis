import ComputableAnalysis.RiemannHilbert.DomainChainRule

/-! Quantitative continuity under restriction, composition and scalar
products. All local bounds come from valid represented values. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def restrictContinuous {D E : Scalar → Prop} (g : ∀ z, D z → Scalar)
    (h : ContinuousOn D g) (hED : ∀ z, E z → D z) :
    ContinuousOn E (fun z hz => g z (hED z hz)) where
  delta a ha := h.delta a (hED a ha)
  estimate a ha eps z hz hza := h.estimate a (hED a ha) eps z (hED z hz) hza

def composeContinuous (f g : Map) (F : ∀ z, f.domain z → Scalar)
    (hf : ContinuousOn f.domain F) (hg : ContinuousOn g.domain g.eval) :
    ContinuousOn (composeDomain f g)
      (fun z hz => F (g.eval z (compose_inner_mem hz)) (compose_outer_mem hz)) where
  delta a ha eps := hg.delta a (compose_inner_mem ha)
    (hf.delta (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha) eps)
  estimate a ha eps z hz hza :=
    hf.estimate _ (compose_outer_mem ha) eps _ (compose_outer_mem hz)
      (hg.estimate a (compose_inner_mem ha) _ z (compose_inner_mem hz) hza)

theorem scalarProduct_difference (a b c d : Scalar) :
    (sub (scalarProduct a b).val (scalarProduct c d).val).Equiv
      (add (mul (sub a.val c.val) b.val) (mul c.val (sub b.val d.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scalarProduct a b).property (scalarProduct c d).property)
    (hright := add_valid (mul_valid (sub_valid a.property c.property) b.property)
      (mul_valid c.property (sub_valid b.property d.property)))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  change A*B + -(C*D) = (A + -C)*B + C*(B + -D)
  grind

def productLeftError (eps : QPos) (g : Scalar) : QPos :=
  divideRadius eps ⟨4*(scalarBound g+2), by
    exact Rat.mul_pos (by decide +kernel) (by have h := scalarBound_pos g; grind)⟩

def productRightError (eps : QPos) (f : Scalar) : QPos :=
  divideRadius eps ⟨4*(scalarBound f+1), by
    exact Rat.mul_pos (by decide +kernel) (by have h := scalarBound_pos f; grind)⟩

theorem product_error_bound (eps : QPos) (f g : Scalar) :
    2*(productLeftError eps g).val*(scalarBound g+1)+
      2*scalarBound f*(productRightError eps f).val ≤ eps.val := by
  have h1 := divideRadius_identity eps
    ⟨4*(scalarBound g+2), Rat.mul_pos (by decide +kernel) (by have h := scalarBound_pos g; grind)⟩
  have h2 := divideRadius_identity eps
    ⟨4*(scalarBound f+1), Rat.mul_pos (by decide +kernel) (by have h := scalarBound_pos f; grind)⟩
  have hp1 := (productLeftError eps g).property
  have hp2 := (productRightError eps f).property
  change 4*(scalarBound g+2)*(productLeftError eps g).val=eps.val at h1
  change 4*(scalarBound f+1)*(productRightError eps f).val=eps.val at h2
  grind

def productContinuous {D : Scalar → Prop} (f g : ∀ z, D z → Scalar)
    (hf : ContinuousOn D f) (hg : ContinuousOn D g) :
    ContinuousOn D (fun z hz => scalarProduct (f z hz) (g z hz)) where
  delta a ha eps := minRadius (hg.delta a ha unitError)
    (minRadius (hf.delta a ha (productLeftError eps (g a ha)))
      (hg.delta a ha (productRightError eps (f a ha))))
  estimate a ha eps z hz hza := by
    let alpha := productLeftError eps (g a ha)
    let beta := productRightError eps (f a ha)
    have h1 := hg.estimate a ha unitError z hz (hza.mono (minRadius_left _ _))
    have hrest := hza.mono (minRadius_right (hg.delta a ha unitError)
      (minRadius (hf.delta a ha alpha) (hg.delta a ha beta)))
    have hF := hf.estimate a ha alpha z hz (hrest.mono (minRadius_left _ _))
    have hG := hg.estimate a ha beta z hz (hrest.mono (minRadius_right _ _))
    have hsum := LocalODE.small_add (scalar_small (g a ha)) h1
    have hgz : Small (g z hz).val (scalarBound (g a ha)+1) := Small.congr
      (add_valid (g a ha).property (sub_valid (g z hz).property (g a ha).property)) (g z hz).property
      (SeriesLimitLaws.add_difference (g z hz).val (g a ha).val (g z hz).property (g a ha).property) hsum
    have hleft := Small.mul (sub_valid (f z hz).property (f a ha).property) (g z hz).property
      (Rat.le_of_lt alpha.property) (by have h := scalarBound_pos (g a ha); grind) hF hgz
    have hright := Small.mul (f a ha).property (sub_valid (g z hz).property (g a ha).property)
      (Rat.le_of_lt (scalarBound_pos _)) (Rat.le_of_lt beta.property) (scalar_small _) hG
    have hs := LocalODE.small_add hleft hright
    apply Small.congr
      (add_valid (mul_valid (sub_valid (f z hz).property (f a ha).property) (g z hz).property)
        (mul_valid (f a ha).property (sub_valid (g z hz).property (g a ha).property)))
      (sub_valid (scalarProduct (f z hz) (g z hz)).property (scalarProduct (f a ha) (g a ha)).property)
      (equiv_symm (scalarProduct_difference _ _ _ _))
    exact hs.mono (product_error_bound eps (f a ha) (g a ha))

end ComputableAnalysis.RiemannHilbert.DomainFunctions
