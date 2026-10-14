import ComputableAnalysis.RiemannHilbert.DomainDerivativeBounds

/-! The complex chain rule for actual domain-dependent evaluations.
The output radius is computed from the supplied derivative radii and
first-box bounds, and the composition remainder is explicitly bounded. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def chainInnerError (eps : QPos) (df : Scalar) : QPos :=
  divideRadius eps ⟨4*(scalarBound df+1), by
    exact Rat.mul_pos (by decide +kernel) (by have h := scalarBound_pos df; grind)⟩

def chainOuterError (eps : QPos) (dg : Scalar) : QPos :=
  divideRadius eps ⟨2*(derivativeRate dg).val, Rat.mul_pos (by decide +kernel) (derivativeRate dg).property⟩

theorem chain_error_bound (eps : QPos) (df dg : Scalar) :
    (chainOuterError eps dg).val*(derivativeRate dg).val +
      2*scalarBound df*(chainInnerError eps df).val ≤ eps.val := by
  have h1 := divideRadius_identity eps
    ⟨4*(scalarBound df+1), Rat.mul_pos (by decide +kernel) (by have h := scalarBound_pos df; grind)⟩
  have h2 := divideRadius_identity eps
    ⟨2*(derivativeRate dg).val, Rat.mul_pos (by decide +kernel) (derivativeRate dg).property⟩
  have hp := (chainInnerError eps df).property
  change 4*(scalarBound df+1)*(chainInnerError eps df).val=eps.val at h1
  change 2*(derivativeRate dg).val*(chainOuterError eps dg).val=eps.val at h2
  grind

def composeDerivative (f g : Map) (a : Scalar) (ha : composeDomain f g a) (df dg : Scalar)
    (hf : HasDerivativeAt f (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha) df)
    (hg : HasDerivativeAt g a (compose_inner_mem ha) dg) :
    HasDerivativeAt (compose f g) a ha (scalarProduct df dg) where
  delta eps := minRadius (hg.delta unitError)
    (minRadius (hg.delta (chainInnerError eps df))
      (divideRadius (hf.delta (chainOuterError eps dg)) (derivativeRate dg)))
  estimate eps H z hz hH hza := by
    let L := derivativeRate dg
    let alpha := chainInnerError eps df
    let beta := chainOuterError eps dg
    have hHunit : H.val ≤ (hg.delta unitError).val := Rat.le_trans hH (minRadius_left _ _)
    have hHrest : H.val ≤
        (minRadius (hg.delta alpha) (divideRadius (hf.delta beta) L)).val :=
      Rat.le_trans hH (minRadius_right _ _)
    have hHinner : H.val ≤ (hg.delta alpha).val := Rat.le_trans hHrest (minRadius_left _ _)
    have hHouter : H.val ≤ (divideRadius (hf.delta beta) L).val :=
      Rat.le_trans hHrest (minRadius_right _ _)
    let J : QPos := ⟨L.val*H.val, Rat.mul_pos L.property H.property⟩
    have hJ : J.val ≤ (hf.delta beta).val := by
      have hm := Rat.mul_le_mul_of_nonneg_left hHouter (Rat.le_of_lt L.property)
      rw [divideRadius_identity] at hm
      exact hm
    have himage := hg.difference_bound H z (compose_inner_mem hz) hHunit hza
    have houter := hf.estimate beta J (g.eval z (compose_inner_mem hz)) (compose_outer_mem hz) hJ himage
    have hinner := hg.estimate alpha H z (compose_inner_mem hz) hHinner hza
    have hscaled := Small.mul df.property (remainder_valid _ _ _ _ _ _)
      (Rat.le_of_lt (scalarBound_pos df)) (Rat.mul_nonneg (Rat.le_of_lt alpha.property) (Rat.le_of_lt H.property))
      (scalar_small df) hinner
    have hs := LocalODE.small_add houter hscaled
    have he : beta.val*J.val+2*scalarBound df*(alpha.val*H.val) =
        (beta.val*L.val+2*scalarBound df*alpha.val)*H.val := by dsimp [J]; grind
    rw [he] at hs
    have hbound := Rat.mul_le_mul_of_nonneg_right (chain_error_bound eps df dg) (Rat.le_of_lt H.property)
    apply Small.congr
      (add_valid (remainder_valid _ _ _ _ _ _) (mul_valid df.property (remainder_valid _ _ _ _ _ _)))
      (remainder_valid _ _ _ _ _ _) (equiv_symm (compose_remainder f g a ha df dg z hz))
    exact hs.mono hbound

end ComputableAnalysis.RiemannHilbert.DomainFunctions
