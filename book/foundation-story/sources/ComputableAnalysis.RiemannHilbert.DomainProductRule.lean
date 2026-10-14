import ComputableAnalysis.RiemannHilbert.DomainHolomorphicComposition

/-! The product rule for actual domain-dependent scalar evaluations.
Both first-order remainders and the quadratic difference term are bounded
using executable rational radii. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def scalarSum (a b : Scalar) : Scalar := ⟨add a.val b.val, add_valid a.property b.property⟩

def productOn (f g : Map) (hfg : ∀ z, f.domain z → g.domain z) : Map where
  domain := f.domain
  eval z hz := scalarProduct (f.eval z hz) (g.eval z (hfg z hz))
  domain_congr := f.domain_congr
  eval_congr z w hz hw hzw := mul_equiv (f.eval z hz).property (f.eval w hw).property
    (g.eval z (hfg z hz)).property (g.eval w (hfg w hw)).property
    (f.eval_congr z w hz hw hzw) (g.eval_congr z w _ _ hzw)

def productSlope (fa ga df dg : Scalar) : Scalar :=
  scalarSum (scalarProduct df ga) (scalarProduct fa dg)

theorem product_remainder (f g : Map) (hfg : ∀ z, f.domain z → g.domain z)
    (a : Scalar) (ha : f.domain a) (df dg : Scalar) (z : Scalar) (hz : f.domain z) :
    (remainder (productOn f g hfg) a ha (productSlope (f.eval a ha) (g.eval a (hfg a ha)) df dg) z hz).Equiv
      (add (add (mul (remainder f a ha df z hz) (g.eval a (hfg a ha)).val)
        (mul (f.eval a ha).val (remainder g a (hfg a ha) dg z (hfg z hz))))
        (mul (sub (f.eval z hz).val (f.eval a ha).val)
          (sub (g.eval z (hfg z hz)).val (g.eval a (hfg a ha)).val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := remainder_valid _ _ _ _ _ _)
    (hright := add_valid (add_valid
      (mul_valid (remainder_valid _ _ _ _ _ _) (g.eval a (hfg a ha)).property)
      (mul_valid (f.eval a ha).property (remainder_valid _ _ _ _ _ _)))
      (mul_valid (sub_valid (f.eval z hz).property (f.eval a ha).property)
        (sub_valid (g.eval z (hfg z hz)).property (g.eval a (hfg a ha)).property)))
  let F := ComplexRawQuotient.ofRaw (f.eval a ha).val (f.eval a ha).property
  let G := ComplexRawQuotient.ofRaw (g.eval a (hfg a ha)).val (g.eval a (hfg a ha)).property
  let X := ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property
  let Y := ComplexRawQuotient.ofRaw (g.eval z (hfg z hz)).val (g.eval z (hfg z hz)).property
  let D := ComplexRawQuotient.ofRaw df.val df.property
  let E := ComplexRawQuotient.ofRaw dg.val dg.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change (X*Y + -(F*G)) + -((D*G+F*E)*(Z + -A)) =
    (((X + -F) + -(D*(Z + -A)))*G + F*((Y + -G) + -(E*(Z + -A)))) +
      (X + -F)*(Y + -G)
  grind

def halfError (eps : QPos) : QPos := divideRadius eps ⟨2, by decide +kernel⟩

theorem halfError_identity (eps : QPos) : 2*(halfError eps).val=eps.val :=
  divideRadius_identity eps ⟨2, by decide +kernel⟩

def productCross (df dg : Scalar) : QPos :=
  ⟨2*(derivativeRate df).val*(derivativeRate dg).val,
    Rat.mul_pos (Rat.mul_pos (by decide +kernel) (derivativeRate df).property) (derivativeRate dg).property⟩

def crossRadius (eps : QPos) (df dg : Scalar) : QPos :=
  divideRadius (halfError eps) (productCross df dg)

theorem product_linear_error (eps : QPos) (fa ga : Scalar) :
    2*(productLeftError (halfError eps) ga).val*scalarBound ga +
      2*scalarBound fa*(productRightError (halfError eps) fa).val ≤ (halfError eps).val := by
  have h := product_error_bound (halfError eps) fa ga
  have hα := (productLeftError (halfError eps) ga).property
  grind

def productDerivative (f g : Map) (hfg : ∀ z, f.domain z → g.domain z)
    (a : Scalar) (ha : f.domain a) (df dg : Scalar)
    (hf : HasDerivativeAt f a ha df) (hg : HasDerivativeAt g a (hfg a ha) dg) :
    HasDerivativeAt (productOn f g hfg) a ha (productSlope (f.eval a ha) (g.eval a (hfg a ha)) df dg) where
  delta eps := minRadius (hf.delta unitError) (minRadius (hg.delta unitError)
    (minRadius (hf.delta (productLeftError (halfError eps) (g.eval a (hfg a ha))))
      (minRadius (hg.delta (productRightError (halfError eps) (f.eval a ha))) (crossRadius eps df dg))))
  estimate eps H z hz hH hza := by
    let alpha := productLeftError (halfError eps) (g.eval a (hfg a ha))
    let beta := productRightError (halfError eps) (f.eval a ha)
    have hFunit := Rat.le_trans hH (minRadius_left _ _)
    have hrest1 := Rat.le_trans hH (minRadius_right _ _)
    have hGunit := Rat.le_trans hrest1 (minRadius_left _ _)
    have hrest2 := Rat.le_trans hrest1 (minRadius_right _ _)
    have hFalpha := Rat.le_trans hrest2 (minRadius_left _ _)
    have hrest3 := Rat.le_trans hrest2 (minRadius_right _ _)
    have hGbeta := Rat.le_trans hrest3 (minRadius_left _ _)
    have hCross := Rat.le_trans hrest3 (minRadius_right _ _)
    have hF := hf.estimate alpha H z hz hFalpha hza
    have hG := hg.estimate beta H z (hfg z hz) hGbeta hza
    have hDF := hf.difference_bound H z hz hFunit hza
    have hDG := hg.difference_bound H z (hfg z hz) hGunit hza
    have hleft := Small.mul (remainder_valid _ _ _ _ _ _) (g.eval a (hfg a ha)).property
      (Rat.mul_nonneg (Rat.le_of_lt alpha.property) (Rat.le_of_lt H.property))
      (Rat.le_of_lt (scalarBound_pos _)) hF (scalar_small _)
    have hright := Small.mul (f.eval a ha).property (remainder_valid _ _ _ _ _ _)
      (Rat.le_of_lt (scalarBound_pos _))
      (Rat.mul_nonneg (Rat.le_of_lt beta.property) (Rat.le_of_lt H.property)) (scalar_small _) hG
    have hquadratic := Small.mul (sub_valid (f.eval z hz).property (f.eval a ha).property)
      (sub_valid (g.eval z (hfg z hz)).property (g.eval a (hfg a ha)).property)
      (Rat.mul_nonneg (Rat.le_of_lt (derivativeRate df).property) (Rat.le_of_lt H.property))
      (Rat.mul_nonneg (Rat.le_of_lt (derivativeRate dg).property) (Rat.le_of_lt H.property)) hDF hDG
    have hs := LocalODE.small_add (LocalODE.small_add hleft hright) hquadratic
    have hlin := Rat.mul_le_mul_of_nonneg_right
      (product_linear_error eps (f.eval a ha) (g.eval a (hfg a ha))) (Rat.le_of_lt H.property)
    have hcross := Rat.mul_le_mul_of_nonneg_left hCross (Rat.le_of_lt (productCross df dg).property)
    unfold crossRadius at hcross
    rw [divideRadius_identity] at hcross
    have hquad := Rat.mul_le_mul_of_nonneg_right hcross (Rat.le_of_lt H.property)
    have hhalf := halfError_identity eps
    have hbound :
        (2*(alpha.val*H.val)*scalarBound (g.eval a (hfg a ha)) +
          2*scalarBound (f.eval a ha)*(beta.val*H.val)) +
          2*((derivativeRate df).val*H.val)*((derivativeRate dg).val*H.val) ≤ eps.val*H.val := by
      change (2*alpha.val*scalarBound (g.eval a (hfg a ha)) +
        2*scalarBound (f.eval a ha)*beta.val)*H.val ≤ (halfError eps).val*H.val at hlin
      change (2*(derivativeRate df).val*(derivativeRate dg).val*H.val)*H.val ≤
        (halfError eps).val*H.val at hquad
      calc
        _ = (2*alpha.val*scalarBound (g.eval a (hfg a ha)) +
          2*scalarBound (f.eval a ha)*beta.val)*H.val +
            2*(derivativeRate df).val*(derivativeRate dg).val*H.val*H.val := by grind only
        _ ≤ (halfError eps).val*H.val + (halfError eps).val*H.val := by grind only
        _ = eps.val*H.val := by grind only
    exact Small.congr
      (add_valid (add_valid
        (mul_valid (remainder_valid _ _ _ _ _ _) (g.eval a (hfg a ha)).property)
        (mul_valid (f.eval a ha).property (remainder_valid _ _ _ _ _ _)))
        (mul_valid (sub_valid (f.eval z hz).property (f.eval a ha).property)
          (sub_valid (g.eval z (hfg z hz)).property (g.eval a (hfg a ha)).property)))
      (remainder_valid _ _ _ _ _ _) (equiv_symm (product_remainder f g hfg a ha df dg z hz)) (hs.mono hbound)

end ComputableAnalysis.RiemannHilbert.DomainFunctions
