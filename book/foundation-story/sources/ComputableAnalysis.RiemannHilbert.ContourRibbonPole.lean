import ComputableAnalysis.RiemannHilbert.ContourRibbonDeformation
import ComputableAnalysis.RiemannHilbert.ContourCauchyKernel

/-! A represented pole strictly inside the inner rectangle is excluded from
the entire ribbon. Actual shifted reciprocals and Cauchy kernels deform. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem representedRectangle_congr (J : QInterval × QInterval) (z w : Scalar) (he : z≈w)
    (hz : representedRectangleContains J z) : representedRectangleContains J w := by
  have hr := realPart_equiv he
  have hi := imagPart_equiv he
  have hrv := realPart_valid z.property
  have hwv := realPart_valid w.property
  have hiv := imagPart_valid z.property
  have hwi := imagPart_valid w.property
  exact ⟨RealRaw.le_trans hrv hz.1 (RealRaw.le_of_equiv hrv hwv hr),
    RealRaw.le_trans hrv (RealRaw.le_of_equiv hwv hrv (RealRaw.equiv_symm hr)) hz.2.1,
    RealRaw.le_trans hiv hz.2.2.1 (RealRaw.le_of_equiv hiv hwi hi),
    RealRaw.le_trans hiv (RealRaw.le_of_equiv hwi hiv (RealRaw.equiv_symm hi)) hz.2.2.2⟩

theorem ribbonContains_congr (G : RectangleRibbon) (z w : Scalar) (he : z≈w)
    (hz : ribbonContains G z) : ribbonContains G w := by
  rcases hz with hL | hR | hB | hT
  · exact Or.inl (representedRectangle_congr _ z w he hL)
  · exact Or.inr (Or.inl (representedRectangle_congr _ z w he hR))
  · exact Or.inr (Or.inr (Or.inl (representedRectangle_congr _ z w he hB)))
  · exact Or.inr (Or.inr (Or.inr (representedRectangle_congr _ z w he hT)))

def RibbonPoleInterior (G : RectangleRibbon) (b : Scalar) : Prop :=
  ∃ R : QPos, representedRectangleContains
    (⟨G.inner.1.lo+R.val,G.inner.1.hi-R.val⟩,⟨G.inner.2.lo+R.val,G.inner.2.hi-R.val⟩) b

theorem ribbonPoleInterior_excludes (G : RectangleRibbon) (b : Scalar) (hb : RibbonPoleInterior G b) :
    ¬ribbonContains G b := by
  obtain ⟨R,hb⟩ := hb
  intro h
  rcases h with hL | hR | hB | hT
  · have he := RealRaw.le_trans (realPart_valid b.property) hb.1 hL.2.1
    have h := he 0 0
    change G.inner.1.lo+R.val≤G.inner.1.lo at h
    have hp := R.property
    grind only
  · have he := RealRaw.le_trans (realPart_valid b.property) hR.1 hb.2.1
    have h := he 0 0
    change G.inner.1.hi≤G.inner.1.hi-R.val at h
    have hp := R.property
    grind only
  · have he := RealRaw.le_trans (imagPart_valid b.property) hb.2.2.1 hB.2.2.2
    have h := he 0 0
    change G.inner.2.lo+R.val≤G.inner.2.lo at h
    have hp := R.property
    grind only
  · have he := RealRaw.le_trans (imagPart_valid b.property) hT.2.2.1 hb.2.2.2
    have h := he 0 0
    change G.inner.2.hi≤G.inner.2.hi-R.val at h
    have hp := R.property
    grind only

def ribbonPoleOffset (b : Scalar) : DomainFunctions.Map :=
  DomainFunctions.affine ⟨neg b.val,neg_valid b.property⟩ oneScalar

theorem ribbonPoleOffset_agreement (b z : Scalar) :
    (ribbonPoleOffset b).eval z trivial ≈ Centered.offset b z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((ribbonPoleOffset b).eval z trivial).property)
    (hright := (Centered.offset b z).property)
  let B := gridScalarValue b
  let Z := gridScalarValue z
  change -B+1*Z=Z-B
  grind only

theorem ribbonPoleOffset_nonzero (G : RectangleRibbon) (b z : Scalar)
    (hb : RibbonPoleInterior G b) (hz : ribbonContains G z) :
    NonzeroBoxSearch.Nonzero ((ribbonPoleOffset b).eval z trivial) := by
  intro he
  have h0 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((ribbonPoleOffset b).eval z trivial).property) (hright := (ofQComplex_valid _)) he
  let B := gridScalarValue b
  let Z := gridScalarValue z
  change -B+1*Z=0 at h0
  have hezb : z≈b := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property) (hright := b.property)
    change Z=B
    grind only
  exact ribbonPoleInterior_excludes G b hb (ribbonContains_congr G z b hezb hz)

def ribbonPoleReciprocal (b : Scalar) : DomainFunctions.Map :=
  compose ReciprocalHolomorphic.function (ribbonPoleOffset b)

def ribbonPoleReciprocal_holomorphic (b : Scalar) : Holomorphic (ribbonPoleReciprocal b) :=
  ReciprocalHolomorphic.holomorphic.compose (DomainFunctions.affine_holomorphic _ oneScalar)

theorem ribbonPoleReciprocal_value (b z : Scalar) (hz : (ribbonPoleReciprocal b).domain z)
    (hn : NonzeroBoxSearch.Nonzero (Centered.offset b z)) :
    (ribbonPoleReciprocal b).eval z hz ≈ RepresentedReciprocal.inverse (Centered.offset b z) hn :=
  RepresentedReciprocal.inverse_congr _ _ (compose_outer_mem hz) hn (ribbonPoleOffset_agreement b z)

def ribbonPoleReciprocal_domain (G : RectangleRibbon) (b : Scalar) (hb : RibbonPoleInterior G b) :
    RibbonDomain (ribbonPoleReciprocal b) G :=
  fun z hz => ⟨trivial,ribbonPoleOffset_nonzero G b z hb hz⟩

theorem ribbonPoleReciprocal_deformation (G : RectangleRibbon) (b : Scalar) (hb : RibbonPoleInterior G b) :
    Converges (ribbonDifference (ribbonPoleReciprocal b) G (ribbonPoleReciprocal_domain G b hb))
      (rationalRectangleScalar QComplex.zero) :=
  ribbonDifference_converges_zero _ (ribbonPoleReciprocal_holomorphic b) G (ribbonPoleReciprocal_domain G b hb)

def ribbonKernelNumerator (f : DomainFunctions.Map) (b : Scalar) : DomainFunctions.Map :=
  onDomain f (intersectionSum f (ribbonPoleReciprocal b)).domain_congr (fun _ hz => hz.1)

def ribbonCauchyKernel (f : DomainFunctions.Map) (b : Scalar) : DomainFunctions.Map :=
  productOn (ribbonKernelNumerator f b) (ribbonPoleReciprocal b) (fun _ hz => hz.2)

def ribbonCauchyKernel_holomorphic (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) :
    Holomorphic (ribbonCauchyKernel f b) :=
  (hf.onDomain (intersectionOpenData hf (ribbonPoleReciprocal_holomorphic b)) (fun _ hz => hz.1)).productOn
    (ribbonPoleReciprocal_holomorphic b) (fun _ hz => hz.2)

def ribbonCauchyKernel_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G)
    (b : Scalar) (hb : RibbonPoleInterior G b) : RibbonDomain (ribbonCauchyKernel f b) G :=
  fun z hz => ⟨hd z hz,ribbonPoleReciprocal_domain G b hb z hz⟩

theorem ribbonCauchyKernel_value (f : DomainFunctions.Map) (b z : Scalar)
    (hz : (ribbonCauchyKernel f b).domain z) (hn : NonzeroBoxSearch.Nonzero (Centered.offset b z)) :
    (ribbonCauchyKernel f b).eval z hz ≈ scalarProduct (f.eval z hz.1)
      (RepresentedReciprocal.inverse (Centered.offset b z) hn) :=
  mul_equiv (f.eval z hz.1).property (f.eval z hz.1).property
    ((ribbonPoleReciprocal b).eval z hz.2).property (RepresentedReciprocal.inverse (Centered.offset b z) hn).property
    (equiv_refl _ (f.eval z hz.1).property) (ribbonPoleReciprocal_value b z hz.2 hn)

theorem ribbonCauchyKernel_deformation (f : DomainFunctions.Map) (hf : Holomorphic f)
    (G : RectangleRibbon) (hd : RibbonDomain f G) (b : Scalar) (hb : RibbonPoleInterior G b) :
    Converges (ribbonDifference (ribbonCauchyKernel f b) G (ribbonCauchyKernel_domain f G hd b hb))
      (rationalRectangleScalar QComplex.zero) :=
  ribbonDifference_converges_zero _ (ribbonCauchyKernel_holomorphic f hf b) G (ribbonCauchyKernel_domain f G hd b hb)

end ComputableAnalysis.RiemannHilbert.RectangularContour
