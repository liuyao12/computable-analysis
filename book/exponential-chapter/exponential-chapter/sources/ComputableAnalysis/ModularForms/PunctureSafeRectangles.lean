import ComputableAnalysis.ModularForms.PairedRiccatiCauchyIntegrandAgreement
import ComputableAnalysis.ModularForms.RationalMidpointGrid

/-! Whole-rectangle nonzero evidence for the actual punctured integrand. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def representedRectangleContains (J : QInterval × QInterval) (z : Scalar) : Prop :=
  RealRaw.Le (RealRaw.ofRat J.1.lo) z.val.realPart ∧
  RealRaw.Le z.val.realPart (RealRaw.ofRat J.1.hi) ∧
  RealRaw.Le (RealRaw.ofRat J.2.lo) z.val.imagPart ∧
  RealRaw.Le z.val.imagPart (RealRaw.ofRat J.2.hi)

def rectangleSeparated (J : QInterval × QInterval) (R : QPos) : Prop :=
  R.val≤J.1.lo ∨ J.1.hi≤ -R.val ∨ R.val≤J.2.lo ∨ J.2.hi≤ -R.val

theorem representedRectangle_nonzero (J : QInterval × QInterval) (R : QPos)
    (hs : rectangleSeparated J R) (z : Scalar) (hz : representedRectangleContains J z) :
    NonzeroBoxSearch.Nonzero z := by
  intro he
  have hr := ComplexRaw.realPart_equiv he
  have hi := ComplexRaw.imagPart_equiv he
  have hrv := realPart_valid z.property
  have hiv := imagPart_valid z.property
  have hzero : (RealRaw.ofRat 0).Valid := RealRaw.ofRat_valid 0
  have hr0 : RealRaw.Le z.val.realPart (RealRaw.ofRat 0) := RealRaw.le_of_equiv hrv hzero hr
  have h0r : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart :=
    RealRaw.le_of_equiv hzero hrv (RealRaw.equiv_symm hr)
  have hi0 : RealRaw.Le z.val.imagPart (RealRaw.ofRat 0) := RealRaw.le_of_equiv hiv hzero hi
  have h0i : RealRaw.Le (RealRaw.ofRat 0) z.val.imagPart :=
    RealRaw.le_of_equiv hzero hiv (RealRaw.equiv_symm hi)
  rcases hs with hs|hs|hs|hs
  · have hb := (RealRaw.le_trans hrv hz.1 hr0) 0 0
    change J.1.lo≤0 at hb
    have hp := R.property
    grind only
  · have hb := (RealRaw.le_trans hrv h0r hz.2.1) 0 0
    change (0:Rat)≤J.1.hi at hb
    have hp := R.property
    grind only
  · have hb := (RealRaw.le_trans hiv hz.2.2.1 hi0) 0 0
    change J.2.lo≤0 at hb
    have hp := R.property
    grind only
  · have hb := (RealRaw.le_trans hiv h0i hz.2.2.2) 0 0
    change (0:Rat)≤J.2.hi at hb
    have hp := R.property
    grind only

theorem rationalRectangle_represented_mem (J : QInterval × QInterval) (q : QComplex)
    (hq : rationalRectangleContains J q) : representedRectangleContains J (rationalRectangleScalar q) :=
  ⟨fun _ _ => hq.1,fun _ _ => hq.2.1,fun _ _ => hq.2.2.1,fun _ _ => hq.2.2.2⟩

theorem punctureSafeRectangle_kernel_domain (a : Scalar) (J : QInterval × QInterval) (R : QPos)
    (hs : rectangleSeparated J R) (z : Scalar) (hz : representedRectangleContains J z) :
    (pairedRiccatiCauchyIntegrandMap a).domain z := representedRectangle_nonzero J R hs z hz

theorem punctureSafeGridCell_kernel_domain (a : Scalar) (J : QInterval × QInterval)
    (R : QPos) (hs : rectangleSeparated J R) (M j k : Nat)
    (hM : 0<M) (hj : j<M) (hk : k<M)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (q : QComplex) (hq : rationalRectangleContains (rectangleGridCell J M j k) q) :
    (pairedRiccatiCauchyIntegrandMap a).domain (rationalRectangleScalar q) :=
  punctureSafeRectangle_kernel_domain a J R hs (rationalRectangleScalar q)
    (rationalRectangle_represented_mem J q
      (rectangleGridCell_contains_initial J M j k hM hj hk hX hY q hq))

end ComputableAnalysis.ModularForms
