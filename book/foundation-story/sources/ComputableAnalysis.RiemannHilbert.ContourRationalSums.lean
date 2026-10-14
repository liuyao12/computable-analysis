import ComputableAnalysis.RiemannHilbert.ContourInnerAssembly
import ComputableAnalysis.RiemannHilbert.ContourFrameSampleValues

/-! Finite rational square sums and their exact represented values. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

def rationalGridSum : Nat → (Nat → QComplex) → QComplex
  | 0, _ => QComplex.zero
  | n+1, f => QComplex.add (rationalGridSum n f) (f n)

theorem rational_constant_add (q r : QComplex) :
    add (ofQComplex q) (ofQComplex r) = ofQComplex (QComplex.add q r) := rfl

theorem rational_constant_neg (q : QComplex) :
    neg (ofQComplex q) = ofQComplex (QComplex.neg q) := rfl

theorem rationalGridSum_add (n : Nat) (f g : Nat → QComplex) :
    rationalGridSum n (fun j => QComplex.add (f j) (g j))=
      QComplex.add (rationalGridSum n f) (rationalGridSum n g) := by
  induction n with
  | zero => simp only [rationalGridSum,QComplex.add,QComplex.zero,Rat.zero_add]
  | succ n ih =>
    simp only [rationalGridSum]
    rw [ih]
    simp only [QComplex.add,QComplex.mk.injEq]
    constructor <;> grind only

theorem rationalGridSum_scale (r : Rat) (n : Nat) (f : Nat → QComplex) :
    rationalGridSum n (fun j => QComplex.scaleRat r (f j))=
      QComplex.scaleRat r (rationalGridSum n f) := by
  induction n with
  | zero => simp only [rationalGridSum,QComplex.zero,QComplex.scaleRat,Rat.mul_zero]
  | succ n ih =>
    simp only [rationalGridSum]
    rw [ih]
    simp only [QComplex.add,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only

theorem gridScalarSum_rational (n : Nat) (f : Nat → QComplex) :
    (gridScalarSum n (fun j => rationalRectangleScalar (f j))).val.Equiv
      (ofQComplex (rationalGridSum n f)) := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih =>
    exact add_equiv ih (equiv_refl _ (ofQComplex_valid _))

def literalReciprocalSample (q : QComplex) : Scalar :=
  rationalRectangleScalar (QComplex.inverse q)

theorem literalReciprocalSample_value (R : QPos) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q)) :
    reciprocalFrameSample R q ≈ literalReciprocalSample q := by
  have hn := frame_rational_norm_lower R q hq
  have hp := Rat.mul_pos R.property R.property
  have hz := frameDomain_nonzero R _ hq
  have hs := reciprocalFrameSample_value R q hq
  exact Setoid.trans hs (rational_inverse_agreement q hz (by grind only))

theorem innerBoundary_congr_on_frame (f g : QComplex → Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (he : ∀ q, frameDomain R (rationalRectangleScalar q) → f q ≈ g q) :
    innerBoundary f R M ≈ innerBoundary g R M := by
  have hh (j k : Nat) (hj : j=1 ∨ j=2) (hk : k=1 ∨ k=3) :
      (squareFrameHorizontalEdge f R M j k).val.Equiv
        (squareFrameHorizontalEdge g R M j k).val := by
    apply gridScalarSum_congr_bounded M
    intro u hu
    exact mul_equiv (f _).property (g _).property (ofQComplex_valid _) (ofQComplex_valid _)
      (he _ (innerHorizontalPoint_mem R M j k u hM hj hk hu))
      (equiv_refl _ (ofQComplex_valid _))
  have hv (j k : Nat) (hj : j=1 ∨ j=3) (hk : k=1 ∨ k=2) :
      (squareFrameVerticalEdge f R M j k).val.Equiv
        (squareFrameVerticalEdge g R M j k).val := by
    apply gridScalarSum_congr_bounded M
    intro u hu
    exact mul_equiv (f _).property (g _).property (ofQComplex_valid _) (ofQComplex_valid _)
      (he _ (innerVerticalPoint_mem R M j k u hM hj hk hu))
      (equiv_refl _ (ofQComplex_valid _))
  change (frameScalarRectBoundary _ _ 1 1 2 2).val.Equiv _
  unfold frameScalarRectBoundary
  apply add_equiv
  · apply gridScalarSum_congr_bounded 2
    intro u hu
    have hj : 1+u=1 ∨ 1+u=2 := by omega
    exact add_equiv (hh _ 1 hj (Or.inl rfl)) (neg_equiv (hh _ 3 hj (Or.inr rfl)))
  · apply gridScalarSum_congr_bounded 2
    intro u hu
    have hk : 1+u=1 ∨ 1+u=2 := by omega
    exact add_equiv (hv 3 _ (Or.inr rfl) hk) (neg_equiv (hv 1 _ (Or.inl rfl) hk))

def rationalSquareDensity (es : List HalfEdge) (u : Rat) : QComplex :=
  (es.map fun e => pullback e u).foldr QComplex.add QComplex.zero

end ComputableAnalysis.RiemannHilbert.RectangularContour
