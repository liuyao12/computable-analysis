import ComputableAnalysis.RiemannHilbert.ContourIntervalGrid

/-! Actual continuous functions on horizontal or vertical represented edges
instantiate interval-cell oscillation without a supplied uniform modulus. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def horizontalIntervalSample (f : DomainFunctions.Map) (I : QInterval) (y : Rat)
    (hdom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (t : Rat) : Scalar := continuousRectangleSample f (horizontalIntervalRectangle I y) hdom ⟨t,y⟩

def verticalIntervalSample (f : DomainFunctions.Map) (I : QInterval) (x : Rat)
    (hdom : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (t : Rat) : Scalar := continuousRectangleSample f (verticalIntervalRectangle I x) hdom ⟨x,t⟩

theorem horizontalIntervalSample_oscillation (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (I : QInterval) (y : Rat) (hI : I.lo≤I.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ j, j<2^n → ∀ p q : Rat,
      ((intervalGridCell I (2^n) j).lo≤p ∧ p≤(intervalGridCell I (2^n) j).hi) →
      ((intervalGridCell I (2^n) j).lo≤q ∧ q≤(intervalGridCell I (2^n) j).hi) →
      Small (sub (horizontalIntervalSample f I y hdom q).val
        (horizontalIntervalSample f I y hdom p).val) eps.val := by
  obtain ⟨N,hN⟩ := continuousRectangle_cell_oscillation f hc (horizontalIntervalRectangle I y) hdom hI
    (show y≤y from Rat.le_refl) eps
  refine ⟨N, ?_⟩
  intro n hn j hj p q hp hq
  have hs := hN n hn j 0 hj (Nat.two_pow_pos n) (⟨p,y⟩ : QComplex) (⟨q,y⟩ : QComplex)
  rw [horizontalIntervalRectangle_cell] at hs
  exact hs ⟨hp.1,hp.2,Rat.le_refl,Rat.le_refl⟩ ⟨hq.1,hq.2,Rat.le_refl,Rat.le_refl⟩

theorem verticalIntervalSample_oscillation (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (I : QInterval) (x : Rat) (hI : I.lo≤I.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ j, j<2^n → ∀ p q : Rat,
      ((intervalGridCell I (2^n) j).lo≤p ∧ p≤(intervalGridCell I (2^n) j).hi) →
      ((intervalGridCell I (2^n) j).lo≤q ∧ q≤(intervalGridCell I (2^n) j).hi) →
      Small (sub (verticalIntervalSample f I x hdom q).val
        (verticalIntervalSample f I x hdom p).val) eps.val := by
  obtain ⟨N,hN⟩ := continuousRectangle_cell_oscillation f hc (verticalIntervalRectangle I x) hdom
    (show x≤x from Rat.le_refl) hI eps
  refine ⟨N, ?_⟩
  intro n hn j hj p q hp hq
  have hs := hN n hn 0 j (Nat.two_pow_pos n) hj (⟨x,p⟩ : QComplex) (⟨x,q⟩ : QComplex)
  rw [verticalIntervalRectangle_cell] at hs
  exact hs ⟨Rat.le_refl,Rat.le_refl,hp.1,hp.2⟩ ⟨Rat.le_refl,Rat.le_refl,hq.1,hq.2⟩

end ComputableAnalysis.RiemannHilbert.RectangularContour
