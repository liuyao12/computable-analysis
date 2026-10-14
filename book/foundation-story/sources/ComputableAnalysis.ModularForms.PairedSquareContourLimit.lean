import ComputableAnalysis.ModularForms.PairedSquareDyadicDecay

/-! A concrete interval-name limit using a classically selected depth schedule.
The finite samples and interval stabilization are executable for supplied
executable schedules. The selected schedule below is noncomputable; no
computability certificate or integral/Cauchy formula is asserted. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

noncomputable def contourChosenDepth (a : Scalar) (R : Rat) (hR : 0<R) (k : Nat) : Nat :=
  Classical.choose (pairedSquareDyadicContour_cauchy a R hR (RepresentedCauchySum.error k))

def monotoneDepth (choose : Nat → Nat) : Nat → Nat
  | 0 => choose 0
  | k+1 => max (monotoneDepth choose k) (choose (k+1))

theorem monotoneDepth_ge (choose : Nat → Nat) (k : Nat) : choose k≤monotoneDepth choose k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

theorem monotoneDepth_monotone (choose : Nat → Nat) (k n : Nat) (hkn : k≤n) :
    monotoneDepth choose k≤monotoneDepth choose n := by
  induction hkn with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

noncomputable def contourDepth (a : Scalar) (R : Rat) (hR : 0<R) : Nat → Nat :=
  monotoneDepth (contourChosenDepth a R hR)

noncomputable def contourScheduledSample (a : Scalar) (R : Rat) (hR : 0<R) (k : Nat) : ComplexRaw :=
  (pairedSquareDyadicContour a R (contourDepth a R hR k)).val

theorem contourScheduledSample_valid (a : Scalar) (R : Rat) (hR : 0<R) (k : Nat) :
    (contourScheduledSample a R hR k).Valid :=
  (pairedSquareDyadicContour a R (contourDepth a R hR k)).property

theorem contourScheduledSample_cauchy (a : Scalar) (R : Rat) (hR : 0<R)
    (k n : Nat) (hkn : k≤n) :
    Small (sub (contourScheduledSample a R hR n) (contourScheduledSample a R hR k))
      (RepresentedCauchySum.error k).val := by
  have hs := Classical.choose_spec
    (pairedSquareDyadicContour_cauchy a R hR (RepresentedCauchySum.error k))
  have hk := monotoneDepth_ge (contourChosenDepth a R hR) k
  have hn := monotoneDepth_monotone (contourChosenDepth a R hR) k n hkn
  exact hs _ _ (Nat.le_trans hk hn) hk

noncomputable def pairedSquareContourLimit (a : Scalar) (R : Rat) (hR : 0<R) : ComplexRaw :=
  RepresentedCauchySum.value (contourScheduledSample a R hR)
    (contourScheduledSample_valid a R hR) (fun k => (RepresentedCauchySum.error k).val)

theorem pairedSquareContourLimit_valid (a : Scalar) (R : Rat) (hR : 0<R) :
    (pairedSquareContourLimit a R hR).Valid :=
  RepresentedCauchySum.value_valid _ _ _ RepresentedCauchySum.error_shrinks
    (contourScheduledSample_cauchy a R hR)

theorem pairedSquareContourLimit_sample_error (a : Scalar) (R : Rat) (hR : 0<R) (k : Nat) :
    Small (sub (pairedSquareContourLimit a R hR) (contourScheduledSample a R hR k))
      (RepresentedCauchySum.error k).val :=
  RepresentedCauchySum.value_close_prefix _ _ _ (contourScheduledSample_cauchy a R hR) k

end ComputableAnalysis.ModularForms
