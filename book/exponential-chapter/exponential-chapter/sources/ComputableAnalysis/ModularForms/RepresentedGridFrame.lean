import ComputableAnalysis.ModularForms.PairedRiccatiGridBoundaryVanishing

/-! Exact represented contour cancellation around a rectangular hole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem gridValueSum_append (f : Nat → ScalarAlgebra.Value) (m n : Nat) :
    gridValueSum (m + n) f = gridValueSum m f + gridValueSum n (fun j => f (m + j)) := by
  induction n with
  | zero => simp only [Nat.add_zero, gridValueSum]; grind only
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by omega, gridValueSum, ih, gridValueSum]
    grind only

def frameValueRectSum (f : Nat → Nat → ScalarAlgebra.Value) (x y m n : Nat) : ScalarAlgebra.Value :=
  gridValueSum m (fun j => gridValueSum n (fun k => f (x + j) (y + k)))

theorem frameValueRectSum_split_x (f : Nat → Nat → ScalarAlgebra.Value) (x y m r n : Nat) :
    frameValueRectSum f x y (m + r) n =
      frameValueRectSum f x y m n + frameValueRectSum f (x + m) y r n := by
  unfold frameValueRectSum
  rw [gridValueSum_append]
  simp only [Nat.add_assoc]

theorem frameValueRectSum_split_y (f : Nat → Nat → ScalarAlgebra.Value) (x y m n t : Nat) :
    frameValueRectSum f x y m (n + t) =
      frameValueRectSum f x y m n + frameValueRectSum f x (y + n) m t := by
  unfold frameValueRectSum
  simp only [gridValueSum_append, gridValueSum_add, Nat.add_assoc]

def frameValueRectBoundary (H V : Nat → Nat → ScalarAlgebra.Value) (x y m n : Nat) : ScalarAlgebra.Value :=
  gridValueBoundary (fun j k => H (x + j) (y + k)) (fun j k => V (x + j) (y + k)) m n

theorem frameValueRect_stokes (H V : Nat → Nat → ScalarAlgebra.Value) (x y m n : Nat) :
    frameValueRectSum (gridValueCell H V) x y m n = frameValueRectBoundary H V x y m n := by
  have h := gridValue_discrete_stokes (fun j k => H (x + j) (y + k))
    (fun j k => V (x + j) (y + k)) m n
  simpa only [frameValueRectSum, frameValueRectBoundary, gridValueCell, Nat.add_assoc] using h

/-- Four disjoint strips: full-width bottom and top, then the left and
right strips at the height of the hole. The hole's cells are not evaluated. -/
def frameValueSum (f : Nat → Nat → ScalarAlgebra.Value) (left holeWidth right bottom holeHeight top : Nat) : ScalarAlgebra.Value :=
  (frameValueRectSum f 0 0 (left + holeWidth + right) bottom +
    frameValueRectSum f 0 (bottom + holeHeight) (left + holeWidth + right) top) +
  (frameValueRectSum f 0 bottom left holeHeight +
    frameValueRectSum f (left + holeWidth) bottom right holeHeight)

theorem frameValueSum_eq_difference (f : Nat → Nat → ScalarAlgebra.Value)
    (l p r b q t : Nat) :
    frameValueSum f l p r b q t =
      frameValueRectSum f 0 0 (l + p + r) (b + q + t) - frameValueRectSum f l b p q := by
  have h0 := frameValueRectSum_split_y f 0 0 (l + p + r) b (q + t)
  have h1 := frameValueRectSum_split_y f 0 b (l + p + r) q t
  have h2 := frameValueRectSum_split_x f 0 b l (p + r) q
  have h3 := frameValueRectSum_split_x f l b p r q
  simp only [Nat.zero_add, ← Nat.add_assoc] at h0 h2
  rw [h1, h2, h3] at h0
  unfold frameValueSum
  rw [h0]
  grind only

/-- Annular discrete Stokes. Both displayed contours are counterclockwise;
the subtraction gives the clockwise orientation on the hole gridValueBoundary. -/
theorem frameValue_stokes (H V : Nat → Nat → ScalarAlgebra.Value) (l p r b q t : Nat) :
    frameValueSum (gridValueCell H V) l p r b q t =
      frameValueRectBoundary H V 0 0 (l + p + r) (b + q + t) - frameValueRectBoundary H V l b p q := by
  rw [frameValueSum_eq_difference, frameValueRect_stokes, frameValueRect_stokes]


def frameScalarRectSum (f : Nat → Nat → Scalar) (x y m n : Nat) : Scalar :=
  gridScalarSum m (fun j => gridScalarSum n (fun k => f (x+j) (y+k)))

def frameScalarRectBoundary (h v : Nat → Nat → Scalar) (x y m n : Nat) : Scalar :=
  gridScalarBoundary (fun j k => h (x+j) (y+k)) (fun j k => v (x+j) (y+k)) m n

def frameScalarSum (f : Nat → Nat → Scalar) (l p r b q t : Nat) : Scalar :=
  scalarSum
    (scalarSum (frameScalarRectSum f 0 0 (l+p+r) b)
      (frameScalarRectSum f 0 (b+q) (l+p+r) t))
    (scalarSum (frameScalarRectSum f 0 b l q)
      (frameScalarRectSum f (l+p) b r q))

theorem frameScalarRectSum_value (f : Nat → Nat → Scalar) (x y m n : Nat) :
    gridScalarValue (frameScalarRectSum f x y m n)=
      frameValueRectSum (fun j k => gridScalarValue (f j k)) x y m n := by
  simp only [frameScalarRectSum,frameValueRectSum,gridScalarSum_value]

theorem frameScalarSum_value (f : Nat → Nat → Scalar) (l p r b q t : Nat) :
    gridScalarValue (frameScalarSum f l p r b q t)=
      frameValueSum (fun j k => gridScalarValue (f j k)) l p r b q t := by
  simp only [frameScalarSum,frameValueSum,gridScalarValue_add,frameScalarRectSum_value]

theorem frameScalarRectBoundary_value (h v : Nat → Nat → Scalar) (x y m n : Nat) :
    gridScalarValue (frameScalarRectBoundary h v x y m n)=
      frameValueRectBoundary (fun j k => gridScalarValue (h j k))
        (fun j k => gridScalarValue (v j k)) x y m n := by
  simp only [frameScalarRectBoundary,frameValueRectBoundary,gridScalarBoundary,
    gridValueBoundary,gridScalarValue_add,gridScalarSum_value,gridScalarValue_sub]

theorem representedGrid_frame_stokes (h v : Nat → Nat → Scalar) (l p r b q t : Nat) :
    (frameScalarSum (gridScalarCell h v) l p r b q t).val.Equiv
      (gridScalarSub (frameScalarRectBoundary h v 0 0 (l+p+r) (b+q+t))
        (frameScalarRectBoundary h v l b p q)).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (frameScalarSum (gridScalarCell h v) l p r b q t).property)
    (hright := (gridScalarSub (frameScalarRectBoundary h v 0 0 (l+p+r) (b+q+t))
      (frameScalarRectBoundary h v l b p q)).property)
  change gridScalarValue (frameScalarSum (gridScalarCell h v) l p r b q t)=
    gridScalarValue (gridScalarSub _ _)
  rw [frameScalarSum_value,gridScalarValue_sub,frameScalarRectBoundary_value,
    frameScalarRectBoundary_value]
  simp only [gridScalarCell,gridScalarValue_add,gridScalarValue_sub]
  exact frameValue_stokes _ _ l p r b q t

def representedFrameCell (l p r b q t j k : Nat) : Prop :=
  j<l+p+r ∧ k<b+q+t ∧ (j<l ∨ l+p≤j ∨ k<b ∨ b+q≤k)

def representedFrameCellCount (l p r b q t : Nat) : Nat :=
  (l+p+r)*b+(l+p+r)*t+l*q+r*q

theorem frameScalarRectSum_bound (f : Nat → Nat → Scalar) (x y m n : Nat)
    (E : Rat) (hE : 0≤E)
    (hf : ∀ j k, j<m → k<n → Small (f (x+j) (y+k)).val E) :
    Small (frameScalarRectSum f x y m n).val ((m:Rat)*((n:Rat)*E)) :=
  gridScalarDoubleSum_bound m n _ E hE hf

theorem frameScalarSum_bound (f : Nat → Nat → Scalar) (l p r b q t : Nat)
    (E : Rat) (hE : 0≤E)
    (hf : ∀ j k, representedFrameCell l p r b q t j k → Small (f j k).val E) :
    Small (frameScalarSum f l p r b q t).val ((representedFrameCellCount l p r b q t:Rat)*E) := by
  have hb := frameScalarRectSum_bound f 0 0 (l+p+r) b E hE (by
    intro j k hj hk; apply hf; unfold representedFrameCell; omega)
  have ht := frameScalarRectSum_bound f 0 (b+q) (l+p+r) t E hE (by
    intro j k hj hk; apply hf; unfold representedFrameCell; omega)
  have hl := frameScalarRectSum_bound f 0 b l q E hE (by
    intro j k hj hk; apply hf; unfold representedFrameCell; omega)
  have hr := frameScalarRectSum_bound f (l+p) b r q E hE (by
    intro j k hj hk; apply hf; unfold representedFrameCell; omega)
  have ha := LocalODE.small_add (LocalODE.small_add hb ht) (LocalODE.small_add hl hr)
  have he : ((l+p+r:Nat):Rat)*((b:Rat)*E)+((l+p+r:Nat):Rat)*((t:Rat)*E)+
      ((l:Rat)*((q:Rat)*E)+(r:Rat)*((q:Rat)*E))=
      ((representedFrameCellCount l p r b q t:Nat):Rat)*E := by
    simp only [representedFrameCellCount,Rat.natCast_add,Rat.natCast_mul]
    grind only
  rw [he] at ha
  exact ha

theorem representedGrid_frame_difference_bound (h v : Nat → Nat → Scalar)
    (l p r b q t : Nat) (E : Rat) (hE : 0≤E)
    (hf : ∀ j k, representedFrameCell l p r b q t j k → Small (gridScalarCell h v j k).val E) :
    Small (gridScalarSub (frameScalarRectBoundary h v 0 0 (l+p+r) (b+q+t))
      (frameScalarRectBoundary h v l b p q)).val ((representedFrameCellCount l p r b q t:Rat)*E) :=
  Small.congr (frameScalarSum (gridScalarCell h v) l p r b q t).property
    (gridScalarSub (frameScalarRectBoundary h v 0 0 (l+p+r) (b+q+t))
      (frameScalarRectBoundary h v l b p q)).property
    (representedGrid_frame_stokes h v l p r b q t)
    (frameScalarSum_bound _ l p r b q t E hE hf)

theorem weightedGrid_frame_difference_bound (f : QComplex → Scalar)
    (J : QInterval × QInterval) (M l p r b q t : Nat) (E : Rat) (hE : 0≤E)
    (hf : ∀ j k, representedFrameCell l p r b q t j k →
      Small (fullRectangleMidpointCycle f (rectangleGridCell J M j k)).val E) :
    Small (gridScalarSub
      (frameScalarRectBoundary (rectangleGridHorizontal f J M) (rectangleGridVertical f J M)
        0 0 (l+p+r) (b+q+t))
      (frameScalarRectBoundary (rectangleGridHorizontal f J M) (rectangleGridVertical f J M)
        l b p q)).val ((representedFrameCellCount l p r b q t:Rat)*E) := by
  apply representedGrid_frame_difference_bound _ _ l p r b q t E hE
  intro j k hframe
  exact Small.congr
    (fullRectangleMidpointCycle f (rectangleGridCell J M j k)).property
    (gridScalarCell (rectangleGridHorizontal f J M) (rectangleGridVertical f J M) j k).property
    (equiv_symm (weightedGridCell_midpoint_agreement f J M j k)) (hf j k hframe)

end ComputableAnalysis.ModularForms
