import ComputableAnalysis.Basic

/-!
# A rational rectangle isoperimetric certificate

For rectangles, the isoperimetric inequality is an exact rational consequence
of the project's AM--GM square bound.  The general inequality for arbitrary
plane regions remains outside this finite coordinate core.
-/

namespace ComputableAnalysis

def rectanglePerimeter (a b : Rat) : Rat := 2 * (a + b)
def rectangleArea (a b : Rat) : Rat := a * b

/-! A finite triangular fan stores each piece as `(height, width)`.  These
are rational sums, so the resulting bound is available without coordinates,
limits, or a completed area measure. -/
def finiteFanArea : List (Prod Rat Rat) -> Rat
  | [] => 0
  | piece :: rest => piece.1 * piece.2 / 2 + finiteFanArea rest

def finiteFanPerimeter : List (Prod Rat Rat) -> Rat
  | [] => 0
  | piece :: rest => piece.2 + finiteFanPerimeter rest

theorem finiteFanArea_le_half_perimeter :
    forall pieces : List (Prod Rat Rat),
      (forall piece : Prod Rat Rat, List.Mem piece pieces -> piece.1 <= 1) ->
      (forall piece : Prod Rat Rat, List.Mem piece pieces -> 0 <= piece.2) ->
      finiteFanArea pieces <= finiteFanPerimeter pieces / 2
  | [], _hheight, _hwidth => by
      simp [finiteFanArea, finiteFanPerimeter]
      native_decide
  | piece :: rest, hheight, hwidth => by
      have h_height : piece.1 <= 1 :=
        hheight piece (List.Mem.head rest)
      have h_width : 0 <= piece.2 :=
        hwidth piece (List.Mem.head rest)
      have hrest_height :
          forall p : Prod Rat Rat, List.Mem p rest -> p.1 <= 1 := by
        intro p hp
        exact hheight p (List.Mem.tail piece hp)
      have hrest_width :
          forall p : Prod Rat Rat, List.Mem p rest -> 0 <= p.2 := by
        intro p hp
        exact hwidth p (List.Mem.tail piece hp)
      have ih := finiteFanArea_le_half_perimeter rest
        hrest_height hrest_width
      have htriangle : piece.1 * piece.2 / 2 <= piece.2 / 2 := by
        have hmul : piece.1 * piece.2 <= 1 * piece.2 :=
          Rat.mul_le_mul_of_nonneg_right h_height h_width
        have hmul' : piece.1 * piece.2 <= piece.2 := by
          simpa [Rat.one_mul] using hmul
        rw [Rat.div_def, Rat.div_def]
        exact Rat.mul_le_mul_of_nonneg_right hmul'
          (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide)))
      simp [finiteFanArea, finiteFanPerimeter]
      calc
        piece.1 * piece.2 / 2 + finiteFanArea rest <=
            piece.2 / 2 + finiteFanPerimeter rest / 2 := by
          grind
        _ = (piece.2 + finiteFanPerimeter rest) / 2 := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]

theorem finiteFanArea_eq_half_perimeter_of_unit_heights
    (pieces : List (Prod Rat Rat))
    (hheight : ∀ piece : Prod Rat Rat, List.Mem piece pieces -> piece.1 = 1) :
    finiteFanArea pieces = finiteFanPerimeter pieces / 2 := by
  induction pieces with
  | nil =>
      simp [finiteFanArea, finiteFanPerimeter]
      native_decide
  | cons piece rest ih =>
      have hpiece : piece.1 = 1 :=
        hheight piece (List.Mem.head rest)
      have hrest :
          ∀ p : Prod Rat Rat, List.Mem p rest -> p.1 = 1 := by
        intro p hp
        exact hheight p (List.Mem.tail piece hp)
      simp [finiteFanArea, finiteFanPerimeter, hpiece, ih hrest]
      grind [Rat.div_def, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem rectangle_isoperimetric {a b : Rat} :
    16 * rectangleArea a b ≤ rectanglePerimeter a b ^ 2 := by
  unfold rectangleArea rectanglePerimeter
  have h := am_gm_square_bound a b
  grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
    Rat.add_mul]

theorem rectangle_isoperimetric_gap {a b : Rat} :
    rectanglePerimeter a b ^ 2 - 16 * rectangleArea a b =
      4 * (a - b) ^ 2 := by
  unfold rectangleArea rectanglePerimeter
  grind [Rat.pow_succ, Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_add, Rat.add_mul]

theorem rectangle_isoperimetric_eq_iff {a b : Rat} :
    16 * rectangleArea a b = rectanglePerimeter a b ^ 2 ↔ a = b := by
  unfold rectangleArea rectanglePerimeter
  constructor
  · intro h
    apply am_gm_rational_half_eq_iff.mp
    rw [Rat.div_def]
    grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
      Rat.add_mul, Rat.mul_inv_cancel]
  · intro h
    subst b
    grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm, Rat.mul_add,
      Rat.add_mul]

theorem rectangle_three_by_four_certificate :
    rectangleArea 3 4 = 12 /\
      rectanglePerimeter 3 4 = 14 /\
      16 * rectangleArea 3 4 ≤ rectanglePerimeter 3 4 ^ 2 := by
  native_decide

theorem rectangle_five_by_twelve_certificate :
    rectangleArea 5 12 = 60 /\
      rectanglePerimeter 5 12 = 34 /\
      16 * rectangleArea 5 12 < rectanglePerimeter 5 12 ^ 2 /\
      rectanglePerimeter 5 12 ^ 2 - 16 * rectangleArea 5 12 = 196 := by
  native_decide

end ComputableAnalysis
