import ComputableAnalysis.Calculus

/-!
# A complete branch-local inverse provider

The identity on `[0,1]` is the smallest example of the project inverse
interface.  Its inverse search simply reuses the target interval.  This is a
useful regression: all domain, range, separation, and overlap fields are
constructive and rational, so later nonlinear inverse providers can follow
the same shape without importing a completed real line.
-/

namespace ComputableAnalysis

def identityFunctionOnUnit : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun x => x) 0 1

def identityFunctionOnUnitRegular : IntervalRegularOn identityFunctionOnUnit where
  evalInterval := fun I _ _ => I
  inputPrecision := fun n => n + 1
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    have hwidth : 0 <= I.width := by
      unfold QInterval.width
      grind [hI.1, hI.2.1]
    exact ⟨hwidth, hsmall⟩
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    change QInterval.ContainsInterval I { lo := x, hi := x }
    exact ⟨hIlo, hIhi⟩

def identityInvertibleOnUnit : InvertibleFunctionOnInterval where
  continuous := {
    function := identityFunctionOnUnit
    regular := identityFunctionOnUnitRegular }
  source_ordered := by native_decide
  monotone := MonotoneOnInterval.ofNondecreasing (by
    intro x y hx hy hxy n
    change x <= y
    exact hxy)
  separation := {
    kind := .nondecreasing
    inputPrecision := fun n => n + 1
    inputPrecision_pos := by
      intro n
      omega
    outputPrecision := fun n => n
    separated := by
      intro x y hx hy n hgap
      change x < y
      have hpos : 0 < (1 / ((n + 1 : Nat) : Rat)) :=
        one_div_nat_pos (by omega)
      grind }
  orientation := trivial

theorem identityInvertibleOnUnit_function_eq :
    identityInvertibleOnUnit.function = identityFunctionOnUnit := rfl

theorem identityInvertibleOnUnit_endpoint_range
    (y : InRangeRaw identityInvertibleOnUnit) (n : Nat) :
    0 <= (y.value.compute n).lo /\ (y.value.compute n).hi <= 1 := by
  have h := y.in_range n
  change 0 <= (y.value.compute n).lo /\
    (y.value.compute n).hi <= 1 at h
  exact h

theorem identityForwardRealRaw_equiv_target
    (y : InRangeRaw identityInvertibleOnUnit) :
    (identityInvertibleOnUnit.forwardRealRaw
      { compute := fun n => y.value.compute n }
      (by simpa [RealRaw.Valid] using y.value_valid)
      (by
        intro n
        have h := identityInvertibleOnUnit_endpoint_range y n
        exact ⟨h.1, RealRaw.interval_order_of_valid y.value y.value_valid n,
          h.2⟩)).Equiv y.value := by
  let X : RealRaw := { compute := fun n => y.value.compute n }
  have hX : X.Valid := by simpa [X, RealRaw.Valid] using y.value_valid
  have hsource : forall n,
      subintervalOf (X.compute n)
        identityInvertibleOnUnit.continuous.function.lower
        identityInvertibleOnUnit.continuous.function.upper := by
    intro n
    change subintervalOf (X.compute n) 0 1
    have h := identityInvertibleOnUnit_endpoint_range y n
    exact ⟨h.1, RealRaw.interval_order_of_valid X hX n, h.2⟩
  apply RealRaw.sameStageOverlap_equiv
  intro n
  let s : Nat :=
    identityInvertibleOnUnit.continuous.inputStage X hX n
  have hns : n <= s :=
    identityInvertibleOnUnit.continuous.le_inputStage X hX n
  have hnested := hX.2.1 n s hns
  have hcontains :=
    identityInvertibleOnUnit.continuous.applyRealRaw_contains_candidate
      X hX hsource n
  have hcandidate :
      (identityInvertibleOnUnit.continuous.applyCandidate X hX
        hsource).compute n =
        X.compute s := by
    rfl
  apply (RealRaw.compareAt_overlap_iff
    (identityInvertibleOnUnit.continuous.applyRealRaw X hX
      hsource) X n n).2
  rw [hcandidate] at hcontains
  exact ⟨Rat.le_trans hcontains.1
      (Rat.le_trans hnested.2.1 hnested.2.2),
    Rat.le_trans hnested.1
      (Rat.le_trans hnested.2.1 hcontains.2)⟩

def identityInverseBisectionSearch
    (y : InRangeRaw identityInvertibleOnUnit) :
    InverseBisectionSearch identityInvertibleOnUnit y where
  compute_preimage := fun n => y.value.compute n
  valid_preimage := y.value_valid
  preimage_subinterval := by
    intro n
    have h := identityInvertibleOnUnit_endpoint_range y n
    exact ⟨h.1, (RealRaw.interval_order_of_valid y.value y.value_valid n), h.2⟩
  value_overlaps := by
    intro n
    change QInterval.Overlaps (y.value.compute n) (y.value.compute n)
    have h := RealRaw.interval_order_of_valid y.value y.value_valid n
    exact ⟨h, h⟩
  forward_equiv_target := by
    change (identityInvertibleOnUnit.forwardRealRaw
      { compute := fun n => y.value.compute n }
      y.value_valid
      (by
        intro n
        have h := identityInvertibleOnUnit_endpoint_range y n
        exact ⟨h.1,
          RealRaw.interval_order_of_valid y.value y.value_valid n, h.2⟩)).Equiv
      y.value
    exact identityForwardRealRaw_equiv_target y

def identityInverseRaw : InverseRaw identityInvertibleOnUnit :=
  inverseRawOfSearch identityInverseBisectionSearch

theorem identityInverseRaw_apply_eq_target
    (y : InRangeRaw identityInvertibleOnUnit) :
    (identityInverseRaw.apply y).Equiv y.value := by
  apply RealRaw.equiv_refl
  exact y.value_valid

end ComputableAnalysis
