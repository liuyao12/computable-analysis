import ComputableAnalysis.ComplexMultiplication
import ComputableAnalysis.GeometricPiRotation
import ComputableAnalysis.PiProofs
import ComputableAnalysis.RotationSeries
import ComputableAnalysis.RotationLift
import ComputableAnalysis.SectorAreaReparametrization

/-!
# The certified imaginary half-pi input

This small bridge turns the project's abstract, multi-presentation pi handle
into the represented complex input `i * pi / 2` and a factorial rotation at
its represented half angle.  It is deliberately not an Euler-identity
theorem: the remaining work identifies that stabilized rotation with the
geometric quarter-turn endpoint and establishes the logarithm branch.
-/

namespace ComputableAnalysis

namespace PiProofs

namespace pi

/-- The preferred circle-area representative stays inside its initial
rational enclosure at every stage.  This tiny certificate is the uniform
input bound for the future represented-angle rotation evaluator; it follows
only from the checked nesting of the area boxes. -/
theorem circleArea_bounds (n : Nat) :
    (2 : Rat) <= (circleArea.raw.compute n).lo /\
      (circleArea.raw.compute n).hi <= 4 := by
  have hzero : circleArea.raw.compute 0 = { lo := 2, hi := 4 } := by
    change piCircleArea.compute 0 = { lo := 2, hi := 4 }
    exact piCircleArea_compute_zero
  have hnest := circleArea.valid.2.1 0 n (Nat.zero_le n)
  rw [hzero] at hnest
  exact ⟨hnest.1, hnest.2.2⟩

/-- The represented real angle \(\pi/2\), retained independently of its
imaginary-axis embedding.  The separate name is convenient for algorithms
that consume a bounded real parameter before multiplying by \(i\). -/
def halfPi : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 2) circleArea.raw

theorem halfPi_valid : halfPi.Valid := by
  unfold halfPi
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide) circleArea.valid

/-- The real half-angle inherits an explicit denominator rate from the
circle-area computation.  This is the usable input-width modulus for a
represented-angle series construction. -/
theorem halfPi_width_le_two_div_succ (n : Nat) :
    (halfPi.compute n).width <= 2 / (((n + 1 : Nat) : Rat)) := by
  have harea := AreaLoopValidity.areaWidthLinearBound_four n
  have hhalf : (0 : Rat) <= (1 : Rat) / 2 := by native_decide
  unfold halfPi
  rw [RealRaw.scaleRat_width_of_nonneg hhalf]
  calc
    ((1 : Rat) / 2) * (circleArea.raw.compute n).width <=
        ((1 : Rat) / 2) * (4 / (((n + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left harea hhalf
    _ = 2 / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.div_def, Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Every rational interval for \(\pi/2\) is contained in the fixed box
\([1,2]\).  No decimal approximation or completed-real order is involved. -/
theorem halfPi_bounds (n : Nat) :
    (1 : Rat) <= (halfPi.compute n).lo /\
      (halfPi.compute n).hi <= 2 := by
  have hcircle := circleArea_bounds n
  have hhalf : (0 : Rat) <= (1 : Rat) / 2 := by native_decide
  unfold halfPi RealRaw.scaleRat RealRaw.scaleRatCompute
  simp only [if_pos hhalf]
  change (1 : Rat) <= ((1 : Rat) / 2) * (circleArea.raw.compute n).lo /\
    ((1 : Rat) / 2) * (circleArea.raw.compute n).hi <= 2
  constructor
  · calc
      (1 : Rat) = ((1 : Rat) / 2) * 2 := by native_decide
      _ <= ((1 : Rat) / 2) * (circleArea.raw.compute n).lo :=
        Rat.mul_le_mul_of_nonneg_left hcircle.1 hhalf
  · calc
      ((1 : Rat) / 2) * (circleArea.raw.compute n).hi <=
          ((1 : Rat) / 2) * 4 :=
        Rat.mul_le_mul_of_nonneg_left hcircle.2 hhalf
      _ = 2 := by native_decide

/-- The finite input certificate used by the generic represented-angle
rotation lift.  It isolates exactly the area-loop facts required by the
complex factorial calculation. -/
def halfPiInput : RotationLift.HalfPiInput where
  raw := halfPi
  valid := halfPi_valid
  bounds := halfPi_bounds
  width_le_two_div_succ := halfPi_width_le_two_div_succ

/-- The same represented half-angle, but evaluated through the checked
geometric arctangent identity \(\pi=4\arctan_{\rm geom}(1)\).  Keeping this
finite raw presentation separate exposes the exact input used by the Euler
route before any rotation/geometry identification is claimed. -/
def halfPiFromArctanGeom : RealRaw :=
  RealRaw.scaleRat ((1 : Rat) / 2)
    ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat))

theorem halfPiFromArctanGeom_valid : halfPiFromArctanGeom.Valid := by
  unfold halfPiFromArctanGeom
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    fourArctanGeomOneValid

/-- Scaling the geometric arctangent pi identity yields the represented
half-angle identity \(\pi/2=2\arctan_{\rm geom}(1)\), at the raw interval
level rather than in an ambient completed field. -/
theorem halfPiFromArctanGeom_equiv_halfPi :
    halfPiFromArctanGeom.Equiv halfPi := by
  unfold halfPiFromArctanGeom halfPi
  apply RealRaw.scaleRat_equiv_of_nonneg (by native_decide)
  simpa [circleArea, presentation, piCertifiedPresentation,
    piPresentationRaw] using four_arctanGeom_one_equiv_piCircleArea

/-- The literal two-times-arctangent presentation of the half angle. -/
def twoArctanGeomOne : RealRaw :=
  (2 : Nat) * ArctanGeometry.arctanGeom (1 : Rat)

theorem twoArctanGeomOne_valid : twoArctanGeomOne.Valid := by
  unfold twoArctanGeomOne
  exact RealRaw.natScale_valid 2 arctanGeomOneValid

theorem halfPiFromArctanGeom_equiv_twoArctanGeomOne :
    halfPiFromArctanGeom.Equiv twoArctanGeomOne := by
  have hscale := RealRaw.scaleRat_scaleRat_equiv_of_nonneg
    ((1 : Rat) / 2) (4 : Rat) (by native_decide) (by native_decide)
    (ArctanGeometry.arctanGeom (1 : Rat)) arctanGeomOneValid
  have htwo : ((1 : Rat) / 2) * 4 = 2 := by native_decide
  simpa [halfPiFromArctanGeom, twoArctanGeomOne, htwo] using hscale

theorem halfPi_equiv_twoArctanGeomOne :
    halfPi.Equiv twoArctanGeomOne := by
  exact RealRaw.equiv_trans
    halfPi_valid halfPiFromArctanGeom_valid twoArctanGeomOne_valid
    (RealRaw.equiv_symm halfPiFromArctanGeom_equiv_halfPi)
    halfPiFromArctanGeom_equiv_twoArctanGeomOne

/-- The sector-area clock reaches the same represented quarter-turn angle as
the preferred \(\pi/2\) handle.  This is an endpoint bridge between the
rectangle-integral clock and the established geometric arctangent route. -/
theorem sectorAreaAngleOne_equiv_halfPi :
    (SectorAreaReparametrization.angleAt (1 : Rat) (by
      change (0 : Rat) <= 1 /\ 1 <= (1 : Rat)
      native_decide)).Equiv
      halfPi := by
  let hunit : inDomainInterval
      SectorAreaReparametrization.angleOnUnit.lower
      SectorAreaReparametrization.angleOnUnit.upper (1 : Rat) := by
    change (0 : Rat) <= 1 /\ 1 <= (1 : Rat)
    native_decide
  have hangle := SectorAreaReparametrization.angleAt_equiv_two_arctanGeom
    (1 : Rat) hunit
  have hangle' :
      (SectorAreaReparametrization.angleAt (1 : Rat) hunit).Equiv
        twoArctanGeomOne := by
    simpa [twoArctanGeomOne] using hangle
  exact RealRaw.equiv_trans
    (SectorAreaReparametrization.angleAt_valid (1 : Rat) hunit)
    twoArctanGeomOne_valid halfPi_valid
    hangle' (RealRaw.equiv_symm halfPi_equiv_twoArctanGeomOne)

/-- The geometric normalized quarter-turn input is itself a valid raw real. -/
theorem geometricQuarterTurnOne_valid :
    (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)).Valid := by
  unfold RationalCircle.GeometricTrig.quarterTurnRaw
  exact RealRaw.scaleRat_valid_of_nonneg (by native_decide)
    (by simpa [AreaValid] using AreaLoopValidity.areaValid)

/-- The literal doubled unit-slope arctangent and the normalized geometric
quarter-turn use the same finite area computation. -/
theorem twoArctanGeomOne_equiv_geometricQuarterTurnOne :
    twoArctanGeomOne.Equiv
      (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)) := by
  simpa [twoArctanGeomOne] using
    ArctanGeometry.two_arctanGeom_one_equiv_quarterTurnRaw_one

/-- At normalized quarter turn one, the geometric angle raw is exactly the
preferred represented half-pi input. -/
theorem halfPi_equiv_geometricQuarterTurnOne :
    halfPi.Equiv (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)) := by
  exact RealRaw.equiv_trans
    halfPi_valid twoArctanGeomOne_valid geometricQuarterTurnOne_valid
    halfPi_equiv_twoArctanGeomOne
    twoArctanGeomOne_equiv_geometricQuarterTurnOne

/-- The abstract pi registry and the geometry-only Euler route use the same
represented half angle.  This is an explicit raw-real transport through the
normalized rational-circle quarter turn, rather than a choice of a preferred
decimal or a completed-real equality. -/
theorem halfPi_equiv_geometricHalfPi :
    halfPi.Equiv GeometricPiRotation.halfPi := by
  exact RealRaw.equiv_trans
    halfPi_valid
    geometricQuarterTurnOne_valid
    GeometricPiRotation.halfPi_valid
    halfPi_equiv_geometricQuarterTurnOne
    (RealRaw.equiv_symm
      GeometricPiRotation.halfPi_equiv_geometricQuarterTurnOne)

/-- The rational midpoint selected from any pi/2 input interval remains in the
uniform input range for the imaginary-axis factorial evaluator. -/
theorem halfPi_midpoint_qabs_le_two (n : Nat) :
    qabs ((halfPi.compute n).midpoint) <= 2 := by
  simpa [halfPiInput] using
    RotationLift.HalfPiInput.midpoint_qabs_le_two halfPiInput n

/-- At every rational midpoint of the certified pi/2 input interval, the
common factorial schedule is a valid complex rotation-series computation. -/
theorem uniformRotationExpRaw_halfPi_midpoint_valid (n : Nat) :
    (RotationSeries.uniformRotationExpRaw (halfPi.compute n).midpoint).Valid :=
  RotationSeries.uniformRotationExpRaw_valid _
    (halfPi_midpoint_qabs_le_two n)

/-- Later midpoint samples of pi/2 remain within the earlier input box.
This is the exact rational Cauchy modulus that the represented-angle
rotation construction must combine with a finite series Lipschitz bound. -/
theorem halfPi_midpoint_sub_le_width (k n : Nat) (hkn : k <= n) :
    qabs ((halfPi.compute n).midpoint - (halfPi.compute k).midpoint) <=
      (halfPi.compute k).width := by
  simpa [halfPiInput] using
    RotationLift.HalfPiInput.midpoint_sub_le_width halfPiInput k n hkn

/-- The direct, non-nested candidate for a represented pi/2 rotation.
Stage n evaluates the common rational factorial schedule at the midpoint of
the stage-n pi/2 interval. A later Cauchy containment theorem will stabilize
these already ordered, shrinking candidates without invoking completeness. -/
def halfPiRotationCandidate : ComplexRaw :=
  RotationLift.HalfPiInput.rotationCandidate halfPiInput

theorem halfPiRotationCandidate_compute (n : Nat) :
    halfPiRotationCandidate.compute n =
      RotationSeries.uniformRotationBox (halfPi.compute n).midpoint n := by
  simpa [halfPiRotationCandidate, halfPiInput] using
    RotationLift.HalfPiInput.rotationCandidate_compute halfPiInput n

/-- At a common finite factorial stage, the abstract-registry candidate fits
inside the geometry-only candidate after the explicit Lipschitz enlargement
from both half-angle input widths.  This is a rational-box transport fact;
the stabilization-level equivalence is packaged below from the generic
representative-respecting lift theorem. -/
theorem halfPiRotationCandidate_contained_expand_geometricRotationCandidate
    (n : Nat) :
    QBox.NestedIn (halfPiRotationCandidate.compute n)
      (QBox.expand (GeometricPiRotation.rotationCandidate.compute n)
        (16 * ((halfPi.compute n).width +
          (GeometricPiRotation.halfPi.compute n).width))) := by
  simpa [halfPiRotationCandidate, halfPiInput,
    GeometricPiRotation.rotationCandidate,
    GeometricPiRotation.halfPiInput] using
    RotationLift.HalfPiInput.rotationCandidate_sameStage_contained_expand_of_equiv
      halfPiInput GeometricPiRotation.halfPiInput
      halfPi_equiv_geometricHalfPi n

/-- The symmetric same-stage finite enclosure for the geometry-only
candidate.  Together with the forward enclosure it exhibits the finite data
used by the generic equivalence theorem for the two Cauchy stabilizations. -/
theorem geometricRotationCandidate_contained_expand_halfPiRotationCandidate
    (n : Nat) :
    QBox.NestedIn (GeometricPiRotation.rotationCandidate.compute n)
      (QBox.expand (halfPiRotationCandidate.compute n)
        (16 * ((halfPi.compute n).width +
          (GeometricPiRotation.halfPi.compute n).width))) := by
  simpa [halfPiRotationCandidate, halfPiInput,
    GeometricPiRotation.rotationCandidate,
    GeometricPiRotation.halfPiInput,
    Rat.add_comm] using
    RotationLift.HalfPiInput.rotationCandidate_sameStage_contained_expand_of_equiv
      GeometricPiRotation.halfPiInput halfPiInput
      (RealRaw.equiv_symm halfPi_equiv_geometricHalfPi) n

theorem halfPiRotationCandidate_ordered (n : Nat) :
    (halfPiRotationCandidate.compute n).Ordered := by
  simpa [halfPiRotationCandidate] using
    RotationLift.HalfPiInput.rotationCandidate_ordered halfPiInput n

theorem halfPiRotationCandidate_widths_shrink :
    ComplexRaw.WidthsShrinkToZero halfPiRotationCandidate.compute := by
  simpa [halfPiRotationCandidate] using
    RotationLift.HalfPiInput.rotationCandidate_widths_shrink halfPiInput

/-- The input-error radius for the represented π/2 rotation candidate.
The factor sixteen is the checked finite-prefix Lipschitz budget for the
uniform rational factorial schedule. -/
def halfPiRotationRadius (n : Nat) : Rat :=
  RotationLift.HalfPiInput.rotationRadius halfPiInput n

theorem halfPiRotationRadius_shrinks :
    ShrinksToZero halfPiRotationRadius := by
  simpa [halfPiRotationRadius] using
    RotationLift.HalfPiInput.rotationRadius_shrinks halfPiInput

/-- The represented-angle imaginary-axis rotation.  It stabilizes the
finite boxes obtained by evaluating one common factorial schedule at the
rational midpoint of each certified π/2 interval. -/
def halfPiRotation : ComplexRaw :=
  RotationLift.HalfPiInput.rotation halfPiInput

theorem halfPiRotation_valid : halfPiRotation.Valid := by
  simpa [halfPiRotation] using
    RotationLift.HalfPiInput.rotation_valid halfPiInput

/-- The abstract-pi factorial rotation and the geometry-only factorial
rotation are equivalent.  The generic lift transports raw-real equivalence of
their half-angle inputs through finite Lipschitz boxes and Cauchy prefix
stabilization; no completed complex plane is used. -/
theorem halfPiRotation_equiv_geometricRotation :
    halfPiRotation.Equiv GeometricPiRotation.rotation := by
  simpa [halfPiRotation, halfPiInput,
    GeometricPiRotation.rotation,
    GeometricPiRotation.halfPiInput] using
    RotationLift.HalfPiInput.rotation_equiv_of_input_equiv
      halfPiInput GeometricPiRotation.halfPiInput
      halfPi_equiv_geometricHalfPi

/-- The stabilized represented rotation still contains the direct midpoint
series box at the same stage.  This is the public finite witness to use when
an eventual quarter-turn proof encloses the direct factorial candidate. -/
theorem halfPiRotation_contains_current_candidate (n : Nat) :
    QBox.NestedIn (halfPiRotationCandidate.compute n)
      (halfPiRotation.compute n) := by
  simpa [halfPiRotationCandidate, halfPiRotation] using
    RotationLift.HalfPiInput.rotation_contains_current_candidate halfPiInput n

/-- The certified complex raw input \(i\pi/2\), formed from the default
circle-area representative of the abstract pi handle. -/
def imaginaryHalf : ComplexRaw :=
  ComplexRaw.scaleRat ((1 : Rat) / 2) (ComplexRaw.imaginaryAxis circleArea.raw)

/-- The exact rational complex scalar `i/2`.  Applying it through
`ComplexRaw.qcomplexLeftMul` is the algebraic presentation of the same
represented input as `imaginaryHalf`. -/
def imaginaryHalfScalar : QComplex := { re := 0, im := (1 : Rat) / 2 }

theorem imaginaryHalf_valid : imaginaryHalf.Valid := by
  unfold imaginaryHalf
  exact ComplexRaw.scaleRat_valid_of_nonneg (by native_decide)
    (ComplexRaw.imaginaryAxis_valid circleArea.valid)

/-- The two construction orders for \(i\pi/2\) agree stagewise: first form
the bounded real parameter \(\pi/2\) and embed it, or first embed \(\pi\)
and apply the rational scalar \(1/2\). -/
theorem imaginaryHalf_compute_eq_imaginaryAxis_halfPi :
    imaginaryHalf.compute = (ComplexRaw.imaginaryAxis halfPi).compute := by
  funext n
  have hhalf : (0 : Rat) <= (1 : Rat) / 2 := by native_decide
  simp only [imaginaryHalf, halfPi, ComplexRaw.scaleRat,
    ComplexRaw.imaginaryAxis_compute, RealRaw.scaleRat,
    RealRaw.scaleRatCompute, QBox.scaleRat, if_pos hhalf, Rat.mul_zero]

theorem imaginaryHalf_equiv_imaginaryAxis_halfPi :
    imaginaryHalf.Equiv (ComplexRaw.imaginaryAxis halfPi) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff imaginaryHalf
    (ComplexRaw.imaginaryAxis halfPi) n n).2
  rw [imaginaryHalf_compute_eq_imaginaryAxis_halfPi]
  have hordered := ComplexRaw.valid_ordered
    (ComplexRaw.imaginaryAxis_valid halfPi_valid) n
  exact ⟨hordered, hordered⟩

/-- The registry's `i*pi/2` input is equivalent to the geometry-only
imaginary half angle used by the represented factorial rotation.  Thus the
remaining Euler gap is the rotation-system/quarter-turn endpoint theorem,
not a mismatch between the two half-pi inputs. -/
theorem imaginaryHalf_equiv_geometricImaginaryHalf :
    imaginaryHalf.Equiv GeometricPiRotation.imaginaryHalf := by
  exact ComplexRaw.equiv_trans
    imaginaryHalf_valid
    (ComplexRaw.imaginaryAxis_valid halfPi_valid)
    GeometricPiRotation.imaginaryHalf_valid
    imaginaryHalf_equiv_imaginaryAxis_halfPi
    (ComplexRaw.imaginaryAxis_equiv
      halfPi_valid GeometricPiRotation.halfPi_valid
      halfPi_equiv_geometricHalfPi)

/-- The coordinate construction of `i*pi/2` agrees stage by stage with
literal multiplication of the preferred pi representative by the exact
rational complex scalar (i/2). -/
theorem imaginaryHalf_compute_eq_qcomplexLeftMul :
    imaginaryHalf.compute =
      (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
        (ComplexRaw.ofRealRaw circleArea.raw)).compute := by
  funext n
  change QBox.scaleRat ((1 : Rat) / 2)
      { lo := { re := 0, im := (circleArea.raw.compute n).lo },
        hi := { re := 0, im := (circleArea.raw.compute n).hi } } =
    QBox.add (QBox.scaleRat 0 (QBox.ofRealInterval (circleArea.raw.compute n)))
      (QBox.scaleRat ((1 : Rat) / 2)
        { lo := { re := -(QBox.ofRealInterval (circleArea.raw.compute n)).hi.im,
                  im := (QBox.ofRealInterval (circleArea.raw.compute n)).lo.re },
          hi := { re := -(QBox.ofRealInterval (circleArea.raw.compute n)).lo.im,
                  im := (QBox.ofRealInterval (circleArea.raw.compute n)).hi.re } })
  have h0 : (0 : Rat) <= 0 := by native_decide
  have hhalf : (0 : Rat) <= (1 : Rat) / 2 := by native_decide
  simp only [QBox.scaleRat, QBox.add, QBox.ofRealInterval, if_pos h0,
    if_pos hhalf, Rat.zero_mul, Rat.neg_zero]
  congr 1 <;> congr 1 <;> exact (Rat.zero_add _).symm

/-- The literal `i/2` action on pi is itself a valid complex raw. -/
theorem imaginaryHalf_qcomplexLeftMul_valid :
    (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
      (ComplexRaw.ofRealRaw circleArea.raw)).Valid :=
  ComplexRaw.qcomplexLeftMul_valid imaginaryHalfScalar
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid)

/-- The two presentations of `i*pi/2` are equivalent.  This makes the
Euler route use the same exact complex-scalar operation as later formulas
such as `-2*i*log(i)`, without claiming that the complex exponential is
already defined on this represented input. -/
theorem imaginaryHalf_equiv_qcomplexLeftMul :
    imaginaryHalf.Equiv
      (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
        (ComplexRaw.ofRealRaw circleArea.raw)) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff imaginaryHalf
    (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
      (ComplexRaw.ofRealRaw circleArea.raw)) n n).2
  rw [imaginaryHalf_compute_eq_qcomplexLeftMul]
  have hordered :=
    ComplexRaw.valid_ordered imaginaryHalf_qcomplexLeftMul_valid n
  exact ⟨hordered, hordered⟩

/-- Exact `i/2`-scalar multiplication transports every named pi
presentation to the same represented complex input. -/
theorem imaginaryHalf_qcomplexLeftMul_equiv_presentation
    (kind : PiPresentation) :
    (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
      (ComplexRaw.ofRealRaw circleArea.raw)).Equiv
      (ComplexRaw.qcomplexLeftMul imaginaryHalfScalar
        (ComplexRaw.ofRealRaw (presentation kind).raw)) := by
  apply ComplexRaw.qcomplexLeftMul_equiv
  apply ComplexRaw.ofRealRaw_equiv_of_equiv circleArea.valid
    (presentation kind).valid
  exact representations_equiv circleArea (presentation kind)

/-- The exact scalar `-2i`, used in the complex-logarithm presentation of pi. -/
def negativeTwoImaginaryScalar : QComplex := { re := 0, im := -2 }

/-- The exact rational raw complex number (-2i), retained separately from
the affine scalar so that the Euler/logarithm route can use ordinary certified
complex multiplication. -/
def negativeTwoImaginaryRaw : ComplexRaw :=
  ComplexRaw.ofQComplex negativeTwoImaginaryScalar

theorem negativeTwoImaginaryRaw_valid : negativeTwoImaginaryRaw.Valid :=
  ComplexRaw.ofQComplex_valid negativeTwoImaginaryScalar

/-- The finite rational box calculation

\[
 (-2i)(i\pi/2)=\pi
\]

is exact at every stage of the selected pi representative. -/
theorem negativeTwoImaginaryScalar_imaginaryHalf_compute :
    (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar imaginaryHalf).compute =
      (ComplexRaw.ofRealRaw circleArea.raw).compute := by
  funext n
  change QBox.add
      (QBox.scaleRat 0
        (QBox.scaleRat ((1 : Rat) / 2)
          { lo := { re := 0, im := (circleArea.raw.compute n).lo },
            hi := { re := 0, im := (circleArea.raw.compute n).hi } }))
      (QBox.scaleRat (-2)
        { lo := { re := -(QBox.scaleRat ((1 : Rat) / 2)
                    { lo := { re := 0, im := (circleArea.raw.compute n).lo },
                      hi := { re := 0, im := (circleArea.raw.compute n).hi } }).hi.im,
                  im := (QBox.scaleRat ((1 : Rat) / 2)
                    { lo := { re := 0, im := (circleArea.raw.compute n).lo },
                      hi := { re := 0, im := (circleArea.raw.compute n).hi } }).lo.re },
          hi := { re := -(QBox.scaleRat ((1 : Rat) / 2)
                    { lo := { re := 0, im := (circleArea.raw.compute n).lo },
                      hi := { re := 0, im := (circleArea.raw.compute n).hi } }).lo.im,
                  im := (QBox.scaleRat ((1 : Rat) / 2)
                    { lo := { re := 0, im := (circleArea.raw.compute n).lo },
                      hi := { re := 0, im := (circleArea.raw.compute n).hi } }).hi.re } }) =
    QBox.ofRealInterval (circleArea.raw.compute n)
  have h0 : (0 : Rat) <= 0 := by native_decide
  have hhalf : (0 : Rat) <= (1 : Rat) / 2 := by native_decide
  have hminusTwo : ¬ (0 : Rat) <= -2 := by native_decide
  have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by
    exact Rat.mul_inv_cancel 2 (Rat.ne_of_gt (by native_decide))
  have hscale (q : Rat) : (-2 : Rat) * -(((1 : Rat) / 2) * q) = q := by
    rw [Rat.div_def]
    simp only [Rat.one_mul]
    calc
      (-2 : Rat) * -(2⁻¹ * q) = 2 * (2⁻¹ * q) := by
        grind [Rat.neg_mul, Rat.mul_neg]
      _ = (2 * 2⁻¹) * q := by rw [Rat.mul_assoc]
      _ = q := by rw [htwo, Rat.one_mul]
  simp only [QBox.scaleRat, QBox.add, QBox.ofRealInterval, QComplex.add,
    if_pos h0, if_pos hhalf, if_neg hminusTwo, Rat.zero_mul]
  congr 1 <;> congr 1
  all_goals try rw [hscale]
  all_goals grind

/-- The exact scalar conversion from the certified `i*pi/2` input back to
the real-axis preferred pi representative. -/
theorem negativeTwoImaginaryScalar_imaginaryHalf_equiv_piCircleArea :
    (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar imaginaryHalf).Equiv
      (ComplexRaw.ofRealRaw circleArea.raw) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar imaginaryHalf)
    (ComplexRaw.ofRealRaw circleArea.raw) n n).2
  rw [negativeTwoImaginaryScalar_imaginaryHalf_compute]
  have hordered := ComplexRaw.valid_ordered
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid) n
  exact ⟨hordered, hordered⟩

/-- The same return leg is now also a theorem of ordinary certified complex
multiplication, rather than only of the exact affine scalar shortcut:

\[
  (-2i)(i\pi/2)=\pi.
\]

The general product is first bridged to the affine evaluator using its common
rational center witness; no completed complex field is introduced. -/
theorem negativeTwoImaginaryRaw_mul_imaginaryHalf_equiv_piCircleArea :
    (negativeTwoImaginaryRaw * imaginaryHalf).Equiv
      (ComplexRaw.ofRealRaw circleArea.raw) := by
  have hproductToAffine :
      (negativeTwoImaginaryRaw * imaginaryHalf).Equiv
        (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar imaginaryHalf) := by
    simpa [negativeTwoImaginaryRaw] using
      ComplexRaw.equiv_symm
        (ComplexRaw.qcomplexLeftMul_equiv_mul_ofQComplex
          negativeTwoImaginaryScalar imaginaryHalf_valid)
  exact ComplexRaw.equiv_trans
    (ComplexRaw.mul_valid negativeTwoImaginaryRaw_valid imaginaryHalf_valid)
    (ComplexRaw.qcomplexLeftMul_valid negativeTwoImaginaryScalar imaginaryHalf_valid)
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid)
    hproductToAffine
    negativeTwoImaginaryScalar_imaginaryHalf_equiv_piCircleArea

/-- The remaining branch-specific input for the complex-logarithm pi route.
This package does not construct a logarithm: a series, path, or inverse-exp
branch must separately supply its valid raw evaluator and its agreement with
the certified `i*pi/2` input. -/
structure LogAtICertificate where
  raw : ComplexRaw
  valid : raw.Valid
  agreesWithImaginaryHalf : raw.Equiv imaginaryHalf

/-- Once a complex logarithm branch at `i` has been certified to equal
`i*pi/2`, the formula `-2*i*log(i)=pi` follows using only the checked
exact affine scalar action. -/
theorem negativeTwoImaginary_logAtI_equiv_piCircleArea
    (logI : LogAtICertificate) :
    (ComplexRaw.qcomplexLeftMul negativeTwoImaginaryScalar logI.raw).Equiv
      (ComplexRaw.ofRealRaw circleArea.raw) := by
  exact ComplexRaw.equiv_trans
    (ComplexRaw.qcomplexLeftMul_valid negativeTwoImaginaryScalar logI.valid)
    (ComplexRaw.qcomplexLeftMul_valid negativeTwoImaginaryScalar
      imaginaryHalf_valid)
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid)
    (ComplexRaw.qcomplexLeftMul_equiv negativeTwoImaginaryScalar
      logI.agreesWithImaginaryHalf)
    negativeTwoImaginaryScalar_imaginaryHalf_equiv_piCircleArea

/-- The same conditional logarithm route, stated with literal certified
complex multiplication.  Thus a future branch certificate
\(\log(i)=i\pi/2\) feeds the natural formula \((-2i)\log(i)=\pi\) directly,
without routing the public conclusion through the affine scalar shortcut. -/
theorem negativeTwoImaginaryRaw_mul_logAtI_equiv_piCircleArea
    (logI : LogAtICertificate) :
    (negativeTwoImaginaryRaw * logI.raw).Equiv
      (ComplexRaw.ofRealRaw circleArea.raw) := by
  have hproduct :
      (negativeTwoImaginaryRaw * logI.raw).Equiv
        (negativeTwoImaginaryRaw * imaginaryHalf) := by
    apply ComplexRaw.mul_equiv negativeTwoImaginaryRaw_valid
      negativeTwoImaginaryRaw_valid logI.valid imaginaryHalf_valid
    · exact ComplexRaw.equiv_refl negativeTwoImaginaryRaw
        negativeTwoImaginaryRaw_valid
    · exact logI.agreesWithImaginaryHalf
  exact ComplexRaw.equiv_trans
    (ComplexRaw.mul_valid negativeTwoImaginaryRaw_valid logI.valid)
    (ComplexRaw.mul_valid negativeTwoImaginaryRaw_valid imaginaryHalf_valid)
    (ComplexRaw.ofRealRaw_valid circleArea.raw circleArea.valid)
    hproduct
    negativeTwoImaginaryRaw_mul_imaginaryHalf_equiv_piCircleArea

/-- The `i*pi/2` input formed from any named pi presentation agrees with the
default handle.  This is the representation transport needed before an Euler
route can evaluate a complex exponential at the selected pi value. -/
theorem imaginaryHalf_equiv_presentation (kind : PiPresentation) :
    imaginaryHalf.Equiv
      (((1 : Rat) / 2) * ComplexRaw.imaginaryAxis (presentation kind).raw) := by
  unfold imaginaryHalf
  change (ComplexRaw.scaleRat ((1 : Rat) / 2)
      (ComplexRaw.imaginaryAxis circleArea.raw)).Equiv
    (ComplexRaw.scaleRat ((1 : Rat) / 2)
      (ComplexRaw.imaginaryAxis (presentation kind).raw))
  apply ComplexRaw.scaleRat_equiv_of_nonneg (by native_decide)
  apply ComplexRaw.imaginaryAxis_equiv circleArea.valid (presentation kind).valid
  exact representations_equiv circleArea (presentation kind)

end pi

end PiProofs

end ComputableAnalysis
