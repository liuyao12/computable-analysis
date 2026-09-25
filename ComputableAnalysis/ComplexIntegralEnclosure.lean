import ComputableAnalysis.FiniteComplexPathCertificate

/-!
# Direct complex chunk enclosures

The inputs are geometric chunks and their finite complex displacements.
Whole-chunk range evidence precedes multiplication and summation. A change
of sampling coordinate is a later comparison, not the integral definition.
-/
namespace ComputableAnalysis.ComplexPathIntegral

/-- The rectangle of a value after multiplication by the upward unit direction.
The old upper imaginary bound becomes the new lower real bound. -/
def rotateRange (B : QBox) : QBox :=
  ⟨⟨-B.hi.im, B.lo.re⟩, ⟨-B.lo.im, B.hi.re⟩⟩

theorem rotateRange_contains {B : QBox} {z : QComplex}
    (hlo : B.lo ≤ z) (hhi : z ≤ B.hi) :
    (rotateRange B).lo ≤ QComplex.mul z ⟨0,1⟩ ∧
    QComplex.mul z ⟨0,1⟩ ≤ (rotateRange B).hi := by
  simp only [rotateRange, QComplex.mul, QComplex.le_def] at *
  constructor <;> constructor <;> grind

/-- Range soundness is independent of the choice of tags in a chunk. -/
theorem subsegmentIntegralBox_contains_point_box
    {f : EntireBoxFunctionRaw} (hf : f.Sound)
    (a b z : QComplex) (n k : Nat)
    (hlo : (segmentSubBox a b n k).lo ≤ z)
    (hhi : z ≤ (segmentSubBox a b n k).hi) :
    (QBox.mul
      (f.point.compute z (hf.entire z) (f.rangePrecision (segmentSubBox a b n k)))
      (QBox.point (segmentStep a b n))).NestedIn
      (subsegmentIntegralBox f a b n k) := by
  apply QBox.mul_nested
  · exact (QBox.ordered_iff_width_height_nonneg _).2
      ((hf.valid z (hf.entire z)).1 _)
  · exact ⟨Rat.le_refl, Rat.le_refl⟩
  · exact hf.range _ z (hf.entire z) hlo hhi
  · exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩

/-- A nonconstant evaluator really encloses the whole input box. -/
theorem zSquared_sound : zSquared.Sound := by
  constructor
  · intro z; trivial
  · intro z hz; exact ComplexRaw.ofQComplex_valid (QComplex.mul z z)
  · intro B z hz hlo hhi
    exact QBox.mul_contains hlo hhi hlo hhi

/-- A constant on an open vertical segment is integrated from its chunk
rectangles, including the first stage. -/
theorem constant_vertical_value (c : QComplex) (x a b : Rat) :
    (polygonalIntegralRawEntire (constantBoxFunction c) [⟨x,a⟩,⟨x,b⟩]).Equiv
      (ComplexRaw.ofQComplex (QComplex.mul c ⟨0,b-a⟩)) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  change QBox.Overlaps
    (polygonalIntegralBoxEntire (constantBoxFunction c) [⟨x,a⟩,⟨x,b⟩] (2^n)) _
  rw [polygonalIntegralBoxEntire_constant c ⟨x,a⟩ [⟨x,b⟩] (2^n) (Nat.two_pow_pos n)]
  simp [polygonalConstantDifferentialDisplacement, polygonalDisplacementTo,
    QComplex.mul, QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero,
    QBox.Overlaps, QBox.point, QComplex.le_def, ComplexRaw.ofQComplex] <;> grind

end ComputableAnalysis.ComplexPathIntegral
