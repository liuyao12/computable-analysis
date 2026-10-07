import ComputableAnalysis.FTA.RealFactors

/-! Reciprocal construction for arbitrary nonzero represented complex values.
A finite positive norm enclosure drives the executable reciprocal. Existence
of that enclosure is proved from nonzero raw-value equivalence. -/
namespace ComputableAnalysis.RepresentedPolynomial
open ComputableCoefficient

def realCoordinate (z : ComplexCert) : Real :=
  Real.ofRaw z.raw.realPart (ComplexRaw.realPart_valid z.valid)

def imagCoordinate (z : ComplexCert) : Real :=
  Real.ofRaw z.raw.imagPart (ComplexRaw.imagPart_valid z.valid)

def normValue (z : ComplexCert) : Value :=
  let u := Value.parameter (realCoordinate z)
  let v := Value.parameter (imagCoordinate z)
  Value.add (Value.mul u u) (Value.mul v v)

private theorem squared_separation (B : QBox) (h : ¬ B.Overlaps QBox.zero) :
    ∃ δ : Rat, 0 < δ ∧ ∀ w : QComplex, B.lo ≤ w → w ≤ B.hi → δ ≤ QComplex.normSq w := by
  have hcases : B.hi.re < 0 ∨ 0 < B.lo.re ∨ B.hi.im < 0 ∨ 0 < B.lo.im := by
    change ¬ ((B.lo.re ≤ 0 ∧ B.lo.im ≤ 0) ∧ (0 ≤ B.hi.re ∧ 0 ≤ B.hi.im)) at h
    grind
  have sqmono {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) : a*a ≤ b*b := by
    have h1 := Rat.mul_le_mul_of_nonneg_left hab ha
    have h2 := Rat.mul_le_mul_of_nonneg_right hab (Rat.le_trans ha hab)
    grind
  rcases hcases with hr | hr | hi | hi
  · refine ⟨B.hi.re*B.hi.re, ?_, ?_⟩
    · have hp := Rat.mul_pos (show 0 < -B.hi.re by grind) (show 0 < -B.hi.re by grind)
      grind
    · intro w _ hw
      have hsq := sqmono (a := -B.hi.re) (b := -w.re) (by grind) (Rat.neg_le_neg hw.1)
      have him := rat_square_nonneg_basic w.im
      unfold QComplex.normSq
      grind
  · refine ⟨B.lo.re*B.lo.re, Rat.mul_pos hr hr, ?_⟩
    intro w hw _
    have hsq := sqmono (Rat.le_of_lt hr) hw.1
    have him := rat_square_nonneg_basic w.im
    unfold QComplex.normSq
    grind
  · refine ⟨B.hi.im*B.hi.im, ?_, ?_⟩
    · have hp := Rat.mul_pos (show 0 < -B.hi.im by grind) (show 0 < -B.hi.im by grind)
      grind
    · intro w _ hw
      have hsq := sqmono (a := -B.hi.im) (b := -w.im) (by grind) (Rat.neg_le_neg hw.2)
      have hre := rat_square_nonneg_basic w.re
      unfold QComplex.normSq
      grind
  · refine ⟨B.lo.im*B.lo.im, Rat.mul_pos hi hi, ?_⟩
    intro w hw _
    have hsq := sqmono (Rat.le_of_lt hi) hw.2
    have hre := rat_square_nonneg_basic w.re
    unfold QComplex.normSq
    grind

/-- Nonzero complex values have a strictly positive finite norm enclosure.
This derives the division certificate; callers need not provide a precision. -/
theorem exists_positive_norm_stage (z : ComplexCert) (hz : ¬ z.raw.Equiv zero.raw) :
    ∃ N, 0 < ((normValue z).real.compute N).lo := by
  classical
  have hsep : ∃ N, ¬ (z.raw.compute N).Overlaps QBox.zero := by
    apply Classical.byContradiction
    intro hnone
    apply hz
    intro n
    apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
    change (z.raw.compute n).Overlaps QBox.zero
    exact Classical.byContradiction (fun hn => hnone ⟨n, hn⟩)
  obtain ⟨N, hN⟩ := hsep
  obtain ⟨δ, hδ, hbound⟩ := squared_separation (z.raw.compute N) hN
  have hhalf : 0 < δ / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_pos hδ (by decide +kernel)
  obtain ⟨M, hM⟩ := (normValue z).real.valid.2.2 ⟨δ/2, hhalf⟩
  let k := max N M
  let s : Real → Rat := fun a => (a.compute k).lo
  have hval := (normValue z).encloses k k
    (by simp [normValue, Value.add, Value.mul, Value.parameter]) s (samples_lower k)
  have hsamp : (normValue z).sample s = QComplex.normSq (z.raw.compute k).lo := rfl
  rw [hsamp] at hval
  have hn := ComplexRaw.valid_nestedIn z.valid (show N ≤ k by dsimp [k]; omega)
  have ho := ComplexRaw.valid_ordered z.valid k
  have hnorm := hbound (z.raw.compute k).lo hn.1 (QComplex.le_trans ho hn.2)
  have hw := hM k (show M ≤ k by dsimp [k]; omega)
  have hh : δ/2+δ/2=δ := by
    rw [Rat.div_def]
    have : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
    grind
  refine ⟨k, ?_⟩
  change ((normValue z).real.compute k).hi - ((normValue z).real.compute k).lo ≤ δ/2 at hw
  grind

def inverseRealValue (z : ComplexCert) (N : Nat)
    (h : 0 < ((normValue z).real.compute N).lo) : Value :=
  Value.mul (Value.parameter (realCoordinate z)) (Value.positiveInv (normValue z) N h)

def inverseImagValue (z : ComplexCert) (N : Nat)
    (h : 0 < ((normValue z).real.compute N).lo) : Value :=
  Value.neg (Value.mul (Value.parameter (imagCoordinate z)) (Value.positiveInv (normValue z) N h))

/-- Executable reciprocal after a finite positive norm test succeeds. -/
def inverseAt (z : ComplexCert) (N : Nat)
    (h : 0 < ((normValue z).real.compute N).lo) : ComplexCert :=
  ofParts (inverseRealValue z N h).real (inverseImagValue z N h).real

/-- The reciprocal computed from a finite norm certificate satisfies the exact
field identity for arbitrary represented complex inputs. -/
theorem mul_inverseAt (z : ComplexCert) (N : Nat)
    (h : 0 < ((normValue z).real.compute N).lo) :
    (mul z (inverseAt z N h)).raw.Equiv (ofQComplex QComplex.one).raw := by
  intro n
  let m := max n N
  let s : Real → Rat := fun a => (a.compute m).lo
  have hs : Samples m s := samples_lower m
  have hRe := (inverseRealValue z N h).encloses n m
    (by simp [inverseRealValue, normValue, Value.mul, Value.parameter, Value.positiveInv,
      Value.add, m]; omega) s hs
  have hIm := (inverseImagValue z N h).encloses n m
    (by simp [inverseImagValue, normValue, Value.neg, Value.mul, Value.parameter,
      Value.positiveInv, Value.add, m]; omega) s hs
  have hNorm := (normValue z).encloses N m
    (by simp [normValue, Value.add, Value.mul, Value.parameter, m]; omega) s hs
  have hp : 0 < (normValue z).sample s := by have := hNorm.1; grind
  let a : QComplex := (z.raw.compute m).lo
  let b : QComplex :=
    { re := (inverseRealValue z N h).sample s
      im := (inverseImagValue z N h).sample s }
  have hb : ((inverseAt z N h).raw.compute n).lo ≤ b ∧
      b ≤ ((inverseAt z N h).raw.compute n).hi := ⟨⟨hRe.1, hIm.1⟩, ⟨hRe.2, hIm.2⟩⟩
  have hn := ComplexRaw.valid_nestedIn z.valid (show n ≤ m by dsimp [m]; omega)
  have ha := ComplexRaw.valid_ordered z.valid m
  have hmul := QBox.mul_contains hn.1 (QComplex.le_trans ha hn.2) hb.1 hb.2
  have heq : QComplex.mul a b = QComplex.one := by
    have hcancel := Rat.mul_inv_cancel ((normValue z).sample s) (Rat.ne_of_gt hp)
    change (a.re*a.re+a.im*a.im) * (a.re*a.re+a.im*a.im)⁻¹ = 1 at hcancel
    have hbRe : b.re = a.re * (a.re*a.re+a.im*a.im)⁻¹ := rfl
    have hbIm : b.im = -(a.im * (a.re*a.re+a.im*a.im)⁻¹) := rfl
    have hre : (QComplex.mul a b).re = QComplex.one.re := by
      change a.re*b.re-a.im*b.im=1
      rw [hbRe, hbIm]
      grind
    have him : (QComplex.mul a b).im = QComplex.one.im := by
      change a.re*b.im+a.im*b.re=0
      rw [hbRe, hbIm]
      grind
    cases hab : QComplex.mul a b
    simp [hab, QComplex.one] at hre him ⊢
    exact ⟨hre, him⟩
  change (QBox.mul (z.raw.compute n) ((inverseAt z N h).raw.compute n)).lo ≤ QComplex.mul a b ∧
    QComplex.mul a b ≤ (QBox.mul (z.raw.compute n) ((inverseAt z N h).raw.compute n)).hi at hmul
  rw [heq] at hmul
  exact (ComplexRaw.compareAt_overlap_iff _ _ n n).2 hmul

/-- Every nonzero represented complex number has an exact reciprocal. -/
theorem exists_inverse (z : ComplexCert) (hz : ¬ z.raw.Equiv zero.raw) :
    ∃ w : ComplexCert, (mul z w).raw.Equiv (ofQComplex QComplex.one).raw := by
  obtain ⟨N, hN⟩ := exists_positive_norm_stage z hz
  exact ⟨inverseAt z N hN, mul_inverseAt z N hN⟩

end ComputableAnalysis.RepresentedPolynomial
