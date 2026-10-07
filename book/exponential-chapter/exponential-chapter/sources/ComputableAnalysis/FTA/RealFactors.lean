import ComputableAnalysis.FTA.Algebra
import ComputableAnalysis.ComputableCoefficient

/-! Pairing a represented complex number with its conjugate gives a real
quadratic factor. The proof uses shared rational samples of the input boxes,
so it applies to arbitrary valid real representatives. -/
namespace ComputableAnalysis.RepresentedPolynomial

/-- A complex representative with the supplied real and imaginary parts. -/
def ofParts (u v : Real) : ComplexCert where
  raw := { compute := fun n =>
    { lo := { re := (u.compute n).lo, im := (v.compute n).lo }
      hi := { re := (u.compute n).hi, im := (v.compute n).hi } } }
  valid := by
    constructor
    · intro n
      exact ⟨u.valid.1 n, v.valid.1 n⟩
    · constructor
      · intro n m hnm
        have hu := u.valid.2.1 n m hnm
        have hv := v.valid.2.1 n m hnm
        exact ⟨hu.1, hu.2.2, hv.1, hv.2.2⟩
      · intro eps
        obtain ⟨N, hN⟩ := u.valid.2.2 eps
        obtain ⟨M, hM⟩ := v.valid.2.2 eps
        exact ⟨max N M, fun n hn => ⟨hN n (by omega), hM n (by omega)⟩⟩

def realArgument (x : Real) : ComplexCert where
  raw := ComplexRaw.ofRealRaw x.preferred
  valid := ComplexRaw.ofRealRaw_valid x.preferred x.valid

/-- The normalized real quadratic associated to a conjugate pair. -/
def quadraticValue (u v x : Real) : ComputableCoefficient.Value :=
  let d := ComputableCoefficient.Value.sub (.parameter x) (.parameter u)
  .add (.mul d d) (.mul (.parameter v) (.parameter v))

/-- Exact real quadratic identity for a conjugate pair, at every real argument.
No test deciding whether the imaginary part is zero is performed. -/
theorem conjugate_pair_quadratic (u v x : Real) :
    (mul (sub (realArgument x) (ofParts u v))
      (sub (realArgument x) (conj (ofParts u v)))).raw.Equiv
        (ComplexRaw.ofRealRaw (quadraticValue u v x).real.preferred) := by
  intro n
  let e : Arithmetic.Expression := .mul
    (.add (.parameter (realArgument x)) (.neg (.parameter (ofParts u v))))
    (.add (.parameter (realArgument x)) (.neg (.conj (.parameter (ofParts u v)))))
  let s : ComplexCert → QComplex := fun a => (a.raw.compute n).lo
  have hs : ∀ a, (a.raw.compute n).lo ≤ s a ∧ s a ≤ (a.raw.compute n).hi :=
    fun a => ⟨QComplex.le_refl _, ComplexRaw.valid_ordered a.valid n⟩
  have he := e.contains n s hs
  let t : Real → Rat := fun a => (a.compute n).lo
  have ht := ComputableCoefficient.samples_lower n
  have hq := (quadraticValue u v x).encloses n n
    (by simp [quadraticValue, ComputableCoefficient.Value.add,
      ComputableCoefficient.Value.mul, ComputableCoefficient.Value.sub,
      ComputableCoefficient.Value.neg, ComputableCoefficient.Value.parameter]) t ht
  let q : Rat := ((x.compute n).lo - (u.compute n).lo) *
    ((x.compute n).lo - (u.compute n).lo) + (v.compute n).lo * (v.compute n).lo
  have hsample : e.sample s = { re := q, im := 0 } := by
    simp [e, Arithmetic.Expression.sample, s, realArgument, ofParts,
      ComplexRaw.ofRealRaw, QComplex.add, QComplex.mul, QComplex.neg, QComplex.conj]
    constructor <;> dsimp [q, Real.compute] <;> grind
  have hvalue : (quadraticValue u v x).sample t = q := by
    simp [quadraticValue, ComputableCoefficient.Value.add, ComputableCoefficient.Value.mul,
      ComputableCoefficient.Value.sub, ComputableCoefficient.Value.neg,
      ComputableCoefficient.Value.parameter, q, t]
    grind
  rw [hsample] at he
  rw [hvalue] at hq
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  change QBox.Overlaps (e.value.raw.compute n)
    ((ComplexRaw.ofRealRaw (quadraticValue u v x).real.preferred).compute n)
  change ((e.value.raw.compute n).lo.re ≤ ((quadraticValue u v x).real.compute n).hi ∧
    (e.value.raw.compute n).lo.im ≤ (0 : Rat)) ∧
    (((quadraticValue u v x).real.compute n).lo ≤ (e.value.raw.compute n).hi.re ∧
    (0 : Rat) ≤ (e.value.raw.compute n).hi.im)
  exact ⟨⟨Rat.le_trans he.1.1 hq.2, he.1.2⟩,
    ⟨Rat.le_trans hq.1 he.2.1, he.2.2⟩⟩

end ComputableAnalysis.RepresentedPolynomial
