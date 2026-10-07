import ComputableAnalysis.FTA.Coercivity
import ComputableAnalysis.FTA.Normalization
import ComputableAnalysis.FTA.Approximation

/-! A minimum-modulus point constructed from finite rational searches and a
proved box-cluster argument. The search uses actual coefficient samples; its
sublevel bound is uniform over all stages of arbitrary represented inputs. -/
namespace ComputableAnalysis.RepresentedPolynomial
open PolynomialCoercivity

/-- An executable enumeration of all rational complex points. -/
def rationalPoint (n : Nat) : QComplex :=
  let ij := diagonalUnpair n 0
  { re := RationalCode.decode (rationalNatCode ij.1)
    im := RationalCode.decode (rationalNatCode ij.2) }

def rationalPointIndex (z : QComplex) : Nat :=
  diagonalPair (rationalNatIndex z.re) (rationalNatIndex z.im)

theorem rationalPoint_index (z : QComplex) : rationalPoint (rationalPointIndex z) = z := by
  simp only [rationalPoint, rationalPointIndex, diagonalUnpair_diagonalPair,
    rationalNatCode_index, RationalCode.decode_encode]

/-- Finite exhaustive minimization with rational comparisons. -/
def finiteMin (f : QComplex → Rat) (start : QComplex) : List QComplex → QComplex
  | [] => start
  | x :: xs => finiteMin f (if f x ≤ f start then x else start) xs

theorem finiteMin_le_start (f : QComplex → Rat) (xs : List QComplex) (start : QComplex) :
    f (finiteMin f start xs) ≤ f start := by
  induction xs generalizing start with
  | nil => exact Rat.le_refl
  | cons x xs ih =>
      rw [finiteMin]
      split
      · exact Rat.le_trans (ih x) ‹f x ≤ f start›
      · exact ih start

theorem finiteMin_le_mem (f : QComplex → Rat) (xs : List QComplex)
    (start x : QComplex) (hx : x ∈ xs) : f (finiteMin f start xs) ≤ f x := by
  induction xs generalizing start with
  | nil => simp at hx
  | cons a xs ih =>
      have hx' : x = a ∨ x ∈ xs := by simpa using hx
      rcases hx' with rfl | hx'
      · rw [finiteMin]
        split
        · exact finiteMin_le_start f xs x
        · exact Rat.le_trans (finiteMin_le_start f xs start) (by grind)
      · exact ih _ hx'

def sampleNorm (p : Coefficients) (k : Nat) (z : QComplex) : Rat :=
  QComplex.normSq (CPoly.eval (coefficientSamples p k) z)

def minimumCandidate (p : Coefficients) (k : Nat) : QComplex :=
  finiteMin (sampleNorm p k) QComplex.zero ((List.range (k+1)).map rationalPoint)

theorem minimumCandidate_le_zero (p : Coefficients) (k : Nat) :
    sampleNorm p k (minimumCandidate p k) ≤ sampleNorm p k QComplex.zero :=
  finiteMin_le_start _ _ _

theorem minimumCandidate_le_point (p : Coefficients) (z : QComplex)
    (k : Nat) (hk : rationalPointIndex z ≤ k) :
    sampleNorm p k (minimumCandidate p k) ≤ sampleNorm p k z := by
  apply finiteMin_le_mem
  apply List.mem_map.mpr
  exact ⟨rationalPointIndex z, List.mem_range.mpr (by omega), rationalPoint_index z⟩

/-- A uniform bound computed only from the initial coefficient boxes. -/
def coefficientRadius : Coefficients → Rat
  | [] => 0
  | a :: p => 2 * (a.raw.compute 0).coordinateRadius + coefficientRadius p

theorem coefficientRadius_nonneg (p : Coefficients) : 0 ≤ coefficientRadius p := by
  induction p with
  | nil => exact Rat.le_refl
  | cons a p ih =>
      have h := QBox.coordinateRadius_pos (a.raw.compute 0)
      change 0 ≤ 2 * (a.raw.compute 0).coordinateRadius + coefficientRadius p
      grind

theorem coefficientSamples_bound (p : Coefficients) (k : Nat) :
    coefficientBound (coefficientSamples p k) ≤ coefficientRadius p := by
  induction p with
  | nil => exact Rat.le_refl
  | cons a p ih =>
      have h := QBox.coordinateBounded_of_nested (ComplexRaw.valid_ordered a.valid k)
        (ComplexRaw.valid_nestedIn a.valid (Nat.zero_le k))
        (QBox.coordinateBounded_radius (a.raw.compute 0))
      have hr := h.1
      have hi := h.2.2.1
      change QComplex.normBound (a.raw.compute k).lo + coefficientBound (coefficientSamples p k) ≤
        2 * (a.raw.compute 0).coordinateRadius + coefficientRadius p
      unfold QComplex.normBound
      grind

private theorem monic_samples (q : Coefficients) (k : Nat) :
    coefficientSamples (q ++ [one]) k = coefficientSamples q k ++ [QComplex.one] := by
  simp [coefficientSamples, one, ofQComplex, ComplexRaw.ofQComplex]

def minimumRadius (q : Coefficients) : Rat :=
  2 * ((coefficientRadius q + 1)^2 + coefficientRadius q + 2)

theorem minimumRadius_pos (q : Coefficients) : 0 < minimumRadius q := by
  have h := coefficientRadius_nonneg q
  have hs := rat_square_nonneg_basic (coefficientRadius q + 1)
  unfold minimumRadius
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  grind

/-- All finite search minimizers lie in one explicit bounded region. -/
theorem minimumCandidate_bound (q : Coefficients) (hq : 0 < q.length) (k : Nat) :
    QComplex.normBound (minimumCandidate (q ++ [one]) k) ≤ minimumRadius q := by
  let C := coefficientRadius q
  have hC : 0 ≤ C := coefficientRadius_nonneg q
  have hcoeff := coefficientSamples_bound q k
  have hz := eval_normBound_on_unit (coefficientSamples (q++[one]) k) QComplex.zero
    (by decide +kernel)
  rw [monic_samples, coefficientBound_append] at hz
  have hone : coefficientBound [QComplex.one] = 1 := by decide +kernel
  rw [hone] at hz
  have hzero : QComplex.normSq (CPoly.eval (coefficientSamples (q++[one]) k) QComplex.zero) ≤ (C+1)^2 := by
    have hn := normSq_le_normBound_square (CPoly.eval (coefficientSamples (q++[one]) k) QComplex.zero)
    have he : QComplex.normBound (CPoly.eval (coefficientSamples (q++[one]) k) QComplex.zero) ≤ C+1 := by
      rw [monic_samples]
      grind
    have h0 := QComplex.normBound_nonneg (CPoly.eval (coefficientSamples (q++[one]) k) QComplex.zero)
    have h1 := Rat.mul_le_mul_of_nonneg_left he h0
    have h2 := Rat.mul_le_mul_of_nonneg_right he (show 0 ≤ C+1 by grind)
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    grind
  have hmin := minimumCandidate_le_zero (q++[one]) k
  have hn := normBound_le_normSq_add_one
    (CPoly.eval (coefficientSamples (q++[one]) k) (minimumCandidate (q++[one]) k))
  have heval : QComplex.normBound
      (CPoly.eval (coefficientSamples q k ++ [QComplex.one]) (minimumCandidate (q++[one]) k)) ≤
        (C+1)^2 + 1 := by
    rw [← monic_samples]
    unfold sampleNorm at hmin
    grind
  have hM : 0 ≤ (C+1)^2+1 := by
    have hs := Rat.pow_nonneg (show 0 ≤ C+1 by grind) (n := 2)
    grind
  have hb := monic_sublevel_bound (coefficientSamples q k)
    (by simpa [coefficientSamples] using hq)
    (minimumCandidate (q++[one]) k) ((C+1)^2+1) hM heval
  unfold minimumRadius
  grind

/-- Norm-square evaluation encloses the squared norm of every point in the
input box. The coordinate copies use the same rational point. -/
theorem normValue_contains (z : ComplexCert) (n : Nat) (w : QComplex)
    (hlo : (z.raw.compute n).lo ≤ w) (hhi : w ≤ (z.raw.compute n).hi) :
    ((normValue z).real.compute n).lo ≤ QComplex.normSq w ∧
      QComplex.normSq w ≤ ((normValue z).real.compute n).hi := by
  have hr := QBox.mulRealInterval_contains hlo.1 hhi.1 hlo.1 hhi.1
  have hi := QBox.mulRealInterval_contains hlo.2 hhi.2 hlo.2 hhi.2
  change (QBox.mulRealInterval (z.raw.compute n).lo.re (z.raw.compute n).hi.re
      (z.raw.compute n).lo.re (z.raw.compute n).hi.re).lo +
    (QBox.mulRealInterval (z.raw.compute n).lo.im (z.raw.compute n).hi.im
      (z.raw.compute n).lo.im (z.raw.compute n).hi.im).lo ≤ w.re*w.re+w.im*w.im ∧
    w.re*w.re+w.im*w.im ≤
      (QBox.mulRealInterval (z.raw.compute n).lo.re (z.raw.compute n).hi.re
        (z.raw.compute n).lo.re (z.raw.compute n).hi.re).hi +
      (QBox.mulRealInterval (z.raw.compute n).lo.im (z.raw.compute n).hi.im
        (z.raw.compute n).lo.im (z.raw.compute n).hi.im).hi
  exact ⟨rat_add_le_add hr.1 hi.1, rat_add_le_add hr.2 hi.2⟩

/-- A monic nonconstant polynomial has a represented point whose squared
modulus is no larger than its squared modulus at any rational complex point.
The minimum is constructed from the finite search above. -/
theorem exists_minimum_against_rational (q : Coefficients) (hq : 0 < q.length) :
    ∃ z : ComplexCert, ∀ y : QComplex,
      (normValue (eval (q++[one]) z)).real.preferred.Le
        (normValue (eval (q++[one]) (ofQComplex y))).real.preferred := by
  let R := minimumRadius q
  let B : QBox := { lo := { re := -R, im := -R }, hi := { re := R, im := R } }
  have hR : 0 < R := minimumRadius_pos q
  have hB : B.Ordered := by constructor <;> change -R ≤ R <;> grind
  have hbound : ∀ k, B.lo ≤ minimumCandidate (q++[one]) k ∧ minimumCandidate (q++[one]) k ≤ B.hi := by
    intro k
    have h := minimumCandidate_bound q hq k
    have hr := qabs_nonneg (minimumCandidate (q++[one]) k).re
    have hi := qabs_nonneg (minimumCandidate (q++[one]) k).im
    have hlr := neg_qabs_le_self (minimumCandidate (q++[one]) k).re
    have hhr := self_le_qabs (minimumCandidate (q++[one]) k).re
    have hli := neg_qabs_le_self (minimumCandidate (q++[one]) k).im
    have hhi := self_le_qabs (minimumCandidate (q++[one]) k).im
    change qabs (minimumCandidate (q++[one]) k).re + qabs (minimumCandidate (q++[one]) k).im ≤ R at h
    change (-R ≤ _ ∧ -R ≤ _) ∧ (_ ≤ R ∧ _ ≤ R)
    constructor <;> constructor <;> grind
  obtain ⟨z, _, hz⟩ := exists_cluster (minimumCandidate (q++[one])) B hB hbound
  refine ⟨z, ?_⟩
  intro y n m
  obtain ⟨k, hk, hlo, hhi⟩ := hz n (max (max n m) (rationalPointIndex y))
  have hc := sample_eval_contains (q++[one]) (show n ≤ k by omega) hlo hhi
  rw [← eval_compute] at hc
  have hcN := normValue_contains (eval (q++[one]) z) n _ hc.1 hc.2
  have hy := sample_eval_contains (q++[one]) (show m ≤ k by omega)
    (B := QBox.point y) (QComplex.le_refl y) (QComplex.le_refl y)
  have hy' : ((eval (q++[one]) (ofQComplex y)).raw.compute m).lo ≤
      CPoly.eval (coefficientSamples (q++[one]) k) y ∧
      CPoly.eval (coefficientSamples (q++[one]) k) y ≤
        ((eval (q++[one]) (ofQComplex y)).raw.compute m).hi := by
    rw [eval_compute]
    exact hy
  have hyN := normValue_contains (eval (q++[one]) (ofQComplex y)) m _ hy'.1 hy'.2
  have hmin := minimumCandidate_le_point (q++[one]) y k (by omega)
  exact Rat.le_trans hcN.1 (Rat.le_trans hmin hyN.2)

/-- Horner interval evaluation preserves refinement of the argument box. -/
theorem eval_compute_nested_input (p : Coefficients) (a b : ComplexCert) (n : Nat)
    (hab : (a.raw.compute n).NestedIn (b.raw.compute n)) :
    ((eval p a).raw.compute n).NestedIn ((eval p b).raw.compute n) := by
  induction p with
  | nil => exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | cons c p ih =>
      have hm := QBox.mul_nested (ComplexRaw.valid_ordered a.valid n)
        (ComplexRaw.valid_ordered (eval p a).valid n) hab ih
      change (QBox.add (c.raw.compute n) (QBox.mul (a.raw.compute n) ((eval p a).raw.compute n))).NestedIn
        (QBox.add (c.raw.compute n) (QBox.mul (b.raw.compute n) ((eval p b).raw.compute n)))
      exact ⟨⟨Rat.add_le_add_left.mpr hm.1.1, Rat.add_le_add_left.mpr hm.1.2⟩,
        ⟨Rat.add_le_add_left.mpr hm.2.1, Rat.add_le_add_left.mpr hm.2.2⟩⟩

/-- The norm-square interval also preserves input-box refinement. -/
theorem normValue_compute_nested (a b : ComplexCert) (n : Nat)
    (hab : (a.raw.compute n).NestedIn (b.raw.compute n)) :
    ((normValue b).real.compute n).lo ≤ ((normValue a).real.compute n).lo ∧
      ((normValue a).real.compute n).hi ≤ ((normValue b).real.compute n).hi := by
  have ho := ComplexRaw.valid_ordered a.valid n
  have hr := QBox.mulRealInterval_nested hab.1.1 ho.1 hab.2.1 hab.1.1 ho.1 hab.2.1
  have hi := QBox.mulRealInterval_nested hab.1.2 ho.2 hab.2.2 hab.1.2 ho.2 hab.2.2
  exact ⟨rat_add_le_add hr.1 hi.1, rat_add_le_add hr.2 hi.2⟩

/-- A monic nonconstant polynomial attains its minimum squared modulus over
all represented complex arguments. This is derived from rational searches,
explicit coefficient bounds, and nested boxes in the raw foundation. -/
theorem exists_minimum_modulus (q : Coefficients) (hq : 0 < q.length) :
    ∃ z : ComplexCert, ∀ w : ComplexCert,
      (normValue (eval (q++[one]) z)).real.preferred.Le
        (normValue (eval (q++[one]) w)).real.preferred := by
  obtain ⟨z, hz⟩ := exists_minimum_against_rational q hq
  refine ⟨z, ?_⟩
  intro w n m
  let y := (w.raw.compute m).lo
  have hb : ((ofQComplex y).raw.compute m).NestedIn (w.raw.compute m) :=
    ⟨QComplex.le_refl _, ComplexRaw.valid_ordered w.valid m⟩
  have he := eval_compute_nested_input (q++[one]) (ofQComplex y) w m hb
  have hn := normValue_compute_nested _ _ m he
  exact Rat.le_trans (hz y n m) hn.2

end ComputableAnalysis.RepresentedPolynomial
