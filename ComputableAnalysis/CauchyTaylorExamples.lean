import ComputableAnalysis.CauchyTaylorDisk

/-! Concrete, assumption-free instances of the conditional reconstruction
theorem. A fixed finite Cauchy rule is a rational function, not a general
holomorphic input. These examples test the construction without claiming the
missing general Cauchy formula. -/

namespace ComputableAnalysis.CauchyTaylor

open QComplex

def ofRule (ps : Rule) : SeriesCertificate (fun z => ComplexRaw.ofQComplex (cauchySample ps z)) where
  cauchy := {
    rules := fun _ => ps
    massBound := mass ps
    mass_nonneg := mass_nonneg ps
    mass_le := fun _ => Rat.le_refl
    quadratureBound := fun _ => 0
    quadrature_nonneg := fun _ => Rat.le_refl
    valid := fun z _ _ _ _ => ComplexRaw.ofQComplex_valid _
    encloses := by
      intro z r hr hr1 hz n
      simp only [QBox.NestedIn, QBox.expand, QBox.point, ComplexRaw.ofQComplex,
        CertifiedComplexApproximation.rate, QComplex.le_def, Rat.div_def,
        Rat.zero_mul, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
      grind only }
  moments := {
    bound := fun _ => 0
    nonneg := fun _ => Rat.le_refl
    future := by
      intro k i j hij
      simp only [normBound, sub, add, neg, CertifiedComplexApproximation.rate, Rat.div_def,
        Rat.zero_mul]
      simp [qabs, Rat.add_neg_cancel, Rat.add_zero] }

private theorem unit_coordinate (z : QComplex) : add zero (scaleRat 1 z) = z := by
  cases z; simp [add, zero, scaleRat, Rat.one_mul, Rat.zero_add]

def unitDisk (ps : Rule) : Disk where
  center := zero
  radius := 1
  radius_pos := by decide
  function := fun z => ComplexRaw.ofQComplex (cauchySample ps z)
  certificate := by
    simpa only [unit_coordinate] using ofRule ps

def reciprocalRule : Rule := [⟨one, by native_decide, one⟩]

theorem reciprocal_sample (z : QComplex) : cauchySample reciprocalRule z = kernel z := by
  simp only [cauchySample, reciprocalRule, List.foldr_cons, List.foldr_nil,
    mul_one_cert, one_mul_cert, add_zero_cert]

/-- Exact geometric-series equality on the full complex unit disk. -/
theorem reciprocal_eq_series (z : QComplex) (hz : normSq z < 1) :
    (ComplexRaw.ofQComplex (inverse (sub one z))).Equiv ((unitDisk reciprocalRule).series z) := by
  have hs : sub z zero = z := by
    cases z; simp [sub, add, neg, zero, Rat.add_zero]
  have he := (unitDisk reciprocalRule).eq_series
    (z := z) (by simpa only [unitDisk, hs, Rat.mul_one] using hz)
  simpa only [unitDisk, reciprocal_sample, kernel] using he

theorem reciprocal_coefficient_sample (n k : Nat) :
    coefficientSample ((ofRule reciprocalRule).cauchy.rules n) k = one := by
  have hp : natPow one k = one := by
    induction k with
    | zero => rfl
    | succ k ih => rw [natPow, ih, mul_one_cert]
  simp only [ofRule, coefficientSample, reciprocalRule, List.foldr_cons, List.foldr_nil,
    hp, one_mul_cert, add_zero_cert]

theorem reciprocal_coefficients (k : Nat) :
    ((ofRule reciprocalRule).coefficient k).Equiv (ComplexRaw.ofQComplex one) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  have h := (ofRule reciprocalRule).moments.coefficient_contains_sample k n
  rw [reciprocal_coefficient_sample] at h
  simp only [QBox.NestedIn, QBox.Overlaps, QBox.point, ComplexRaw.ofQComplex,
    QComplex.le_def] at *
  grind only [SeriesCertificate.coefficient]

/-- This point is outside the normBound diamond `|re|+|im| < 1`.
The theorem still covers it because its radius is Euclidean. -/
theorem diagonal_point_eq_series :
    (ComplexRaw.ofQComplex ⟨10/13, 15/13⟩).Equiv
      ((unitDisk reciprocalRule).series ⟨3/5, 3/5⟩) := by
  have h := reciprocal_eq_series ⟨3/5, 3/5⟩ (by native_decide)
  have he : inverse (sub one ⟨3/5, 3/5⟩) = ⟨10/13, 15/13⟩ := by native_decide
  rw [he] at h
  exact h

end ComputableAnalysis.CauchyTaylor
