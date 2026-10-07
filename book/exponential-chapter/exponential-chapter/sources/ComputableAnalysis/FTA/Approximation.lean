import ComputableAnalysis.FTA.Cluster

/-! Bounded approximate roots give exact roots. The coefficients are arbitrary
represented values; finite rational evaluations sample their actual boxes at
increasing stages. The proof derives the limit inside the raw foundation. -/
namespace ComputableAnalysis.RepresentedPolynomial

/-- Rational coefficient samples, using the lower corner of each stage box. -/
def coefficientSamples (p : Coefficients) (k : Nat) : CPoly.Coeffs :=
  p.map fun a => (a.raw.compute k).lo

theorem sample_eval_contains (p : Coefficients) {n k : Nat} (hnk : n ≤ k)
    {B : QBox} {w : QComplex} (hwlo : B.lo ≤ w) (hwhi : w ≤ B.hi) :
    (evalBox (p.map fun a => a.raw.compute n) B).lo ≤
      CPoly.eval (coefficientSamples p k) w ∧
    CPoly.eval (coefficientSamples p k) w ≤
      (evalBox (p.map fun a => a.raw.compute n) B).hi := by
  induction p with
  | nil => exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | cons a p ih =>
      have hn := ComplexRaw.valid_nestedIn a.valid hnk
      have ha := ComplexRaw.valid_ordered a.valid k
      exact QBox.add_contains hn.1 (QComplex.le_trans ha hn.2)
        (QBox.mul_contains hwlo hwhi ih.1 ih.2).1
        (QBox.mul_contains hwlo hwhi ih.1 ih.2).2

private theorem lower_le_zero {a : Rat} {error : Nat → Rat}
    (hshrink : ShrinksToZero error)
    (h : ∀ N, ∃ k, N ≤ k ∧ a ≤ error k) : a ≤ 0 := by
  by_cases ha : a ≤ 0
  · exact ha
  have ha : 0 < a := by grind
  have hhalf : 0 < a / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_pos ha (by decide +kernel)
  obtain ⟨N, hN⟩ := hshrink ⟨a / 2, hhalf⟩
  obtain ⟨k, hk, hak⟩ := h N
  have he := hN k hk
  have hh : a / 2 + a / 2 = a := by
    rw [Rat.div_def]
    have hi : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
    grind
  grind

/-- A cluster point of bounded approximate roots is an exact root, even
though both the sampled argument and the coefficient samples vary. -/
theorem root_of_approximate_cluster (p : Coefficients) (points : Nat → QComplex)
    (error : Nat → Rat) (hshrink : ShrinksToZero error)
    (hsmall : ∀ k,
      qabs (CPoly.eval (coefficientSamples p k) (points k)).re ≤ error k ∧
      qabs (CPoly.eval (coefficientSamples p k) (points k)).im ≤ error k)
    (z : ComplexCert) (hcluster : Clusters points z) : Root p z := by
  apply (root_iff_zero_in_boxes p z).2
  intro n
  let B := evalBox (p.map fun a => a.raw.compute n) (z.raw.compute n)
  have hsample : ∀ N, ∃ k, N ≤ k ∧
      B.lo ≤ CPoly.eval (coefficientSamples p k) (points k) ∧
      CPoly.eval (coefficientSamples p k) (points k) ≤ B.hi := by
    intro N
    obtain ⟨k, hk, hlo, hhi⟩ := hcluster n (max n N)
    exact ⟨k, by omega, sample_eval_contains p (by omega) hlo hhi⟩
  have hloRe : B.lo.re ≤ 0 := by
    apply lower_le_zero hshrink
    intro N
    obtain ⟨k, hk, hlo, _⟩ := hsample N
    exact ⟨k, hk, Rat.le_trans hlo.1 (Rat.le_trans (self_le_qabs _) (hsmall k).1)⟩
  have hloIm : B.lo.im ≤ 0 := by
    apply lower_le_zero hshrink
    intro N
    obtain ⟨k, hk, hlo, _⟩ := hsample N
    exact ⟨k, hk, Rat.le_trans hlo.2 (Rat.le_trans (self_le_qabs _) (hsmall k).2)⟩
  have hhiRe : -B.hi.re ≤ 0 := by
    apply lower_le_zero hshrink
    intro N
    obtain ⟨k, hk, _, hhi⟩ := hsample N
    have hq := neg_qabs_le_self (CPoly.eval (coefficientSamples p k) (points k)).re
    have he := (hsmall k).1
    refine ⟨k, hk, ?_⟩
    have hb := hhi.1
    grind
  have hhiIm : -B.hi.im ≤ 0 := by
    apply lower_le_zero hshrink
    intro N
    obtain ⟨k, hk, _, hhi⟩ := hsample N
    have hq := neg_qabs_le_self (CPoly.eval (coefficientSamples p k) (points k)).im
    have he := (hsmall k).2
    refine ⟨k, hk, ?_⟩
    have hb := hhi.2
    grind
  change (B.lo.re ≤ 0 ∧ B.lo.im ≤ 0) ∧ (0 ≤ B.hi.re ∧ 0 ≤ B.hi.im)
  exact ⟨⟨hloRe, hloIm⟩, ⟨by grind, by grind⟩⟩

/-- An actual exact-root existence theorem from bounded approximate roots.
Nested root boxes and a represented root are conclusions, not assumptions. -/
theorem exists_root_of_bounded_approximations (p : Coefficients)
    (points : Nat → QComplex) (initial : QBox) (hordered : initial.Ordered)
    (hbounded : ∀ k, initial.lo ≤ points k ∧ points k ≤ initial.hi)
    (error : Nat → Rat) (hshrink : ShrinksToZero error)
    (hsmall : ∀ k,
      qabs (CPoly.eval (coefficientSamples p k) (points k)).re ≤ error k ∧
      qabs (CPoly.eval (coefficientSamples p k) (points k)).im ≤ error k) :
    ∃ z : ComplexCert, z.raw.compute 0 = initial ∧ Root p z := by
  obtain ⟨z, hz, hc⟩ := exists_cluster points initial hordered hbounded
  exact ⟨z, hz, root_of_approximate_cluster p points error hshrink hsmall z hc⟩

end ComputableAnalysis.RepresentedPolynomial
