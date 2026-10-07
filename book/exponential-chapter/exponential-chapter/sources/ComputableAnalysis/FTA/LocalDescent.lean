import ComputableAnalysis.FTA.Minimizer
import ComputableAnalysis.FTA.RepresentedDirection
import ComputableAnalysis.FTA.DomainDescentStep

/-! Lifting the finite strict-decrease estimate to arbitrary represented
coefficients. Every chosen step has a positive rational margin, and the final
comparison is certified by finite norm enclosures. -/
namespace ComputableAnalysis.RepresentedPolynomial
open Arithmetic

private theorem qext {a b : QComplex} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

/-- A uniform Horner bound over a rational norm ball. -/
def evaluationBound : Coefficients → Rat → Rat
  | [], _ => 0
  | a::p, D => coefficientRadius [a] + D * evaluationBound p D

theorem evaluationBound_nonneg (p : Coefficients) {D : Rat} (hD : 0 ≤ D) :
    0 ≤ evaluationBound p D := by
  induction p with
  | nil => exact Rat.le_refl
  | cons a p ih => exact Rat.add_nonneg (coefficientRadius_nonneg [a]) (Rat.mul_nonneg hD ih)

private theorem sample_norm_bound (a : ComplexCert) (m : Nat) :
    QComplex.normBound (a.raw.compute m).lo ≤ coefficientRadius [a] := by
  have h := coefficientSamples_bound [a] m
  change QComplex.normBound (a.raw.compute m).lo + 0 ≤ coefficientRadius [a] at h
  grind

theorem sample_evaluationBound (p : Coefficients) (m : Nat) (z : QComplex) {D : Rat}
    (hD : 0 ≤ D) (hz : QComplex.normBound z ≤ D) :
    QComplex.normBound (CPoly.eval (coefficientSamples p m) z) ≤ evaluationBound p D := by
  induction p with
  | nil => change QComplex.normBound QComplex.zero ≤ 0; decide +kernel
  | cons a p ih =>
      have hc := sample_norm_bound a m
      have hm := QComplex.normBound_mul_le z (CPoly.eval (coefficientSamples p m) z)
      have h1 := Rat.mul_le_mul_of_nonneg_right hz
        (QComplex.normBound_nonneg (CPoly.eval (coefficientSamples p m) z))
      have h2 := Rat.mul_le_mul_of_nonneg_left ih hD
      have hs := QComplex.normBound_add_le (a.raw.compute m).lo
        (QComplex.mul z (CPoly.eval (coefficientSamples p m) z))
      change QComplex.normBound (QComplex.add (a.raw.compute m).lo
        (QComplex.mul z (CPoly.eval (coefficientSamples p m) z))) ≤
        coefficientRadius [a]+D*evaluationBound p D
      grind

def localValue (c a : ComplexCert) (q : Coefficients) (k : Nat) (h : QComplex) : ComplexCert :=
  add c (mul (ofQComplex (QComplex.pow h k))
    (add a (mul (ofQComplex h) (eval q (ofQComplex h)))))

private theorem localValue_contains (c a : ComplexCert) (q : Coefficients) (k : Nat)
    (h : QComplex) (m : Nat) :
    let v := QComplex.add (c.raw.compute m).lo (QComplex.mul (QComplex.pow h k)
      (QComplex.add (a.raw.compute m).lo (QComplex.mul h (CPoly.eval (coefficientSamples q m) h))))
    ((localValue c a q k h).raw.compute m).lo ≤ v ∧
      v ≤ ((localValue c a q k h).raw.compute m).hi := by
  have hq := sample_eval_contains q (Nat.le_refl m)
    (B := QBox.point h) (QComplex.le_refl h) (QComplex.le_refl h)
  have hq' : ((eval q (ofQComplex h)).raw.compute m).lo ≤ CPoly.eval (coefficientSamples q m) h ∧
      CPoly.eval (coefficientSamples q m) h ≤ ((eval q (ofQComplex h)).raw.compute m).hi := by
    rw [eval_compute]
    exact hq
  have hh := QBox.mul_contains (A := QBox.point h) (QComplex.le_refl h) (QComplex.le_refl h) hq'.1 hq'.2
  have ha := QBox.add_contains (QComplex.le_refl (a.raw.compute m).lo) (ComplexRaw.valid_ordered a.valid m) hh.1 hh.2
  have hp := QBox.mul_contains (A := QBox.point (QComplex.pow h k))
    (QComplex.le_refl _) (QComplex.le_refl _) ha.1 ha.2
  exact QBox.add_contains (QComplex.le_refl (c.raw.compute m).lo) (ComplexRaw.valid_ordered c.valid m) hp.1 hp.2

private theorem qpow_scale (t : Rat) (d : QComplex) (k : Nat) :
    QComplex.pow (QComplex.scaleRat t d) k = QComplex.scaleRat (t^k) (QComplex.pow d k) := by
  induction k with
  | zero => simp [QComplex.pow, Rat.pow_zero, QComplex.scaleRat, Rat.one_mul]
  | succ k ih =>
      rw [QComplex.pow, ih, QComplex.pow, Rat.pow_succ]
      simp only [QComplex.mul, QComplex.scaleRat]
      apply qext <;> grind

private theorem pow_pos {t : Rat} (ht : 0 < t) (k : Nat) : 0 < t^k := by
  induction k with
  | zero => rw [Rat.pow_zero]; decide +kernel
  | succ k ih => rw [Rat.pow_succ]; exact Rat.mul_pos ih ht

private theorem conj_nonzero (c : ComplexCert) (hc : ¬ c.raw.Equiv zero.raw) :
    ¬ (conj c).raw.Equiv zero.raw := by
  intro h
  apply hc
  intro n
  have hh := (ComplexRaw.compareAt_overlap_iff _ _ n n).1 (h n)
  change ((c.raw.compute n).lo.re ≤ 0 ∧ -(c.raw.compute n).hi.im ≤ 0) ∧
    (0 ≤ (c.raw.compute n).hi.re ∧ 0 ≤ -(c.raw.compute n).lo.im) at hh
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  change ((c.raw.compute n).lo.re ≤ 0 ∧ (c.raw.compute n).lo.im ≤ 0) ∧
    (0 ≤ (c.raw.compute n).hi.re ∧ 0 ≤ (c.raw.compute n).hi.im)
  constructor <;> constructor <;> grind

/-- An expansion with a nonzero constant and a nonzero first varying
coefficient admits a rational step with a strictly smaller squared modulus.
The result includes finite endpoint separation, not just a formal expansion. -/
theorem exists_local_decrease_within (radius : QPos) (c a : ComplexCert) (q : Coefficients) (k : Nat)
    (hc : ¬ c.raw.Equiv zero.raw) (ha : ¬ a.raw.Equiv zero.raw) (hk : 0 < k) :
    ∃ h : QComplex, QComplex.normBound h ≤ radius.val ∧ ∃ n : Nat,
      ((normValue (localValue c a q k h)).real.compute n).hi < ((normValue c).real.compute n).lo := by
  let g := mul (conj c) a
  have hg : ¬ g.raw.Equiv zero.raw := mul_nonzero (conj_nonzero c hc) ha
  obtain ⟨d, N, hN⟩ := exists_represented_negative_direction g hg k hk
  let D := QComplex.pow d k
  let δ := -((mul g (ofQComplex D)).raw.compute N).hi.re
  have hδ : 0 < δ := by
    change ((mul g (ofQComplex D)).raw.compute N).hi.re < 0 at hN
    dsimp [δ]
    grind
  let C := coefficientRadius [c]
  let A := coefficientRadius [a] * QComplex.normBound D
  let R := QComplex.normBound D * QComplex.normBound d * evaluationBound q (QComplex.normBound d)
  have hC : 0 ≤ C := coefficientRadius_nonneg [c]
  have hA : 0 ≤ A := Rat.mul_nonneg (coefficientRadius_nonneg [a]) (QComplex.normBound_nonneg D)
  have hR : 0 ≤ R := Rat.mul_nonneg
    (Rat.mul_nonneg (QComplex.normBound_nonneg D) (QComplex.normBound_nonneg d))
    (evaluationBound_nonneg q (QComplex.normBound_nonneg d))
  let t := PolynomialDescentDomain.combinedStep δ C A R radius d
  have hts := PolynomialDescentDomain.combinedStep_spec δ C A R hδ radius d
  have ht : 0 < t := hts.1
  have htle : t ≤ PolynomialNormDescent.step δ C A R := hts.2.1
  have hbase := PolynomialDescent.step_spec (-2*δ) [2*C*R+(A+R)^2] (by grind)
  have ht1 : t < 1 := by
    have hs : PolynomialNormDescent.step δ C A R < 1 := hbase.2.1
    grind
  let h := QComplex.scaleRat t d
  have hh : QComplex.normBound h ≤ QComplex.normBound d := by
    rw [QComplex.normBound_scaleRat, qabs_eq_self_of_nonneg (Rat.le_of_lt ht)]
    have hm := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ht1) (QComplex.normBound_nonneg d)
    grind
  let e := localValue c a q k h
  have hdecrease : ∀ m, N ≤ m →
      let cm := (c.raw.compute m).lo
      let am := (a.raw.compute m).lo
      let qm := CPoly.eval (coefficientSamples q m) h
      QComplex.normSq (QComplex.add cm (QComplex.mul (QComplex.pow h k)
        (QComplex.add am (QComplex.mul h qm)))) ≤ QComplex.normSq cm-t^k*δ := by
    intro m hNm
    let cm := (c.raw.compute m).lo
    let am := (a.raw.compute m).lo
    let qm := CPoly.eval (coefficientSamples q m) h
    let av := QComplex.mul am D
    let rv := QComplex.mul D (QComplex.mul d qm)
    have hcm : QComplex.normBound cm ≤ C := sample_norm_bound c m
    have ham := sample_norm_bound a m
    have hqm := sample_evaluationBound q m h (QComplex.normBound_nonneg d) hh
    have hav : QComplex.normBound av ≤ A := by
      have hmul := QComplex.normBound_mul_le am D
      have hmul' := Rat.mul_le_mul_of_nonneg_right ham (QComplex.normBound_nonneg D)
      change QComplex.normBound (QComplex.mul am D) ≤ coefficientRadius [a]*QComplex.normBound D
      grind
    have hrv : QComplex.normBound rv ≤ R := by
      have h1 := QComplex.normBound_mul_le D (QComplex.mul d qm)
      have h2 := QComplex.normBound_mul_le d qm
      have h3 := Rat.mul_le_mul_of_nonneg_left hqm (QComplex.normBound_nonneg d)
      have h4 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans h2 h3) (QComplex.normBound_nonneg D)
      change QComplex.normBound (QComplex.mul D (QComplex.mul d qm)) ≤
        QComplex.normBound D*QComplex.normBound d*evaluationBound q (QComplex.normBound d)
      grind
    have hdir : (QComplex.mul (QComplex.conj cm) av).re ≤ -δ := by
      let expr : Expression := .mul (.mul (.conj (.parameter c)) (.parameter a)) (.constant D)
      let s : ComplexCert → QComplex := fun b => (b.raw.compute m).lo
      have hs : ∀ b, (b.raw.compute N).lo ≤ s b ∧ s b ≤ (b.raw.compute N).hi := by
        intro b
        have hn := ComplexRaw.valid_nestedIn b.valid hNm
        exact ⟨hn.1, QComplex.le_trans (ComplexRaw.valid_ordered b.valid m) hn.2⟩
      have he := (expr.contains N s hs).2.1
      have heq : expr.sample s = QComplex.mul (QComplex.conj cm) av := QComplex.mul_assoc_cert _ _ _
      rw [heq] at he
      change (QComplex.mul (QComplex.conj cm) av).re ≤ -(-((mul g (ofQComplex D)).raw.compute N).hi.re)
      change (QComplex.mul (QComplex.conj cm) av).re ≤ ((mul g (ofQComplex D)).raw.compute N).hi.re at he
      grind
    have hfinite := (PolynomialNormDescent.decrease_at_smaller_step cm av rv δ C A R t k hδ hC hA hR hk hcm hav hrv hdir ht htle).2
    have heq : QComplex.add cm (QComplex.mul (QComplex.pow h k) (QComplex.add am (QComplex.mul h qm))) =
        QComplex.add cm (QComplex.scaleRat (t^k) (QComplex.add av (QComplex.scaleRat t rv))) := by
      rw [show h = QComplex.scaleRat t d from rfl, qpow_scale]
      simp only [QComplex.add, QComplex.mul, QComplex.scaleRat, av, rv]
      apply qext <;> dsimp [D] <;> grind
    change QComplex.normSq (QComplex.add cm (QComplex.mul (QComplex.pow h k) (QComplex.add am (QComplex.mul h qm)))) ≤
      QComplex.normSq cm-t^k*δ
    rw [heq]
    exact hfinite
  have hη : 0 < t^k*δ := Rat.mul_pos (pow_pos ht k) hδ
  have hε : 0 < (t^k*δ)/4 := by
    rw [Rat.div_def]
    exact Rat.mul_pos hη (by decide +kernel)
  obtain ⟨L, hL⟩ := (normValue e).real.valid.2.2 ⟨(t^k*δ)/4, hε⟩
  obtain ⟨M, hM⟩ := (normValue c).real.valid.2.2 ⟨(t^k*δ)/4, hε⟩
  let n := max N (max L M)
  have hdec := hdecrease n (by dsimp [n]; omega)
  have he := localValue_contains c a q k h n
  have hen := normValue_contains e n _ he.1 he.2
  have hcn := normValue_contains c n (c.raw.compute n).lo (QComplex.le_refl _) (ComplexRaw.valid_ordered c.valid n)
  have hwe := hL n (by dsimp [n]; omega)
  have hwc := hM n (by dsimp [n]; omega)
  have hquarter : 4*((t^k*δ)/4)=t^k*δ := by
    rw [Rat.div_def]
    have : (4 : Rat)*(4 : Rat)⁻¹=1 := by decide +kernel
    grind
  refine ⟨h, hts.2.2, n, ?_⟩
  change ((normValue e).real.compute n).hi - ((normValue e).real.compute n).lo ≤ (t^k*δ)/4 at hwe
  change ((normValue c).real.compute n).hi - ((normValue c).real.compute n).lo ≤ (t^k*δ)/4 at hwc
  change ((normValue e).real.compute n).hi < ((normValue c).real.compute n).lo
  dsimp only at hdec
  grind

/-- The original unrestricted local-decrease statement, now derived from the
arbitrarily small displacement theorem. -/
theorem exists_local_decrease (c a : ComplexCert) (q : Coefficients) (k : Nat)
    (hc : ¬ c.raw.Equiv zero.raw) (ha : ¬ a.raw.Equiv zero.raw) (hk : 0 < k) :
    ∃ h : QComplex, ∃ n : Nat,
      ((normValue (localValue c a q k h)).real.compute n).hi < ((normValue c).real.compute n).lo := by
  obtain ⟨h, _, n, hn⟩ := exists_local_decrease_within ⟨1, by decide +kernel⟩ c a q k hc ha hk
  exact ⟨h, n, hn⟩

end ComputableAnalysis.RepresentedPolynomial
