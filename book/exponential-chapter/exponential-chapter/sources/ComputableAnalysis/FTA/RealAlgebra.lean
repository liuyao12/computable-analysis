import ComputableAnalysis.FTA.RootExistence

/-! Real coefficients and exact algebra used for real factorization. -/
namespace ComputableAnalysis.RepresentedPolynomial
open Arithmetic

theorem certRefl (a : ComplexCert) : a.raw.Equiv a.raw := ComplexRaw.equiv_refl _ a.valid

theorem certTrans {a b c : ComplexCert} (hab : a.raw.Equiv b.raw) (hbc : b.raw.Equiv c.raw) :
    a.raw.Equiv c.raw := ComplexRaw.equiv_trans a.valid b.valid c.valid hab hbc

theorem certAddCongr {a b c d : ComplexCert} (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (add a c).raw.Equiv (add b d).raw := ComplexRaw.add_equiv hab hcd

theorem certMulCongr {a b c d : ComplexCert} (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (mul a c).raw.Equiv (mul b d).raw :=
  ComplexRaw.mul_equiv a.valid b.valid c.valid d.valid hab hcd

theorem certConjCongr {a b : ComplexCert} (hab : a.raw.Equiv b.raw) :
    (conj a).raw.Equiv (conj b).raw := ComplexRaw.conj_equiv hab

theorem certNegCongr {a b : ComplexCert} (hab : a.raw.Equiv b.raw) :
    (neg a).raw.Equiv (neg b).raw := ComplexRaw.neg_equiv hab

theorem certSubCongr {a b c d : ComplexCert} (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (sub a c).raw.Equiv (sub b d).raw := certAddCongr hab (certNegCongr hcd)

private theorem qext {a b : QComplex} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

theorem certMulZero (a : ComplexCert) : (mul a zero).raw.Equiv zero.raw := by
  apply Expression.equiv_of_samples (.mul (.parameter a) (.constant QComplex.zero)) (.constant QComplex.zero)
  intro s
  apply qext <;> simp [Expression.sample, QComplex.mul, QComplex.zero] <;> grind

theorem certOneMul (a : ComplexCert) : (mul one a).raw.Equiv a.raw := by
  apply Expression.equiv_of_samples (.mul (.constant QComplex.one) (.parameter a)) (.parameter a)
  intro s
  exact QComplex.one_mul_cert _

theorem certMulOne (a : ComplexCert) : (mul a one).raw.Equiv a.raw := by
  apply Expression.equiv_of_samples (.mul (.parameter a) (.constant QComplex.one)) (.parameter a)
  intro s
  exact QComplex.mul_one_cert _

theorem certOneNonzero : ¬ one.raw.Equiv zero.raw := by
  intro h
  have hh := (ComplexRaw.compareAt_overlap_iff _ _ 0 0).1 (h 0)
  have hb : (1 : Rat) ≤ 0 := hh.1.1
  contradiction

theorem certSubEqZero {a b : ComplexCert} (h : (sub a b).raw.Equiv zero.raw) : a.raw.Equiv b.raw := by
  have heq : (add (sub a b) b).raw.Equiv a.raw := by
    apply Expression.equiv_of_samples (.add (.add (.parameter a) (.neg (.parameter b))) (.parameter b)) (.parameter a)
    intro s
    apply qext <;> simp [Expression.sample, QComplex.add, QComplex.neg] <;> grind
  exact certTrans (ComplexRaw.equiv_symm heq) (certTrans (certAddCongr h (certRefl b)) (zero_add b))

/-- A complex representative is real when conjugation fixes its value. -/
def IsReal (a : ComplexCert) : Prop := (conj a).raw.Equiv a.raw

namespace IsReal

theorem zero : IsReal RepresentedPolynomial.zero := conj_zero

theorem one : IsReal RepresentedPolynomial.one := by
  apply Expression.equiv_of_samples (.conj (.constant QComplex.one)) (.constant QComplex.one)
  intro s
  change QComplex.conj QComplex.one = QComplex.one
  decide +kernel

theorem add {a b : ComplexCert} (ha : IsReal a) (hb : IsReal b) :
    IsReal (RepresentedPolynomial.add a b) := certTrans (conj_add a b) (certAddCongr ha hb)

theorem mul {a b : ComplexCert} (ha : IsReal a) (hb : IsReal b) :
    IsReal (RepresentedPolynomial.mul a b) := certTrans (conj_mul a b) (certMulCongr ha hb)

theorem neg {a : ComplexCert} (ha : IsReal a) : IsReal (RepresentedPolynomial.neg a) := by
  have he : (conj (RepresentedPolynomial.neg a)).raw.Equiv (RepresentedPolynomial.neg (conj a)).raw := by
    apply Expression.equiv_of_samples (.conj (.neg (.parameter a))) (.neg (.conj (.parameter a)))
    intro s
    rfl
  exact certTrans he (certNegCongr ha)

theorem sub {a b : ComplexCert} (ha : IsReal a) (hb : IsReal b) :
    IsReal (RepresentedPolynomial.sub a b) := add ha (neg hb)

theorem of_equiv {a b : ComplexCert} (ha : IsReal a) (hab : a.raw.Equiv b.raw) : IsReal b :=
  certTrans (b := conj a) (ComplexRaw.conj_equiv (ComplexRaw.equiv_symm hab)) (certTrans (a := conj a) (b := a) ha hab)

theorem realArgument (a : Real) : IsReal (RepresentedPolynomial.realArgument a) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  have ha := RealRaw.interval_order_of_valid _ a.valid n
  change (a.compute n).lo ≤ (a.compute n).hi at ha
  change ((a.compute n).lo ≤ (a.compute n).hi ∧ -0 ≤ (0 : Rat)) ∧
    ((a.compute n).lo ≤ (a.compute n).hi ∧ (0 : Rat) ≤ -0)
  constructor <;> constructor <;> grind

/-- A real complex representative agrees exactly with the embedding of its
real coordinate. -/
theorem projection {a : ComplexCert} (ha : IsReal a) :
    a.raw.Equiv (RepresentedPolynomial.realArgument (realCoordinate a)).raw := by
  intro n
  have hh := (ComplexRaw.compareAt_overlap_iff _ _ n n).1 (ha n)
  have ho := ComplexRaw.valid_ordered a.valid n
  change ((a.raw.compute n).lo.re ≤ (a.raw.compute n).hi.re ∧
      -(a.raw.compute n).hi.im ≤ (a.raw.compute n).hi.im) ∧
    ((a.raw.compute n).lo.re ≤ (a.raw.compute n).hi.re ∧
      (a.raw.compute n).lo.im ≤ -(a.raw.compute n).lo.im) at hh
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  change ((a.raw.compute n).lo.re ≤ (a.raw.compute n).hi.re ∧ (a.raw.compute n).lo.im ≤ 0) ∧
    ((a.raw.compute n).lo.re ≤ (a.raw.compute n).hi.re ∧ 0 ≤ (a.raw.compute n).hi.im)
  constructor <;> constructor <;> grind

theorem imag_zero {a : ComplexCert} (ha : IsReal a) :
    (imagCoordinate a).preferred.Equiv RealRaw.zero :=
  ComplexRaw.imagPart_equiv (projection ha)

end IsReal

theorem conj_conj (a : ComplexCert) : (conj (conj a)).raw.Equiv a.raw := by
  apply Expression.equiv_of_samples (.conj (.conj (.parameter a))) (.parameter a)
  intro s
  apply qext <;> simp [Expression.sample, QComplex.conj]

theorem isReal_of_conj_real {a : ComplexCert} (ha : IsReal (conj a)) : IsReal a :=
  IsReal.of_equiv (certConjCongr ha) (conj_conj a)

def RealCoefficients : Coefficients → Prop
  | [] => True
  | a::p => IsReal a ∧ RealCoefficients p

theorem realCoefficients_ofReal (p : List Real) : RealCoefficients (ofReal p) := by
  induction p with
  | nil => trivial
  | cons a p ih => exact ⟨IsReal.realArgument a, ih⟩

theorem realCoefficients_conj (p : Coefficients) (hp : RealCoefficients p) : Equivalent (p.map conj) p := by
  induction p with
  | nil => exact .nil
  | cons a p ih => exact .cons hp.1 (ih hp.2)

theorem realCoefficients_root_conj {p : Coefficients} (hp : RealCoefficients p) {r : ComplexCert}
    (hr : Root p r) : Root p (conj r) :=
  root_congr (realCoefficients_conj p hp) (certRefl (conj r)) (root_conj hr)

/-- Linear division at a real root preserves real coefficients. -/
theorem syntheticDivide_real (r : ComplexCert) (hr : IsReal r) (p : Coefficients)
    (hp : RealCoefficients p) :
    RealCoefficients (syntheticDivide r p).1 ∧ IsReal (syntheticDivide r p).2 := by
  induction p with
  | nil => exact ⟨True.intro, IsReal.zero⟩
  | cons a p ih =>
      cases p with
      | nil => exact ⟨True.intro, hp.1⟩
      | cons b p =>
          have hi := ih hp.2
          exact ⟨⟨hi.2, hi.1⟩, IsReal.add hp.1 (IsReal.mul hr hi.2)⟩

end ComputableAnalysis.RepresentedPolynomial
