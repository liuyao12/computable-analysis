import ComputableAnalysis.TrigonometricPrimitiveFormula

/-! Factorizations whose correctness uses identities of represented reals.
For example, a square-root computation squares to its radicand, whereas its
finite rational samples need not do so. Such identities must be transported
by `RealRaw.Equiv`, not demanded of every independent rational sample. -/
namespace ComputableAnalysis
namespace ComputableTrigonometricRationalization
open ComputableCoefficient ComputableFactoredAlgebra

/-- A factorized presentation of the transformed rational function. Its
correctness is an algebraic equality of represented computations, not an
assumed primitive or derivative identity. The original expression's domain
is separately retained by the theorem below. -/
structure RepresentedFactorization (e : Expr) where
  factored : FactoredRational
  identity : ∀ (t : C) (N M : Nat) (v w : Value),
    (factored.value t).realize N = some v →
    (e.pullback.value t).realize M = some w →
    v.real.preferred.Equiv w.real.preferred

/-- Sample-exact factorizations are a convenient special case. -/
def Factorization.asRepresented {e : Expr} (F : Factorization e) : RepresentedFactorization e where
  factored := {
    numerator := e.pullback.num
    leading := F.leading
    factors := F.factors
    checkedFactors := F.checked
    leadingApart := F.leadingApart }
  identity := by
    intro t N M v w hv hw
    apply ComputableCoefficient.Expr.realize_equiv _ _ N M v w hv hw F.identity.cutoff
    intro n hn s hs
    have hi := F.identity.holds n hn s hs (t.sample s)
    simp only [FactoredRational.value, Rational.value, ComputableCoefficient.Expr.sample_div,
      ComputableCoefficient.Expr.sample, sample_eval]
    change Polynomial.eval (sampled s e.pullback.num) (t.sample s) /
      (F.leading.sample s * Polynomial.eval (sampled s (denominator F.factors)) (t.sample s)) =
      Polynomial.eval (sampled s e.pullback.num) (t.sample s) /
        Polynomial.eval (sampled s e.pullback.den) (t.sample s)
    change Polynomial.eval (sampled s e.pullback.den) (t.sample s) = _ at hi
    rw [hi]

/-- Cancel the Jacobian in the original compiler independently of any
factorization. This preserves the original partial-expression domain. -/
theorem Expr.pullback_angle_correct (e : Expr) (t : C)
    (domain : SampleCertificate (fun s =>
      (e.shadow s).eval (TrigonometricRationalization.sineCoordinate (t.sample s))
        (TrigonometricRationalization.cosineCoordinate (t.sample s)) ≠ none))
    (N M : Nat) (d v : Value)
    (hd : (ComputableCoefficient.Expr.mul (e.pullback.value t) (inverseJacobianExpr t)).realize N = some d)
    (hv : (e.value (sineCoordinate t) (cosineCoordinate t)).realize M = some v) :
    d.real.preferred.Equiv v.real.preferred := by
  apply ComputableCoefficient.Expr.realize_equiv _ _ N M d v hd hv domain.cutoff
  intro n hn s hs
  have hdom := domain.holds n hn s hs
  cases he : (e.shadow s).eval (TrigonometricRationalization.sineCoordinate (t.sample s))
      (TrigonometricRationalization.cosineCoordinate (t.sample s)) with
  | none => exact False.elim (hdom he)
  | some w =>
      have hp := e.pullback_correct s (t.sample s)
      rw [he] at hp
      have hnz : (e.pullback.shadow s).denominator (t.sample s) ≠ 0 := by
        intro hz
        simp [RatFun.eval?, hz] at hp
      have hvp : (e.pullback.shadow s).numerator (t.sample s) /
          (e.pullback.shadow s).denominator (t.sample s) = w * TrigonometricRationalization.jacobian (t.sample s) := by
        simpa only [RatFun.eval?, if_neg hnz, Option.map_some, Option.some.injEq] using hp
      have hval := e.value_sample_of_eval s (sineCoordinate t) (cosineCoordinate t) w
        (by simpa only [sample_sine, sample_cosine] using he)
      change (e.pullback.value t).sample s * inverseJacobian (t.sample s) = _
      rw [hval, Rational.value, ComputableCoefficient.Expr.sample_div, sample_eval, sample_eval]
      change (e.pullback.shadow s).numerator (t.sample s) /
        (e.pullback.shadow s).denominator (t.sample s) * inverseJacobian (t.sample s) = w
      rw [hvp, Rat.mul_assoc, jacobian_cancel, Rat.mul_one]

/-- Universal formal primitive transfer using represented factorization
identities. Irrational algebraic roots need not satisfy their equations at
any finite rational approximation stage. -/
theorem RepresentedFactorization.primitive_correct {e : Expr} (F : RepresentedFactorization e)
    (t : C)
    (factorDomain : SampleCertificate (fun s =>
      (ComputableFactoredAlgebra.eval (denominator F.factored.factors) t).sample s ≠ 0))
    (domain : SampleCertificate (fun s =>
      (e.shadow s).eval (TrigonometricRationalization.sineCoordinate (t.sample s))
        (TrigonometricRationalization.cosineCoordinate (t.sample s)) ≠ none))
    (N M K H : Nat) (d f p j v : Value)
    (hd : (F.factored.formula.formalDerivative t).realize N = some d)
    (hf : (F.factored.value t).realize M = some f)
    (hp : (e.pullback.value t).realize K = some p)
    (hj : (inverseJacobianExpr t).realize K = some j)
    (hv : (e.value (sineCoordinate t) (cosineCoordinate t)).realize H = some v) :
    (Value.mul d j).real.preferred.Equiv v.real.preferred := by
  have hdf := F.factored.primitive_correct t factorDomain N M d f hd hf
  have hfp := F.identity t M K f p hf hp
  have hdp := RealRaw.equiv_trans d.real.valid f.real.valid p.real.valid hdf hfp
  have hmul : (Value.mul d j).real.preferred.Equiv (Value.mul p j).real.preferred :=
    RealRaw.mul_equiv d.real.valid p.real.valid j.real.valid j.real.valid hdp
      (RealRaw.equiv_refl _ j.real.valid)
  have hchain := e.pullback_angle_correct t domain K H (Value.mul p j) v
    (by simp only [ComputableCoefficient.Expr.realize, hp, hj]; rfl) hv
  exact RealRaw.equiv_trans (Value.mul d j).real.valid (Value.mul p j).real.valid v.real.valid hmul hchain

end ComputableTrigonometricRationalization
end ComputableAnalysis
