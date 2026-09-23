import ComputableAnalysis.ComputableTrigonometricRationalization

/-! The elementary formula theorem after half-angle substitution.
This layer proves the represented formal chain identity, with supplied
factorization and computable coefficients. Runtime derivative transport is
kept separate; the statement does not assume a primitive identity. -/
namespace ComputableAnalysis
namespace ComputableTrigonometricRationalization
open ComputableCoefficient ComputableFactoredAlgebra

/-- A supplied factorization of the compiler's denominator, not a supplied
partial fraction decomposition or primitive. -/
structure Factorization (e : Expr) where
  factors : List ComputableFactoredAlgebra.Factor
  leading : C
  checked : CheckedFactors factors
  leadingApart : SampleCertificate (fun s => leading.sample s ≠ 0)
  identity : SampleCertificate (fun s => ∀ t,
    (e.pullback.shadow s).denominator t = leading.sample s *
      Polynomial.eval (sampled s (denominator factors)) t)

def Factorization.formula {e : Expr} (F : Factorization e) : Formula :=
  primitive F.factors (ComputableFactoredAlgebra.scale F.leading.inv e.pullback.num)

def Factorization.cutoff {e : Expr} (F : Factorization e) : Nat :=
  max F.checked.cutoff (max F.leadingApart.cutoff F.identity.cutoff)

def circleDenominator (t : C) : C := .add (.rational 1) (.mul t t)
def sineCoordinate (t : C) : C := (ComputableCoefficient.Expr.mul (.rational 2) t).div (circleDenominator t)
def cosineCoordinate (t : C) : C :=
  (ComputableCoefficient.Expr.sub (.rational 1) (.mul t t)).div (circleDenominator t)
def inverseJacobianExpr (t : C) : C := (circleDenominator t).div (.rational 2)

def Factorization.angleDerivative {e : Expr} (F : Factorization e) (t : C) : C :=
  .mul (F.formula.formalDerivative t) (inverseJacobianExpr t)

@[simp] theorem sample_sine (t : C) (s : Real → Rat) :
    (sineCoordinate t).sample s = TrigonometricRationalization.sineCoordinate (t.sample s) := rfl
@[simp] theorem sample_cosine (t : C) (s : Real → Rat) :
    (cosineCoordinate t).sample s = TrigonometricRationalization.cosineCoordinate (t.sample s) := by
  simp only [cosineCoordinate, ComputableCoefficient.Expr.sample_div,
    ComputableCoefficient.Expr.sample_sub, ComputableCoefficient.Expr.sample, circleDenominator,
    TrigonometricRationalization.cosineCoordinate]

/-- Successful partial evaluation agrees with coefficient arithmetic. -/
theorem Expr.value_sample_of_eval (e : Expr) (s : Real → Rat) (a b : C) (v : Rat)
    (h : (e.shadow s).eval (a.sample s) (b.sample s) = some v) :
    (e.value a b).sample s = v := by
  induction e generalizing v with
  | sine => cases h; rfl
  | cosine => cases h; rfl
  | const c => cases h; rfl
  | neg e ih =>
      cases he : (e.shadow s).eval (a.sample s) (b.sample s) with
      | none => simp [shadow, TrigonometricRationalization.Expr.eval, he] at h
      | some w =>
          simp only [shadow, TrigonometricRationalization.Expr.eval, he, Option.map_some,
            Option.some.injEq] at h
          change -(e.value a b).sample s = v
          rw [ih w he, h]
  | add e f ie iff =>
      cases he : (e.shadow s).eval (a.sample s) (b.sample s) <;>
        cases hf : (f.shadow s).eval (a.sample s) (b.sample s) <;>
        simp only [shadow, TrigonometricRationalization.Expr.eval, he, hf] at h
      · cases h
      · cases h
      · cases h
      · cases h
        change (e.value a b).sample s + (f.value a b).sample s = _
        rw [ie _ he, iff _ hf]
  | mul e f ie iff =>
      cases he : (e.shadow s).eval (a.sample s) (b.sample s) <;>
        cases hf : (f.shadow s).eval (a.sample s) (b.sample s) <;>
        simp only [shadow, TrigonometricRationalization.Expr.eval, he, hf] at h
      · cases h
      · cases h
      · cases h
      · cases h
        change (e.value a b).sample s * (f.value a b).sample s = _
        rw [ie _ he, iff _ hf]
  | inv e ih =>
      cases he : (e.shadow s).eval (a.sample s) (b.sample s) with
      | none => simp [shadow, TrigonometricRationalization.Expr.eval, he] at h
      | some w =>
          by_cases hw : w = 0
          · simp [shadow, TrigonometricRationalization.Expr.eval, he, hw] at h
          · simp only [shadow, TrigonometricRationalization.Expr.eval, he, if_neg hw,
              Option.some.injEq] at h
            change ((e.value a b).sample s)⁻¹ = v
            rw [ih w he, ← h]
            simp only [Rat.div_def, Rat.one_mul]

/-- All rational expressions and all multiplicities. The supplied data
factor the denominator; the algorithm computes the primitive formula. -/
theorem Factorization.primitive_sample_correct {e : Expr} (F : Factorization e)
    (n : Nat) (hn : F.cutoff ≤ n) (s : Real → Rat) (hs : Samples n s)
    (t : C) (v : Rat)
    (hv : (e.shadow s).eval (TrigonometricRationalization.sineCoordinate (t.sample s))
      (TrigonometricRationalization.cosineCoordinate (t.sample s)) = some v) :
    (F.angleDerivative t).sample s = v := by
  have hc : F.checked.cutoff ≤ n := by dsimp [cutoff] at hn; omega
  have hl : F.leadingApart.cutoff ≤ n := by dsimp [cutoff] at hn; omega
  have hi : F.identity.cutoff ≤ n := by dsimp [cutoff] at hn; omega
  obtain ⟨hp, ha⟩ := F.checked.holds n hc s hs
  have H := e.pullback_correct s (t.sample s)
  rw [hv] at H
  simp only [Option.map_some] at H
  have hd : (e.pullback.shadow s).denominator (t.sample s) ≠ 0 := by
    intro hz
    simp [RatFun.eval?, hz] at H
  have hden : (ComputableFactoredAlgebra.eval (denominator F.factors) t).sample s ≠ 0 := by
    rw [sample_eval]
    intro hz
    apply hd
    rw [F.identity.holds n hi s hs, hz, Rat.mul_zero]
  have hval : (e.pullback.shadow s).numerator (t.sample s) /
      (e.pullback.shadow s).denominator (t.sample s) = v * TrigonometricRationalization.jacobian (t.sample s) := by
    simpa only [RatFun.eval?, if_neg hd, Option.some.injEq] using H
  change ((primitive F.factors (ComputableFactoredAlgebra.scale F.leading.inv e.pullback.num)).formalDerivative t).sample s *
    inverseJacobian (t.sample s) = v
  rw [ComputableFactoredAlgebra.primitive_sample_correct _ _ _ s hp ha hden]
  have heq : (integrand F.factors (ComputableFactoredAlgebra.scale F.leading.inv e.pullback.num) t).sample s =
      (e.pullback.shadow s).numerator (t.sample s) / (e.pullback.shadow s).denominator (t.sample s) := by
    rw [F.identity.holds n hi s hs]
    simp only [integrand, ComputableCoefficient.Expr.sample_div, sample_eval, sample_scale,
      RationalExpressionNormalization.eval_scale, ComputableCoefficient.Expr.sample,
      RatFun.numerator, Rational.shadow, Rat.div_def, Rat.inv_mul_rev]
    grind
  rw [heq, hval, Rat.mul_assoc, jacobian_cancel, Rat.mul_one]

/-- The formal angle derivative is equivalent to the original represented
rational expression. Computable/irrational constants and chart inputs are
retained, and all evaluations must pass the finite reciprocal checks. -/
theorem Factorization.primitive_correct {e : Expr} (F : Factorization e) (t : C)
    (domain : SampleCertificate (fun s =>
      (e.shadow s).eval (TrigonometricRationalization.sineCoordinate (t.sample s))
        (TrigonometricRationalization.cosineCoordinate (t.sample s)) ≠ none))
    (N M : Nat) (d v : Value)
    (hd : (F.angleDerivative t).realize N = some d)
    (hv : (e.value (sineCoordinate t) (cosineCoordinate t)).realize M = some v) :
    d.real.preferred.Equiv v.real.preferred := by
  apply ComputableCoefficient.Expr.realize_equiv _ _ N M d v hd hv (max F.cutoff domain.cutoff)
  intro n hn s hs
  have hh := domain.holds n (by omega) s hs
  cases he : (e.shadow s).eval (TrigonometricRationalization.sineCoordinate (t.sample s))
      (TrigonometricRationalization.cosineCoordinate (t.sample s)) with
  | none => exact False.elim (hh he)
  | some w =>
      rw [F.primitive_sample_correct n (by omega) s hs t w he]
      exact (e.value_sample_of_eval s (sineCoordinate t) (cosineCoordinate t) w (by
        simpa only [sample_sine, sample_cosine] using he)).symm

end ComputableTrigonometricRationalization
end ComputableAnalysis
