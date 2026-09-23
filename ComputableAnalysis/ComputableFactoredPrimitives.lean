import ComputableAnalysis.ComputablePrimitiveFormula

/-!
# Certified factorized input with arbitrary computable-real coefficients

Factorization is supplied, partial fractions are computed. Finite interval
certificates establish positivity and separation; no real equality decision,
FTA axiom, completed-real field, or partial-fraction identity is an input.
The conclusion concerns the represented *formal derivative*. Analytic
realization of the logarithm/arctangent formulas remains a separate theorem.
-/
namespace ComputableAnalysis
namespace ComputableFactoredAlgebra
open ComputableCoefficient

/-- A finite observation sufficient for a property of every finer sample. -/
structure SampleCertificate (P : (Real → Rat) → Prop) where
  cutoff : Nat
  holds : ∀ m, cutoff ≤ m → ∀ s, Samples m s → P s

inductive Constraint where
  | positive (e : C)
  | apart (e : C)

def Constraint.Holds (s : Real → Rat) : Constraint → Prop
  | .positive e => 0 < e.sample s
  | .apart e => e.sample s ≠ 0

/-- All decisions here compare rational interval endpoints. -/
def certify (N : Nat) (c : Constraint) : Option (SampleCertificate (fun s => c.Holds s)) :=
  match c with
  | .positive e =>
      match heval : e.realize N with
      | none => none
      | some v =>
        if hp : 0 < (v.real.compute N).lo then
          some ⟨v.observation N, by
            intro m hm s hs
            have hh := v.encloses N m hm s hs
            have he := Expr.realize_sample e N v heval s
            change 0 < e.sample s
            rw [← he]
            grind⟩
        else none
  | .apart e =>
      match heval : e.realize N with
      | none => none
      | some v =>
        if hp : 0 < (v.real.compute N).lo then
          some ⟨v.observation N, by
            intro m hm s hs
            have hh := v.encloses N m hm s hs
            have he := Expr.realize_sample e N v heval s
            change e.sample s ≠ 0
            rw [← he]
            grind⟩
        else if hn : (v.real.compute N).hi < 0 then
          some ⟨v.observation N, by
            intro m hm s hs
            have hh := v.encloses N m hm s hs
            have he := Expr.realize_sample e N v heval s
            change e.sample s ≠ 0
            rw [← he]
            grind⟩
        else none

def certifyAll (N : Nat) : (cs : List Constraint) →
    Option (SampleCertificate (fun s => ∀ c ∈ cs, c.Holds s))
  | [] => some ⟨0, by intros; simp_all⟩
  | c :: cs => do
      let hc ← certify N c
      let ht ← certifyAll N cs
      return ⟨max hc.cutoff ht.cutoff, by
        intro m hm s hs d hd
        rcases List.mem_cons.mp hd with he | hh
        · subst d; exact hc.holds m (by omega) s hs
        · exact ht.holds m (by omega) s hs d hh⟩

/-- Separation checks depend only on factors, never on a supplied primitive
or partial-fraction decomposition. -/
def requirements : List Factor → List Constraint
  | [] => []
  | .linear a _ :: fs => .apart (eval (denominator fs) a) :: requirements fs
  | .quadratic a b _ :: fs =>
      .positive b :: .apart (norm b (divide a b (denominator fs))) :: requirements fs

theorem requirements_sufficient (fs : List Factor) (s : Real → Rat)
    (h : ∀ c ∈ requirements fs, c.Holds s) :
    Positive s fs ∧ RationalFactoredPrimitives.Admissible (fs.map (Factor.shadow s)) := by
  induction fs with
  | nil => exact ⟨(by intro f hf; cases hf), True.intro⟩
  | cons f fs ih =>
      have ht : ∀ c ∈ requirements fs, c.Holds s := by
        intro c hc
        cases f <;> exact h c (by simp [requirements, hc])
      obtain ⟨hp, ha⟩ := ih ht
      have hpos : f.Positive s := by
        cases f with
        | linear a n => trivial
        | quadratic a b n => exact h (.positive b) (by simp [requirements])
      refine ⟨by intro g hg; rcases List.mem_cons.mp hg with he | hh; subst g; exact hpos; exact hp g hh, ?_⟩
      change (f.shadow s).Compatible (RationalFactoredPrimitives.denominator (fs.map (Factor.shadow s))) ∧ _
      refine ⟨?_, ha⟩
      rw [← sample_denominator s fs hp]
      cases f with
      | linear a n =>
          have hh := h (.apart (eval (denominator fs) a)) (by simp [requirements])
          change (eval (denominator fs) a).sample s ≠ 0 at hh
          rw [sample_eval] at hh
          exact hh
      | quadratic a b n =>
          have hh := h (.apart (norm b (divide a b (denominator fs)))) (by simp [requirements])
          change (norm b (divide a b (denominator fs))).sample s ≠ 0 at hh
          rw [sample_norm, sample_divide] at hh
          change (RationalQuadraticDivision.divide (a.sample s) (positiveSample s b).val (sampled s (denominator fs))).slope ≠ 0 ∨
            (RationalQuadraticDivision.divide (a.sample s) (positiveSample s b).val (sampled s (denominator fs))).constant ≠ 0
          rw [positiveSample_val s b hpos]
          by_cases h1 : (RationalQuadraticDivision.divide (a.sample s) (b.sample s) (sampled s (denominator fs))).slope = 0
          · right; intro h2
            apply hh
            simp [RationalQuadraticDivision.norm, h1, h2, Rat.add_zero]
          · exact Or.inl h1

abbrev CheckedFactors (fs : List Factor) := SampleCertificate (fun s =>
  Positive s fs ∧ RationalFactoredPrimitives.Admissible (fs.map (Factor.shadow s)))

/-- A successful check packages the hypotheses of the integration algorithm. -/
def certifyFactors (N : Nat) (fs : List Factor) : Option (CheckedFactors fs) := do
  let c ← certifyAll N (requirements fs)
  return ⟨c.cutoff, by intro m hm s hs; exact requirements_sufficient fs s (c.holds m hm s hs)⟩

theorem removeLinear_positive (s : Real → Rat) (p q : List C) (a : C) (n : Nat) :
    ∀ t ∈ (removeLinear p q a n).terms, t.Positive s := by
  induction n generalizing p with
  | zero => simp [removeLinear]
  | succ n ih =>
      intro t ht
      change t ∈ Term.linear _ _ _ :: _ at ht
      rcases List.mem_cons.mp ht with he | hh
      · subst t; trivial
      · exact ih _ t hh

theorem removeQuadratic_positive (s : Real → Rat) (a b : C) (p q : List C)
    (hb : 0 < b.sample s) (n : Nat) :
    ∀ t ∈ (removeQuadratic a b p q n).terms, t.Positive s := by
  induction n generalizing p with
  | zero => simp [removeQuadratic]
  | succ n ih =>
      intro t ht
      change t ∈ Term.quadratic _ _ _ _ _ :: _ at ht
      rcases List.mem_cons.mp ht with he | hh
      · subst t; exact hb
      · exact ih _ t hh

theorem normalForm_positive (s : Real → Rat) (fs : List Factor) (p : List C) (h : Positive s fs) :
    ∀ t ∈ (normalForm fs p).terms, t.Positive s := by
  induction fs generalizing p with
  | nil => simp [normalForm]
  | cons f fs ih =>
      intro t ht
      change t ∈ (f.remove p (denominator fs)).terms ++ _ at ht
      rcases List.mem_append.mp ht with hb | hl
      · have hf := h f (by simp)
        cases f with
        | linear a n => exact removeLinear_positive s p (denominator fs) a (n+1) t hb
        | quadratic a b n => exact removeQuadratic_positive s a b p (denominator fs) hf (n+1) t hb
      · exact ih _ (by intro f hf; exact h f (by simp [hf])) t hl

def primitive (fs : List Factor) (p : List C) : Formula := (normalForm fs p).primitive

def integrand (fs : List Factor) (p : List C) (x : C) : C :=
  (eval p x).div (eval (denominator fs) x)

theorem primitive_sample_correct (fs : List Factor) (p : List C) (x : C) (s : Real → Rat)
    (hp : Positive s fs)
    (ha : RationalFactoredPrimitives.Admissible (fs.map (Factor.shadow s)))
    (hx : (eval (denominator fs) x).sample s ≠ 0) :
    ((primitive fs p).formalDerivative x).sample s = (integrand fs p x).sample s := by
  have ht := normalForm_positive s fs p hp
  unfold primitive
  rw [Formula.sample_formalDerivative s _ x ((normalForm fs p).primitive_positive s ht)]
  change ((normalForm fs p).primitive.shadow s).formalDerivative (x.sample s) = _
  rw [NormalForm.shadow_primitive s _ ht, shadow_normalForm s fs p hp]
  have hn : Polynomial.eval (RationalFactoredPrimitives.denominator (fs.map (Factor.shadow s))) (x.sample s) ≠ 0 := by
    rw [sample_eval, sample_denominator s fs hp] at hx
    exact hx
  rw [RationalPrimitiveFormula.NormalForm.primitive_correct _ _
    (RationalFactoredPrimitives.normalForm_regular _ _ _ hn),
    RationalFactoredPrimitives.normalForm_identity _ _ ha _ hn]
  simp only [integrand, Expr.sample_div, sample_eval, sample_denominator s fs hp]

/-- Main coefficient-general theorem: the computed elementary formula's
represented formal derivative agrees with the original factored rational
function. Every real parameter and every computed coefficient is evaluated
by certified interval arithmetic. -/
theorem primitive_correct (fs : List Factor) (p : List C) (hf : CheckedFactors fs)
    (x : C) (hx : SampleCertificate (fun s => (eval (denominator fs) x).sample s ≠ 0))
    (N M : Nat) (d v : Value)
    (hd : ((primitive fs p).formalDerivative x).realize N = some d)
    (hv : (integrand fs p x).realize M = some v) :
    d.real.preferred.Equiv v.real.preferred := by
  apply Expr.realize_equiv _ _ N M d v hd hv (max hf.cutoff hx.cutoff)
  intro m hm s hs
  obtain ⟨hp, ha⟩ := hf.holds m (by omega) s hs
  exact primitive_sample_correct fs p x s hp ha (hx.holds m (by omega) s hs)


/-- Input already in factored form. The leading coefficient and numerator
coefficients may be arbitrary certified computable reals, via `Expr.parameter`.
A separate factorization theorem can provide this data without changing the
integration algorithm. -/
structure FactoredRational where
  numerator : List C
  leading : C
  factors : List Factor
  checkedFactors : CheckedFactors factors
  leadingApart : SampleCertificate (fun s => leading.sample s ≠ 0)

def FactoredRational.formula (f : FactoredRational) : Formula :=
  primitive f.factors (scale f.leading.inv f.numerator)

def FactoredRational.value (f : FactoredRational) (x : C) : C :=
  (eval f.numerator x).div (.mul f.leading (eval (denominator f.factors) x))

/-- The non-monic version retains the original leading coefficient in the
integrand and computes its reciprocal in the output coefficients. -/
theorem FactoredRational.primitive_correct (f : FactoredRational) (x : C)
    (hx : SampleCertificate (fun s => (eval (denominator f.factors) x).sample s ≠ 0))
    (N M : Nat) (d v : Value)
    (hd : (f.formula.formalDerivative x).realize N = some d)
    (hv : (f.value x).realize M = some v) :
    d.real.preferred.Equiv v.real.preferred := by
  apply Expr.realize_equiv _ _ N M d v hd hv (max f.checkedFactors.cutoff hx.cutoff)
  intro m hm s hs
  obtain ⟨hp, ha⟩ := f.checkedFactors.holds m (by omega) s hs
  change ((primitive f.factors (scale f.leading.inv f.numerator)).formalDerivative x).sample s = _
  rw [primitive_sample_correct _ _ _ s hp ha (hx.holds m (by omega) s hs)]
  simp only [integrand, value, Expr.sample_div, sample_eval, sample_scale,
    RationalExpressionNormalization.eval_scale, Expr.sample, Rat.div_def, Rat.inv_mul_rev]
  grind

end ComputableFactoredAlgebra
end ComputableAnalysis
