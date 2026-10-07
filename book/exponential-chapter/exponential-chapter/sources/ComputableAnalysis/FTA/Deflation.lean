import ComputableAnalysis.FTA.Algebra

/-! Exact synthetic division for polynomials with arbitrary represented complex
coefficients. The root is a hypothesis for factor removal, never for FTA's
existence step. Every output coefficient is computed by finite arithmetic. -/
namespace ComputableAnalysis.RepresentedPolynomial

private theorem trans {a b c : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hbc : b.raw.Equiv c.raw) : a.raw.Equiv c.raw :=
  ComplexRaw.equiv_trans a.valid b.valid c.valid hab hbc

private theorem refl (a : ComplexCert) : a.raw.Equiv a.raw :=
  ComplexRaw.equiv_refl _ a.valid

private theorem add_congr {a b c d : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (add a c).raw.Equiv (add b d).raw := ComplexRaw.add_equiv hab hcd

private theorem mul_congr {a b c d : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (mul a c).raw.Equiv (mul b d).raw :=
  ComplexRaw.mul_equiv a.valid b.valid c.valid d.valid hab hcd

private theorem mul_zero (a : ComplexCert) : (mul a zero).raw.Equiv zero.raw := by
  apply Arithmetic.Expression.equiv_of_samples
    (.mul (.parameter a) (.constant QComplex.zero)) (.constant QComplex.zero)
  intro s
  simp [Arithmetic.Expression.sample, QComplex.mul, QComplex.zero]
  grind

/-- Ascending coefficients. The quotient has one fewer coefficient; no
attempt is made to decide whether an arbitrary represented coefficient is zero. -/
def syntheticDivide (r : ComplexCert) : Coefficients → Coefficients × ComplexCert
  | [] => ([], zero)
  | [c] => ([], c)
  | c :: d :: p =>
      let qr := syntheticDivide r (d :: p)
      (qr.2 :: qr.1, add c (mul r qr.2))

theorem syntheticDivide_length (r : ComplexCert) (p : Coefficients) :
    (syntheticDivide r p).1.length = p.length - 1 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      cases p with
      | nil => rfl
      | cons d p =>
          change (syntheticDivide r (d :: p)).1.length + 1 = _
          rw [ih]
          simp

/-- The exact remainder identity, as equality of valid raw values. -/
theorem syntheticDivide_spec (r x : ComplexCert) (p : Coefficients) :
    (eval p x).raw.Equiv
      (add (syntheticDivide r p).2
        (mul (sub x r) (eval (syntheticDivide r p).1 x))).raw := by
  induction p with
  | nil =>
      exact ComplexRaw.equiv_symm (trans
        (add_congr (refl zero) (mul_zero (sub x r))) (zero_add zero))
  | cons c p ih =>
      cases p with
      | nil =>
          change (add c (mul x zero)).raw.Equiv (add c (mul (sub x r) zero)).raw
          exact trans (add_congr (refl c) (mul_zero x))
            (ComplexRaw.equiv_symm (add_congr (refl c) (mul_zero (sub x r))))
      | cons d p =>
          exact trans (add_congr (refl c) (mul_congr (refl x) ih))
            (deflation_step c r x (syntheticDivide r (d :: p)).2
              (eval (syntheticDivide r (d :: p)).1 x))

theorem syntheticDivide_remainder (r : ComplexCert) (p : Coefficients) :
    (syntheticDivide r p).2.raw.Equiv (eval p r).raw := by
  have hzero := trans (mul_congr (sub_self r)
    (refl (eval (syntheticDivide r p).1 r)))
    (zero_mul (eval (syntheticDivide r p).1 r))
  exact ComplexRaw.equiv_symm (trans (syntheticDivide_spec r r p)
    (trans (add_congr (refl (syntheticDivide r p).2) hzero)
      (add_zero (syntheticDivide r p).2)))

/-- Removing an exact represented root gives an exact factor identity at every
represented argument. Neither the root nor the coefficients need be rational. -/
theorem syntheticDivide_factor {p : Coefficients} {r : ComplexCert}
    (hr : Root p r) (x : ComplexCert) :
    (eval p x).raw.Equiv
      (mul (sub x r) (eval (syntheticDivide r p).1 x)).raw := by
  have hrem := trans (syntheticDivide_remainder r p) hr
  exact trans (syntheticDivide_spec r x p)
    (trans (add_congr hrem
      (refl (mul (sub x r) (eval (syntheticDivide r p).1 x))))
      (zero_add _))

/-- This is the algebraic induction step for FTA factorization. Root existence
is the separate analytic step; the quotient and its degree reduction are proved. -/
theorem factor_of_root {p : Coefficients} {r : ComplexCert} (hr : Root p r) :
    ∃ q : Coefficients, q.length = p.length - 1 ∧
      ∀ x : ComplexCert, (eval p x).raw.Equiv (mul (sub x r) (eval q x)).raw :=
  ⟨(syntheticDivide r p).1, syntheticDivide_length r p, syntheticDivide_factor hr⟩

/-- Conjugation commutes with polynomial evaluation, including coefficients. -/
theorem eval_conj (p : Coefficients) (z : ComplexCert) :
    (conj (eval p z)).raw.Equiv (eval (p.map conj) (conj z)).raw := by
  induction p with
  | nil => exact conj_zero
  | cons a p ih =>
      exact trans (conj_add a (mul z (eval p z)))
        (add_congr (refl (conj a))
          (trans (conj_mul z (eval p z)) (mul_congr (refl (conj z)) ih)))

theorem root_conj {p : Coefficients} {z : ComplexCert} (hz : Root p z) :
    Root (p.map conj) (conj z) :=
  trans (ComplexRaw.equiv_symm (eval_conj p z))
    (trans (ComplexRaw.conj_equiv hz) conj_zero)

private theorem real_conj (a : Real) :
    (conj ⟨ComplexRaw.ofRealRaw a.preferred,
      ComplexRaw.ofRealRaw_valid a.preferred a.valid⟩).raw.Equiv
      (ComplexRaw.ofRealRaw a.preferred) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  have ha := a.valid.1 n
  change 0 ≤ (a.preferred.compute n).hi - (a.preferred.compute n).lo at ha
  change ((a.preferred.compute n).lo ≤ (a.preferred.compute n).hi ∧ -0 ≤ (0 : Rat)) ∧
    ((a.preferred.compute n).lo ≤ (a.preferred.compute n).hi ∧ (0 : Rat) ≤ -0)
  constructor <;> constructor <;> grind

theorem ofReal_conj (p : List Real) : Equivalent ((ofReal p).map conj) (ofReal p) := by
  induction p with
  | nil => exact .nil
  | cons a p ih => exact .cons (real_conj a) ih

/-- Non-real roots of a real polynomial have conjugate roots. This theorem
uses exact raw equality and arbitrary real coefficients and arguments. -/
theorem real_root_conj {p : List Real} {z : ComplexCert} (hz : Root (ofReal p) z) :
    Root (ofReal p) (conj z) :=
  root_congr (ofReal_conj p) (refl (conj z)) (root_conj hz)

end ComputableAnalysis.RepresentedPolynomial
