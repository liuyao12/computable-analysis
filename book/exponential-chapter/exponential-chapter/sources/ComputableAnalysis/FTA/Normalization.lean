import ComputableAnalysis.FTA.Inverse
import ComputableAnalysis.FTA.Factorization

/-! Exact normalization and conditional splitting with arbitrary nonzero
leading coefficients. The leading coefficient may be irrational. The caller
supplies its nonzero mathematical hypothesis, not an inversion stage. -/
namespace ComputableAnalysis.RepresentedPolynomial
open Arithmetic

private theorem trans {a b c : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hbc : b.raw.Equiv c.raw) : a.raw.Equiv c.raw :=
  ComplexRaw.equiv_trans a.valid b.valid c.valid hab hbc

private theorem mul_congr {a b c d : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (mul a c).raw.Equiv (mul b d).raw :=
  ComplexRaw.mul_equiv a.valid b.valid c.valid d.valid hab hcd

private theorem add_congr {a b c d : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (add a c).raw.Equiv (add b d).raw := ComplexRaw.add_equiv hab hcd

private theorem qext {a b : QComplex} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

private theorem mul_one (a : ComplexCert) : (mul a one).raw.Equiv a.raw := by
  apply Expression.equiv_of_samples (.mul (.parameter a) (.constant QComplex.one)) (.parameter a)
  intro s
  exact QComplex.mul_one_cert _

private theorem one_mul (a : ComplexCert) : (mul one a).raw.Equiv a.raw := by
  apply Expression.equiv_of_samples (.mul (.constant QComplex.one) (.parameter a)) (.parameter a)
  intro s
  apply qext <;> simp [Expression.sample, QComplex.mul, QComplex.one] <;> grind

private theorem mul_assoc (a b c : ComplexCert) :
    (mul a (mul b c)).raw.Equiv (mul (mul a b) c).raw := by
  apply Expression.equiv_of_samples (.mul (.parameter a) (.mul (.parameter b) (.parameter c)))
    (.mul (.mul (.parameter a) (.parameter b)) (.parameter c))
  intro s
  exact (QComplex.mul_assoc_cert _ _ _).symm

private theorem scale_step (c a x b : ComplexCert) :
    (add (mul c a) (mul x (mul c b))).raw.Equiv (mul c (add a (mul x b))).raw := by
  apply Expression.equiv_of_samples
    (.add (.mul (.parameter c) (.parameter a))
      (.mul (.parameter x) (.mul (.parameter c) (.parameter b))))
    (.mul (.parameter c) (.add (.parameter a) (.mul (.parameter x) (.parameter b))))
  intro s
  apply qext <;> simp [Expression.sample, QComplex.add, QComplex.mul] <;> grind

/-- Scaling coefficients commutes with Horner evaluation at every represented
argument, with exact equality of the represented values. -/
theorem eval_scale (c : ComplexCert) (p : Coefficients) (x : ComplexCert) :
    (eval (p.map (mul c)) x).raw.Equiv (mul c (eval p x)).raw := by
  induction p with
  | nil =>
      apply Expression.equiv_of_samples (.constant QComplex.zero)
        (.mul (.parameter c) (.constant QComplex.zero))
      intro s
      apply qext <;> simp [Expression.sample, QComplex.mul, QComplex.zero] <;> grind
  | cons a p ih =>
      change (add (mul c a) (mul x (eval (p.map (mul c)) x))).raw.Equiv _
      exact trans (add_congr (ComplexRaw.equiv_refl _ (mul c a).valid)
        (mul_congr (ComplexRaw.equiv_refl _ x.valid) ih)) (scale_step c a x (eval p x))

/-- Canonical monic normalization, using a supplied reciprocal of the leading
coefficient. The leading entry is literally one; no raw equality test is used. -/
def normalize (q : Coefficients) (inverse : ComplexCert) : Coefficients :=
  q.map (mul inverse) ++ [one]

theorem normalize_spec (q : Coefficients) (c b : ComplexCert)
    (hcb : (mul c b).raw.Equiv one.raw) (x : ComplexCert) :
    (eval (q ++ [c]) x).raw.Equiv (mul c (eval (normalize q b) x)).raw := by
  have hcoeff : Equivalent (q ++ [c]) ((normalize q b).map (mul c)) := by
    have recover (a : ComplexCert) : (mul c (mul b a)).raw.Equiv a.raw :=
      trans (mul_assoc c b a)
        (trans (mul_congr hcb (ComplexRaw.equiv_refl _ a.valid)) (one_mul a))
    induction q with
    | nil =>
        exact .cons (ComplexRaw.equiv_symm (mul_one c)) .nil
    | cons a q ih =>
        exact .cons (ComplexRaw.equiv_symm (recover a)) ih
  exact trans (eval_equiv hcoeff (ComplexRaw.equiv_refl _ x.valid)) (eval_scale c _ x)

/-- Every nonzero leading coefficient admits monic normalization. The finite
inverse certificate is constructed beneath the exact public statement. -/
theorem exists_monic_normalization (q : Coefficients) (c : ComplexCert)
    (hc : ¬ c.raw.Equiv zero.raw) :
    ∃ p : Coefficients, Monic p ∧ p.length = q.length + 1 ∧
      ∀ x : ComplexCert, (eval (q ++ [c]) x).raw.Equiv (mul c (eval p x)).raw := by
  obtain ⟨b, hb⟩ := exists_inverse c hc
  refine ⟨normalize q b, ⟨q.map (mul b), rfl⟩, ?_, normalize_spec q c b hb⟩
  simp [normalize]

/-- Conditional complete factorization for arbitrary nonzero leading
coefficients. Only the monic root-existence theorem is still assumed. -/
theorem factorization_nonzero_leading_of_root_existence (hroot : MonicRootExistence)
    (q : Coefficients) (c : ComplexCert) (hc : ¬ c.raw.Equiv zero.raw) :
    ∃ roots : List ComplexCert, roots.length = q.length ∧
      ∀ x : ComplexCert, (eval (q ++ [c]) x).raw.Equiv (mul c (rootProduct roots x)).raw := by
  obtain ⟨p, hp, hlen, heval⟩ := exists_monic_normalization q c hc
  obtain ⟨roots, hroots, hfactor⟩ := factorization_of_root_existence hroot p hp
  refine ⟨roots, by omega, ?_⟩
  intro x
  exact trans (heval x) (mul_congr (ComplexRaw.equiv_refl _ c.valid) (hfactor x))

private theorem inverse_recover (a w b : ComplexCert)
    (haw : (mul a w).raw.Equiv one.raw) : (mul w (mul a b)).raw.Equiv b.raw := by
  have hperm : (mul w (mul a b)).raw.Equiv (mul (mul a w) b).raw := by
    apply Expression.equiv_of_samples
      (.mul (.parameter w) (.mul (.parameter a) (.parameter b)))
      (.mul (.mul (.parameter a) (.parameter w)) (.parameter b))
    intro s
    apply qext <;> simp [Expression.sample, QComplex.mul] <;> grind
  exact trans hperm (trans (mul_congr haw (ComplexRaw.equiv_refl _ b.valid)) (one_mul b))

/-- Multiplication by any nonzero represented coefficient is cancellable. -/
theorem mul_cancel_left_of_nonzero {a b c : ComplexCert}
    (ha : ¬ a.raw.Equiv zero.raw) (h : (mul a b).raw.Equiv (mul a c).raw) :
    b.raw.Equiv c.raw := by
  obtain ⟨w, hw⟩ := exists_inverse a ha
  exact trans (ComplexRaw.equiv_symm (inverse_recover a w b hw))
    (trans (mul_congr (ComplexRaw.equiv_refl _ w.valid) h) (inverse_recover a w c hw))

/-- The construction is independent of the successful norm-test stage. -/
theorem inverseAt_equiv (a : ComplexCert) (ha : ¬ a.raw.Equiv zero.raw)
    (N M : Nat) (hN : 0 < ((normValue a).real.compute N).lo)
    (hM : 0 < ((normValue a).real.compute M).lo) :
    (inverseAt a N hN).raw.Equiv (inverseAt a M hM).raw := by
  apply mul_cancel_left_of_nonzero ha
  exact trans (mul_inverseAt a N hN) (ComplexRaw.equiv_symm (mul_inverseAt a M hM))

/-- Reciprocals respect equality of arbitrary valid input representatives. -/
theorem inverseAt_input_equiv {a b : ComplexCert} (hab : a.raw.Equiv b.raw)
    (ha : ¬ a.raw.Equiv zero.raw)
    (N M : Nat) (hN : 0 < ((normValue a).real.compute N).lo)
    (hM : 0 < ((normValue b).real.compute M).lo) :
    (inverseAt a N hN).raw.Equiv (inverseAt b M hM).raw := by
  apply mul_cancel_left_of_nonzero ha
  exact trans (mul_inverseAt a N hN)
    (ComplexRaw.equiv_symm (trans
      (mul_congr hab (ComplexRaw.equiv_refl _ (inverseAt b M hM).valid))
      (mul_inverseAt b M hM)))

/-- No nonzero represented complex factors have zero product. -/
theorem mul_nonzero {a b : ComplexCert}
    (ha : ¬ a.raw.Equiv zero.raw) (hb : ¬ b.raw.Equiv zero.raw) :
    ¬ (mul a b).raw.Equiv zero.raw := by
  intro h
  apply hb
  apply mul_cancel_left_of_nonzero (a := a) ha
  have hz : (mul a zero).raw.Equiv zero.raw := by
    apply Expression.equiv_of_samples (.mul (.parameter a) (.constant QComplex.zero))
      (.constant QComplex.zero)
    intro s
    apply qext <;> simp [Expression.sample, QComplex.mul, QComplex.zero] <;> grind
  exact trans h (ComplexRaw.equiv_symm hz)

end ComputableAnalysis.RepresentedPolynomial
