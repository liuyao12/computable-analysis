import ComputableAnalysis.FTA.Normalization
import ComputableAnalysis.PowerSeries
import ComputableAnalysis.HolomorphicJet

/-! Finite Taylor translation by repeated synthetic division. Coefficients
remain arbitrary represented complex numbers; all identities are exact. -/
namespace ComputableAnalysis.RepresentedPolynomial
open Arithmetic

/-- Coefficients after translating the argument by `r`, computed by repeated
synthetic division. The recursion consumes one coefficient at each step. -/
def translate (r : ComplexCert) (p : Coefficients) : Coefficients :=
  match p with
  | [] => []
  | c :: p =>
      let qr := syntheticDivide r (c::p)
      qr.2 :: translate r qr.1
termination_by p.length
decreasing_by rw [syntheticDivide_length]; simp

theorem translate_length (r : ComplexCert) (p : Coefficients) :
    (translate r p).length = p.length := by
  cases p with
  | nil => rw [translate]
  | cons c p =>
      rw [translate]
      simp only [List.length_cons]
      rw [translate_length, syntheticDivide_length]
      simp
termination_by p.length
decreasing_by rw [syntheticDivide_length]; simp

private theorem trans {a b c : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hbc : b.raw.Equiv c.raw) : a.raw.Equiv c.raw :=
  ComplexRaw.equiv_trans a.valid b.valid c.valid hab hbc

private theorem add_congr {a b c d : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (add a c).raw.Equiv (add b d).raw := ComplexRaw.add_equiv hab hcd

private theorem mul_congr {a b c d : ComplexCert}
    (hab : a.raw.Equiv b.raw) (hcd : c.raw.Equiv d.raw) :
    (mul a c).raw.Equiv (mul b d).raw :=
  ComplexRaw.mul_equiv a.valid b.valid c.valid d.valid hab hcd

private theorem add_sub_cancel (r x : ComplexCert) : (sub (add r x) r).raw.Equiv x.raw := by
  apply Expression.equiv_of_samples
    (.add (.add (.parameter r) (.parameter x)) (.neg (.parameter r))) (.parameter x)
  intro s
  cases hr : s r
  cases hx : s x
  simp [Expression.sample, hr, hx, QComplex.add, QComplex.neg]
  constructor <;> grind

/-- Exact translation identity at every represented argument. -/
theorem translate_eval (r : ComplexCert) (p : Coefficients) (x : ComplexCert) :
    (eval p (add r x)).raw.Equiv (eval (translate r p) x).raw := by
  cases p with
  | nil => rw [translate]; exact ComplexRaw.equiv_refl _ zero.valid
  | cons c p =>
      rw [translate]
      exact trans (syntheticDivide_spec r (add r x) (c::p))
        (add_congr (ComplexRaw.equiv_refl _ (syntheticDivide r (c::p)).2.valid)
          (mul_congr (add_sub_cancel r x) (translate_eval r (syntheticDivide r (c::p)).1 x)))
termination_by p.length
decreasing_by rw [syntheticDivide_length]; simp

/-- Translation preserves a canonical monic leading coefficient literally. -/
theorem translate_monic (r : ComplexCert) (p : Coefficients) (hp : Monic p) :
    Monic (translate r p) := by
  by_cases hlen : 2 ≤ p.length
  · cases p with
    | nil => simp at hlen
    | cons c p =>
        rw [translate]
        obtain ⟨q, hq⟩ := translate_monic r (syntheticDivide r (c::p)).1
          (syntheticDivide_monic r (c::p) hp hlen)
        exact ⟨(syntheticDivide r (c::p)).2 :: q, by rw [hq]; rfl⟩
  · obtain ⟨q, rfl⟩ := hp
    have hlen' : ¬ 2 ≤ q.length + 1 := by simpa only [List.length_append, List.length_cons, List.length_nil] using hlen
    have hq : q = [] := List.length_eq_zero_iff.mp (by omega)
    subst q
    exact ⟨[], by simp [translate, syntheticDivide]⟩
termination_by p.length
decreasing_by rw [syntheticDivide_length]; simp_all

private theorem one_nonzero : ¬ one.raw.Equiv zero.raw := by
  intro h
  have hh := (ComplexRaw.compareAt_overlap_iff _ _ 0 0).1 (h 0)
  have hb : (1 : Rat) ≤ 0 := hh.1.1
  contradiction

private theorem one_mul (a : ComplexCert) : (mul one a).raw.Equiv a.raw := by
  apply Expression.equiv_of_samples (.mul (.constant QComplex.one) (.parameter a)) (.parameter a)
  intro s
  exact QComplex.one_mul_cert _

private theorem combine_power (h : QComplex) (n : Nat) (a : ComplexCert) :
    (mul (ofQComplex h) (mul (ofQComplex (QComplex.pow h n)) a)).raw.Equiv
      (mul (ofQComplex (QComplex.pow h (n+1))) a).raw := by
  apply Expression.equiv_of_samples
    (.mul (.constant h) (.mul (.constant (QComplex.pow h n)) (.parameter a)))
    (.mul (.constant (QComplex.pow h (n+1))) (.parameter a))
  intro s
  exact (QComplex.mul_assoc_cert _ _ _).symm

/-- A monic polynomial has a first nonzero coefficient. Its initial zero
coefficients can be removed as an exact power factor. The choice is confined
to an existence proof; no runtime equality test on raw numbers is introduced. -/
theorem first_nonzero_expansion (p : Coefficients) (hp : Monic p) :
    ∃ n : Nat, ∃ a : ComplexCert, ∃ q : Coefficients,
      (¬ a.raw.Equiv zero.raw) ∧ ∀ h : QComplex,
      (eval p (ofQComplex h)).raw.Equiv
        (mul (ofQComplex (QComplex.pow h n))
          (add a (mul (ofQComplex h) (eval q (ofQComplex h))))).raw := by
  classical
  obtain ⟨initialCoeffs, rfl⟩ := hp
  induction initialCoeffs with
  | nil =>
      refine ⟨0, one, [], one_nonzero, ?_⟩
      intro h
      exact ComplexRaw.equiv_symm (one_mul (eval [one] (ofQComplex h)))
  | cons c initialCoeffs ih =>
      by_cases hc : c.raw.Equiv zero.raw
      · obtain ⟨n, a, q, ha, hexp⟩ := ih
        refine ⟨n+1, a, q, ha, ?_⟩
        intro h
        have hdrop : (eval ((c::initialCoeffs)++[one]) (ofQComplex h)).raw.Equiv
            (mul (ofQComplex h) (eval (initialCoeffs++[one]) (ofQComplex h))).raw :=
          trans (add_congr hc (ComplexRaw.equiv_refl _
            (mul (ofQComplex h) (eval (initialCoeffs++[one]) (ofQComplex h))).valid))
            (zero_add _)
        exact trans hdrop (trans
          (mul_congr (ComplexRaw.equiv_refl _ (ofQComplex h).valid) (hexp h))
          (combine_power h n _))
      · refine ⟨0, c, initialCoeffs++[one], hc, ?_⟩
        intro h
        exact ComplexRaw.equiv_symm (one_mul (eval ((c::initialCoeffs)++[one]) (ofQComplex h)))

/-- Every nonconstant monic polynomial has an exact local expansion with a
nonzero leading varying coefficient at every represented centre. -/
theorem local_expansion (p : Coefficients) (hp : Monic p) (hdegree : 2 ≤ p.length)
    (r : ComplexCert) :
    ∃ c a : ComplexCert, ∃ q : Coefficients, ∃ k : Nat,
      0 < k ∧ (¬ a.raw.Equiv zero.raw) ∧ c.raw.Equiv (eval p r).raw ∧
      ∀ h : QComplex, (eval p (add r (ofQComplex h))).raw.Equiv
        (add c (mul (ofQComplex (QComplex.pow h k))
          (add a (mul (ofQComplex h) (eval q (ofQComplex h)))))).raw := by
  let quotient := (syntheticDivide r p).1
  have hq : Monic quotient := syntheticDivide_monic r p hp hdegree
  obtain ⟨n, a, q, ha, he⟩ := first_nonzero_expansion (translate r quotient) (translate_monic r quotient hq)
  refine ⟨(syntheticDivide r p).2, a, q, n+1, by omega, ha, syntheticDivide_remainder r p, ?_⟩
  intro h
  have htail := trans (translate_eval r quotient (ofQComplex h)) (he h)
  exact trans (syntheticDivide_spec r (add r (ofQComplex h)) p)
    (add_congr (ComplexRaw.equiv_refl _ (syntheticDivide r p).2.valid)
      (trans (mul_congr (add_sub_cancel r (ofQComplex h)) htail) (combine_power h n _)))

end ComputableAnalysis.RepresentedPolynomial
