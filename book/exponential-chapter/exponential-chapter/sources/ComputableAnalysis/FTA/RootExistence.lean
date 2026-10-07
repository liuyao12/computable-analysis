import ComputableAnalysis.FTA.LocalDescent
import ComputableAnalysis.FTA.Translation

/-! Fundamental theorem of algebra over the represented-complex foundation.
A minimum of squared modulus is constructed by finite rational searches; an
exact local expansion and a certified rational decrease rule out a nonzero
minimum. No ambient real or complex completion is imported. -/
namespace ComputableAnalysis.RepresentedPolynomial

/-- Squared modulus respects equality of represented complex values. -/
theorem normValue_equiv {z w : ComplexCert} (h : z.raw.Equiv w.raw) :
    (normValue z).real.preferred.Equiv (normValue w).real.preferred := by
  have hzr := ComplexRaw.realPart_valid z.valid
  have hzi := ComplexRaw.imagPart_valid z.valid
  have hwr := ComplexRaw.realPart_valid w.valid
  have hwi := ComplexRaw.imagPart_valid w.valid
  have hr := ComplexRaw.realPart_equiv h
  have hi := ComplexRaw.imagPart_equiv h
  exact RealRaw.add_equiv (RealRaw.mul_valid hzr hzr) (RealRaw.mul_valid hwr hwr)
    (RealRaw.mul_valid hzi hzi) (RealRaw.mul_valid hwi hwi)
    (RealRaw.mul_equiv hzr hwr hzr hwr hr hr)
    (RealRaw.mul_equiv hzi hwi hzi hwi hi hi)

/-- Every nonconstant monic polynomial with arbitrary represented complex
coefficients has an exact represented complex root. -/
theorem monic_root_existence : MonicRootExistence := by
  classical
  intro p hp hdegree
  obtain ⟨q, rfl⟩ := hp
  have hq : 0 < q.length := by
    have hd : 2 ≤ q.length+1 := by simpa using hdegree
    omega
  obtain ⟨r, hmin⟩ := exists_minimum_modulus q hq
  refine ⟨r, ?_⟩
  apply Classical.byContradiction
  intro hnonzero
  obtain ⟨c, a, tail, k, hk, ha, hc, hexp⟩ :=
    local_expansion (q++[one]) ⟨q, rfl⟩ hdegree r
  have hc0 : ¬ c.raw.Equiv zero.raw := by
    intro h
    apply hnonzero
    exact ComplexRaw.equiv_trans (eval (q++[one]) r).valid c.valid zero.valid
      (ComplexRaw.equiv_symm hc) h
  obtain ⟨h, n, hdecrease⟩ := exists_local_decrease c a tail k hc0 ha hk
  let w := add r (ofQComplex h)
  let e := localValue c a tail k h
  have hce : (normValue c).real.preferred.Equiv
      (normValue (eval (q++[one]) r)).real.preferred := normValue_equiv hc
  have hwe : (normValue (eval (q++[one]) w)).real.preferred.Equiv
      (normValue e).real.preferred := normValue_equiv (hexp h)
  have hle : (normValue c).real.preferred.Le (normValue e).real.preferred :=
    RealRaw.le_trans (normValue (eval (q++[one]) r)).real.valid
      (RealRaw.le_of_equiv (normValue c).real.valid (normValue (eval (q++[one]) r)).real.valid hce)
      (RealRaw.le_trans (normValue (eval (q++[one]) w)).real.valid (hmin w)
        (RealRaw.le_of_equiv (normValue (eval (q++[one]) w)).real.valid (normValue e).real.valid hwe))
  have hb := hle n n
  change ((normValue c).real.compute n).lo ≤ ((normValue (localValue c a tail k h)).real.compute n).hi at hb
  grind

/-- Complete splitting of every monic polynomial, counting multiplicities. -/
theorem monic_factorization (p : Coefficients) (hp : Monic p) :
    ∃ roots : List ComplexCert, roots.length = p.length-1 ∧
      ∀ x : ComplexCert, (eval p x).raw.Equiv (rootProduct roots x).raw :=
  factorization_of_root_existence monic_root_existence p hp

/-- Complete complex factorization for arbitrary nonzero leading coefficients.
The factorization identity holds at every represented complex argument. -/
theorem complex_factorization (q : Coefficients) (c : ComplexCert)
    (hc : ¬ c.raw.Equiv zero.raw) :
    ∃ roots : List ComplexCert, roots.length = q.length ∧
      ∀ x : ComplexCert, (eval (q++[c]) x).raw.Equiv (mul c (rootProduct roots x)).raw :=
  factorization_nonzero_leading_of_root_existence monic_root_existence q c hc

/-- Fundamental theorem of algebra for an arbitrary nonconstant coefficient
list with nonzero leading coefficient. -/
theorem exists_root (q : Coefficients) (c : ComplexCert) (hq : 0 < q.length)
    (hc : ¬ c.raw.Equiv zero.raw) : ∃ z : ComplexCert, Root (q++[c]) z := by
  obtain ⟨p, hp, hlen, hnorm⟩ := exists_monic_normalization q c hc
  obtain ⟨z, hz⟩ := monic_root_existence p hp (by omega)
  refine ⟨z, ?_⟩
  have hm : (mul c (eval p z)).raw.Equiv (mul c zero).raw :=
    ComplexRaw.mul_equiv c.valid c.valid (eval p z).valid zero.valid (ComplexRaw.equiv_refl _ c.valid) hz
  have hzero : (mul c zero).raw.Equiv zero.raw := by
    apply Arithmetic.Expression.equiv_of_samples
      (.mul (.parameter c) (.constant QComplex.zero)) (.constant QComplex.zero)
    intro s
    simp [Arithmetic.Expression.sample, QComplex.mul, QComplex.zero]
    grind
  exact ComplexRaw.equiv_trans (eval (q++[c]) z).valid (mul c (eval p z)).valid zero.valid (hnorm z)
    (ComplexRaw.equiv_trans (mul c (eval p z)).valid (mul c zero).valid zero.valid hm hzero)

end ComputableAnalysis.RepresentedPolynomial
