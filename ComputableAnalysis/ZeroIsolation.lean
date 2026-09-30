import ComputableAnalysis.HolomorphicFoundation

/-! Exact zero location from reflection and uniqueness. No argument principle,
completed zeta evaluator, or zero-count computation is asserted by this module. -/
namespace ComputableAnalysis.FunctionTheory.ZeroIsolation

/-- Reflection in the critical line, preserving the imaginary coordinate. -/
def reflection (z : ComplexRaw) : ComplexRaw :=
  ComplexRaw.sub (ComplexRaw.ofQComplex ⟨1,0⟩) (ComplexRaw.conj z)

theorem reflection_valid {z : ComplexRaw} (hz : z.Valid) : (reflection z).Valid :=
  ComplexRaw.sub_valid (ComplexRaw.ofQComplex_valid _) (ComplexRaw.conj_valid z hz)

/-- A fixed point of reflection has real coordinate exactly one half.
The hypothesis is equality of represented values, not a small numerical gap. -/
theorem fixed_realPart {z : ComplexRaw} (hz : z.Equiv (reflection z)) :
    z.realPart.Equiv (RealRaw.ofRat (1/2)) := by
  intro n
  have h := (ComplexRaw.compareAt_overlap_iff z (reflection z) n n).1 (hz n)
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change (z.compute n).lo.re ≤ 1/2 ∧ 1/2 ≤ (z.compute n).hi.re
  simp only [reflection,ComplexRaw.sub,ComplexRaw.add,ComplexRaw.neg,ComplexRaw.conj,
    ComplexRaw.ofQComplex,QBox.add,QBox.neg,QBox.conj,QBox.point,
    QBox.Overlaps,QComplex.le_def,QComplex.add,QComplex.neg,QComplex.conj] at h
  constructor <;> grind only

/-- A reflected zero is still a zero, when the supplied function has the
reflection-conjugation symmetry. -/
theorem reflected_zero (f : Map) {z : ComplexRaw} (hz : z.Valid)
    (hDz : f.domain z) (hDr : f.domain (reflection z))
    (hsym : (f.eval (reflection z)).Equiv (ComplexRaw.conj (f.eval z)))
    (hzero : (f.eval z).Equiv ComplexRaw.zero) :
    (f.eval (reflection z)).Equiv ComplexRaw.zero := by
  have hc := ComplexRaw.conj_equiv hzero
  have hc0 : (ComplexRaw.conj ComplexRaw.zero).Equiv ComplexRaw.zero := by
    intro n; rfl
  exact ComplexRaw.equiv_trans (f.valid _ (reflection_valid hz) hDr)
    (ComplexRaw.conj_valid (f.eval z) (f.valid _ hz hDz)) (ComplexRaw.ofQComplex_valid _)
    hsym (ComplexRaw.equiv_trans (ComplexRaw.conj_valid (f.eval z) (f.valid _ hz hDz))
      (ComplexRaw.conj_valid ComplexRaw.zero (ComplexRaw.ofQComplex_valid _))
      (ComplexRaw.ofQComplex_valid _) hc hc0)

/-- Uniqueness in a reflection-stable isolating region forces an exact point
on the critical line. Existence, isolation, and symmetry are separate evidence;
none of them is obtained here from sampled values or an assumed zero count. -/
theorem unique_zero_on_line (f : Map) (R : ComplexRaw → Prop)
    {z : ComplexRaw} (hz : z.Valid) (hDz : f.domain z) (hRz : R z)
    (hzero : (f.eval z).Equiv ComplexRaw.zero)
    (hDr : f.domain (reflection z)) (hRr : R (reflection z))
    (hsym : (f.eval (reflection z)).Equiv (ComplexRaw.conj (f.eval z)))
    (hunique : ∀ w, w.Valid → f.domain w → R w →
      (f.eval w).Equiv ComplexRaw.zero → w.Equiv z) :
    z.realPart.Equiv (RealRaw.ofRat (1/2)) := by
  have hrzero := reflected_zero f hz hDz hDr hsym hzero
  exact fixed_realPart (ComplexRaw.equiv_symm
    (hunique (reflection z) (reflection_valid hz) hDr hRr hrzero))

end ComputableAnalysis.FunctionTheory.ZeroIsolation
