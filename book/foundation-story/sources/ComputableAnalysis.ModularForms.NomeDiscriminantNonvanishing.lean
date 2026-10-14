import ComputableAnalysis.ModularForms.NomeDiscriminantLeadingTerm
import ComputableAnalysis.RiemannHilbert.NonzeroBoxSearch

/-! Justified nonvanishing from the actual discriminant error and coordinate separation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

/-- A supplied rational box outside the coordinate bound refutes that exact bound. -/
theorem scalar_not_small_of_box (q : Scalar) (E : Rat) (N : Nat)
    (h : E<(q.val.compute N).lo.re ∨ (q.val.compute N).hi.re< -E ∨
      E<(q.val.compute N).lo.im ∨ (q.val.compute N).hi.im< -E) : ¬Small q.val E := by
  intro hs
  have hrelo := hs.2.1 N 0
  have hrehi := hs.1 0 N
  have himlo := hs.2.2.2 N 0
  have himhi := hs.2.2.1 0 N
  change (q.val.compute N).lo.re≤E at hrelo
  change -E≤(q.val.compute N).hi.re at hrehi
  change (q.val.compute N).lo.im≤E at himlo
  change -E≤(q.val.compute N).hi.im at himhi
  rcases h with h | h | h | h <;> grind only

/-- A supplied approximation error smaller than a justified coordinate separation proves nonvanishing. -/
theorem scalar_nonzero_of_small_difference (x q : Scalar) (E : Rat)
    (hd : Small (sub x.val q.val) E) (hq : ¬Small q.val E) : NonzeroBoxSearch.Nonzero x := by
  intro hx
  have hX := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := x.property) (hright := ofQComplex_valid _) hx
  have he : (neg (sub x.val q.val)).Equiv q.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := neg_valid (sub_valid x.property q.property))
      (hright := q.property)
    let X := ComplexRawQuotient.ofRaw x.val x.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change X=0 at hX
    change -(X-Q)=Q
    rw [hX]
    grind only
  exact hq (Small.congr (neg_valid (sub_valid x.property q.property)) q.property he (SeriesLimitLaws.small_neg hd))

/-- The constructed Fourier discriminant is nonzero when the actual nome is separated from its certified error. -/
theorem nomeModularDiscriminant_nonzero_of_separation (q : Scalar) (r : Rat) (hr : 0≤r)
    (hg : 128*r≤(1:Rat)/2) (hq : Small q.val r) (hsmall : r≤(1:Rat)/65536)
    (hsep : ¬Small q.val (9000*r*r)) :
    NonzeroBoxSearch.Nonzero (nomeModularDiscriminant q r hr hg hq) :=
  scalar_nonzero_of_small_difference _ q _ (nomeModularDiscriminant_linear_bound q r hr hg hq hsmall) hsep

/-- A concrete rational box certifies nonvanishing of the actual Fourier discriminant. -/
theorem nomeModularDiscriminant_nonzero_of_box (q : Scalar) (r : Rat) (hr : 0≤r)
    (hg : 128*r≤(1:Rat)/2) (hq : Small q.val r) (hsmall : r≤(1:Rat)/65536) (N : Nat)
    (hsep : 9000*r*r<(q.val.compute N).lo.re ∨ (q.val.compute N).hi.re< -(9000*r*r) ∨
      9000*r*r<(q.val.compute N).lo.im ∨ (q.val.compute N).hi.im< -(9000*r*r)) :
    NonzeroBoxSearch.Nonzero (nomeModularDiscriminant q r hr hg hq) :=
  nomeModularDiscriminant_nonzero_of_separation q r hr hg hq hsmall (scalar_not_small_of_box q _ N hsep)

end ComputableAnalysis.ModularForms
