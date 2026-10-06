import ComputableAnalysis.RiemannHilbert.DomainFunctions
import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

/-! Composition of domain-dependent executable maps, with its exact
first-order remainder identity. Domain evidence is transported by
representation invariance, rather than chosen by an evaluator. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def composeDomain (f g : Map) (z : Scalar) : Prop :=
  ∃ hg : g.domain z, f.domain (g.eval z hg)

theorem compose_inner_mem {f g : Map} {z : Scalar} (hz : composeDomain f g z) : g.domain z := by
  obtain ⟨hg,_⟩ := hz
  exact hg

theorem compose_outer_mem {f g : Map} {z : Scalar} (hz : composeDomain f g z) :
    f.domain (g.eval z (compose_inner_mem hz)) := by
  obtain ⟨hg,hf⟩ := hz
  exact hf

def compose (f g : Map) : Map where
  domain := composeDomain f g
  eval z hz := f.eval (g.eval z (compose_inner_mem hz)) (compose_outer_mem hz)
  domain_congr z w hzw := by
    constructor
    · rintro ⟨hz,hfz⟩
      have hw := (g.domain_congr z w hzw).1 hz
      exact ⟨hw, (f.domain_congr _ _ (g.eval_congr z w hz hw hzw)).1 hfz⟩
    · rintro ⟨hw,hfw⟩
      have hz := (g.domain_congr z w hzw).2 hw
      exact ⟨hz, (f.domain_congr _ _ (g.eval_congr z w hz hw hzw)).2 hfw⟩
  eval_congr z w hz hw hzw := f.eval_congr _ _ (compose_outer_mem hz) (compose_outer_mem hw)
    (g.eval_congr z w (compose_inner_mem hz) (compose_inner_mem hw) hzw)

def scalarProduct (a b : Scalar) : Scalar :=
  ⟨mul a.val b.val, mul_valid a.property b.property⟩

theorem remainder_valid (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar)
    (z : Scalar) (hz : f.domain z) : (remainder f a ha d z hz).Valid :=
  sub_valid (sub_valid (f.eval z hz).property (f.eval a ha).property)
    (mul_valid d.property (sub_valid z.property a.property))

theorem compose_remainder (f g : Map) (a : Scalar) (ha : composeDomain f g a)
    (df dg : Scalar) (z : Scalar) (hz : composeDomain f g z) :
    (remainder (compose f g) a ha (scalarProduct df dg) z hz).Equiv
      (add (remainder f (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha) df
        (g.eval z (compose_inner_mem hz)) (compose_outer_mem hz))
        (mul df.val (remainder g a (compose_inner_mem ha) dg z (compose_inner_mem hz)))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := remainder_valid _ _ _ _ _ _)
    (hright := add_valid (remainder_valid _ _ _ _ _ _)
      (mul_valid df.property (remainder_valid _ _ _ _ _ _)))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let GA := ComplexRawQuotient.ofRaw (g.eval a (compose_inner_mem ha)).val (g.eval a (compose_inner_mem ha)).property
  let GZ := ComplexRawQuotient.ofRaw (g.eval z (compose_inner_mem hz)).val (g.eval z (compose_inner_mem hz)).property
  let FA := ComplexRawQuotient.ofRaw ((compose f g).eval a ha).val ((compose f g).eval a ha).property
  let FZ := ComplexRawQuotient.ofRaw ((compose f g).eval z hz).val ((compose f g).eval z hz).property
  let DF := ComplexRawQuotient.ofRaw df.val df.property
  let DG := ComplexRawQuotient.ofRaw dg.val dg.property
  change (FZ + -FA) + -((DF*DG)*(Z + -A)) =
    ((FZ + -FA) + -(DF*(GZ + -GA))) + DF*((GZ + -GA) + -(DG*(Z + -A)))
  grind

end ComputableAnalysis.RiemannHilbert.DomainFunctions
