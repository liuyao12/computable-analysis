import ComputableAnalysis.ComplexMultiplication

/-!
# Holomorphic represented functions

Our working holomorphicity interface supplies complex-linear first-order
approximation at every valid represented point of an open domain, together
with a represented derivative and its local continuity moduli. Rational coordinate bounds express the
estimate without a completed norm or field. Derivative witnesses carry an
explicit positive rational radius for each requested rational error.

This definition does not assume a power series, Cauchy formula, or contour
identity. Formal jets alone do not inhabit it. Raw evaluators and radius
functions preserve executable data when their supplied implementations do;
their function types alone are not computability certificates.
-/
namespace ComputableAnalysis.FunctionTheory

open ComplexRaw

/-- Exact closed coordinate bound, not a bound on an arbitrarily early box.
For valid inputs this says both represented coordinates lie in `[-r,r]`. -/
def Small (z : ComplexRaw) (r : Rat) : Prop :=
  (RealRaw.ofRat (-r)).Le z.realPart ∧ z.realPart.Le (RealRaw.ofRat r) ∧
  (RealRaw.ofRat (-r)).Le z.imagPart ∧ z.imagPart.Le (RealRaw.ofRat r)

theorem Small.congr {z w : ComplexRaw} {r : Rat}
    (hz : z.Valid) (hw : w.Valid) (hzw : z.Equiv w) (h : Small z r) :
    Small w r := by
  have hr := ComplexRaw.realPart_equiv hzw
  have hi := ComplexRaw.imagPart_equiv hzw
  have hzr := realPart_valid hz
  have hwr := realPart_valid hw
  have hzi := imagPart_valid hz
  have hwi := imagPart_valid hw
  exact ⟨RealRaw.le_trans hzr h.1 (RealRaw.le_of_equiv hzr hwr hr),
    RealRaw.le_trans hzr (RealRaw.le_of_equiv hwr hzr (RealRaw.equiv_symm hr)) h.2.1,
    RealRaw.le_trans hzi h.2.2.1 (RealRaw.le_of_equiv hzi hwi hi),
    RealRaw.le_trans hzi (RealRaw.le_of_equiv hwi hzi (RealRaw.equiv_symm hi)) h.2.2.2⟩

theorem Small.zero {r : Rat} (hr : 0 ≤ r) : Small ComplexRaw.zero r := by
  constructor
  · intro n m; change -r ≤ 0; grind
  constructor
  · intro n m; exact hr
  constructor
  · intro n m; change -r ≤ 0; grind
  · intro n m; exact hr

theorem Small.mono {z : ComplexRaw} {r s : Rat}
    (h : Small z r) (hrs : r ≤ s) : Small z s := by
  rcases h with ⟨h1,h2,h3,h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m; exact Rat.le_trans (Rat.neg_le_neg hrs) (h1 n m)
  · intro n m; exact Rat.le_trans (h2 n m) hrs
  · intro n m; exact Rat.le_trans (Rat.neg_le_neg hrs) (h3 n m)
  · intro n m; exact Rat.le_trans (h4 n m) hrs

/-- A partial represented map; its values and domain respect equivalence.
The total evaluator's behavior outside the stated domain is irrelevant. -/
structure Map where
  domain : ComplexRaw → Prop
  eval : ComplexRaw → ComplexRaw
  valid : ∀ z, z.Valid → domain z → (eval z).Valid
  domain_congr : ∀ {z w}, z.Valid → w.Valid → z.Equiv w → (domain z ↔ domain w)
  eval_congr : ∀ {z w}, z.Valid → w.Valid → domain z → domain w →
    z.Equiv w → (eval z).Equiv (eval w)

/-- Supplied rational neighborhoods of every valid domain point. -/
structure OpenDomain (f : Map) where
  radius : ∀ a, a.Valid → f.domain a → QPos
  inside : ∀ a ha hfa z, z.Valid → Small (sub z a) (radius a ha hfa).val → f.domain z

/-- First-order error for the proposed derivative `d`. -/
def remainder (f : Map) (a d z : ComplexRaw) : ComplexRaw :=
  sub (sub (f.eval z) (f.eval a)) (mul d (sub z a))

theorem remainder_valid (f : Map) {a d z : ComplexRaw}
    (ha : a.Valid) (hd : d.Valid) (hz : z.Valid)
    (hfa : f.domain a) (hfz : f.domain z) : (remainder f a d z).Valid :=
  sub_valid (sub_valid (f.valid z hz hfz) (f.valid a ha hfa))
    (mul_valid hd (sub_valid hz ha))

theorem sub_congr {a b c d : ComplexRaw} (hab : a.Equiv b) (hcd : c.Equiv d) :
    (sub a c).Equiv (sub b d) := add_equiv hab (neg_equiv hcd)

/-- A complex derivative with explicit error-to-radius data.
The estimate ranges over *all* represented complex neighbors and all positive
rational upper bounds on their displacement, not just a coordinate direction.
No continuity of the derivative or uniformity across the domain is assumed. -/
structure HasDerivativeAt (f : Map) (a d : ComplexRaw) where
  point_valid : a.Valid
  point_mem : f.domain a
  derivative_valid : d.Valid
  delta : QPos → QPos
  estimate : ∀ (eps H : QPos) (z : ComplexRaw), z.Valid → f.domain z →
    H.val ≤ (delta eps).val → Small (sub z a) H.val →
    Small (remainder f a d z) (eps.val * H.val)

/-- Supplied local continuity moduli on a represented domain. -/
structure ContinuousOn (domain : ComplexRaw → Prop) (g : ComplexRaw → ComplexRaw) where
  delta : ∀ a, a.Valid → domain a → QPos → QPos
  estimate : ∀ a ha hfa (eps : QPos) z, z.Valid → domain z →
    Small (sub z a) (delta a ha hfa eps).val → Small (sub (g z) (g a)) eps.val

/-- Our working holomorphic interface supplies a continuous complex derivative.
This is deliberately stronger data than bare pointwise differentiability;
no equivalence with the weakest classical definition is claimed here. -/
structure Holomorphic (f : Map) where
  openDomain : OpenDomain f
  derivative : ComplexRaw → ComplexRaw
  atPoint : ∀ a, a.Valid → f.domain a → HasDerivativeAt f a (derivative a)
  derivative_congr : ∀ {a b}, a.Valid → b.Valid → f.domain a → f.domain b →
    a.Equiv b → (derivative a).Equiv (derivative b)
  continuousDerivative : ContinuousOn f.domain derivative

/-- Changing the name of a derivative preserves the full quantitative law. -/
def HasDerivativeAt.congrDerivative {f : Map} {a d e : ComplexRaw}
    (h : HasDerivativeAt f a d) (he : e.Valid) (hde : d.Equiv e) :
    HasDerivativeAt f a e where
  point_valid := h.point_valid
  point_mem := h.point_mem
  derivative_valid := he
  delta := h.delta
  estimate := by
    intro eps H z hz hfz hH hza
    apply Small.congr (remainder_valid f h.point_valid h.derivative_valid hz h.point_mem hfz)
      (remainder_valid f h.point_valid he hz h.point_mem hfz) _ (h.estimate eps H z hz hfz hH hza)
    apply sub_congr (equiv_refl _ (sub_valid (f.valid z hz hfz)
      (f.valid a h.point_valid h.point_mem)))
    exact mul_equiv h.derivative_valid he (sub_valid hz h.point_valid)
      (sub_valid hz h.point_valid) hde (equiv_refl _ (sub_valid hz h.point_valid))

/-- The same derivative estimate at an equivalent represented base point. -/
def HasDerivativeAt.congrPoint {f : Map} {a b d : ComplexRaw}
    (h : HasDerivativeAt f a d) (hb : b.Valid) (hab : a.Equiv b) :
    HasDerivativeAt f b d where
  point_valid := hb
  point_mem := (f.domain_congr h.point_valid hb hab).mp h.point_mem
  derivative_valid := h.derivative_valid
  delta := h.delta
  estimate := by
    intro eps H z hz hfz hH hzb
    have hfb := (f.domain_congr h.point_valid hb hab).mp h.point_mem
    have hs := sub_congr (equiv_refl z hz) hab
    have hza := Small.congr (sub_valid hz hb) (sub_valid hz h.point_valid)
      (equiv_symm hs) hzb
    apply Small.congr (remainder_valid f h.point_valid h.derivative_valid hz h.point_mem hfz)
      (remainder_valid f hb h.derivative_valid hz hfb hfz) _ (h.estimate eps H z hz hfz hH hza)
    exact sub_congr (sub_congr (equiv_refl _ (f.valid z hz hfz))
      (f.eval_congr h.point_valid hb h.point_mem hfb hab))
      (mul_equiv h.derivative_valid h.derivative_valid (sub_valid hz h.point_valid)
        (sub_valid hz hb) (equiv_refl d h.derivative_valid) hs)

end ComputableAnalysis.FunctionTheory
