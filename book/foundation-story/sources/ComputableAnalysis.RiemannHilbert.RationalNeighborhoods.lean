import ComputableAnalysis.RiemannHilbert.ScalarTopology
import ComputableAnalysis.RiemannHilbert.BoxApproximation
import ComputableAnalysis.RiemannHilbert.DomainProductRule

/-! Executable rational-centered refinements of represented neighborhoods.
The search tests finite rational box widths and heights; validity proves
termination, without extracting a runtime stage by classical choice. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarTopology
open ComplexRaw FunctionTheory DomainFunctions

def narrowBox (a : Scalar) (eps : QPos) (k : Nat) : Bool :=
  decide ((a.val.compute k).width ≤ eps.val ∧ (a.val.compute k).height ≤ eps.val)

theorem eventually_narrowBox (a : Scalar) (eps : QPos) : ∃ N, ∀ k, N ≤ k → narrowBox a eps k = true := by
  obtain ⟨N,hN⟩ := a.property.2.2 eps
  refine ⟨N,fun k hk => ?_⟩
  simpa only [narrowBox,decide_eq_true_eq] using hN k hk

def approximationStage (a : Scalar) (eps : QPos) : Nat :=
  PrecisionSearch.firstFrom (narrowBox a eps) (eventually_narrowBox a eps) 0

theorem approximationStage_spec (a : Scalar) (eps : QPos) :
    (a.val.compute (approximationStage a eps)).width ≤ eps.val ∧
      (a.val.compute (approximationStage a eps)).height ≤ eps.val := by
  have h := (PrecisionSearch.firstFrom_spec (narrowBox a eps) (eventually_narrowBox a eps) 0).2
  simpa only [narrowBox,decide_eq_true_eq,approximationStage] using h

def quarterRadius (r : QPos) : QPos := divideRadius r ⟨4,by decide +kernel⟩
def rationalCenter (a : Scalar) (r : QPos) : QComplex := (a.val.compute (approximationStage a (quarterRadius r))).center
def rationalScalar (q : QComplex) : Scalar := ⟨ofQComplex q,ofQComplex_valid _⟩
def rationalBall (q : QComplex) (r : QPos) : Scalar → Prop := ball (rationalScalar q) r

theorem rationalCenter_error (a : Scalar) (r : QPos) :
    Small (sub a.val (rationalScalar (rationalCenter a r)).val) (quarterRadius r).val :=
  BoxApproximation.center_error a (approximationStage a (quarterRadius r)) (quarterRadius r).val
    (Rat.le_of_lt (quarterRadius r).property) (approximationStage_spec a (quarterRadius r)).1
    (approximationStage_spec a (quarterRadius r)).2

theorem quarterRadius_identity (r : QPos) : 4*(quarterRadius r).val=r.val :=
  divideRadius_identity r ⟨4,by decide +kernel⟩

theorem quarterRadius_lt_half (r : QPos) : (quarterRadius r).val < (halfError r).val := by
  have h1 := quarterRadius_identity r
  have h2 := halfError_identity r
  have hp := r.property
  grind only

theorem rationalRefinement_contains (a : Scalar) (r : QPos) : rationalBall (rationalCenter a r) (halfError r) a :=
  ⟨(quarterRadius r).val,Rat.le_of_lt (quarterRadius r).property,quarterRadius_lt_half r,rationalCenter_error a r⟩

theorem small_triangle (z q a : Scalar) (R S : Rat)
    (hzq : Small (sub z.val q.val) R) (hqa : Small (sub q.val a.val) S) : Small (sub z.val a.val) (R+S) := by
  have hs := LocalODE.small_add hzq hqa
  have he : (add (sub z.val q.val) (sub q.val a.val)).Equiv (sub z.val a.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid z.property q.property) (sub_valid q.property a.property))
      (hright := sub_valid z.property a.property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    let A := ComplexRawQuotient.ofRaw a.val a.property
    change (Z + -Q)+(Q + -A)=Z + -A
    grind
  exact Small.congr (add_valid (sub_valid z.property q.property) (sub_valid q.property a.property))
    (sub_valid z.property a.property) he hs

theorem rationalRefinement_bound (a : Scalar) (r : QPos) (z : Scalar)
    (hz : rationalBall (rationalCenter a r) (halfError r) z) : Small (sub z.val a.val) r.val := by
  have hza := small_triangle z (rationalScalar (rationalCenter a r)) a (halfError r).val (quarterRadius r).val
    (ball_bound _ _ _ hz)
    (RepresentedCauchySum.small_sub_symm _ _ _ (rationalCenter_error a r))
  apply hza.mono
  have h1 := quarterRadius_identity r
  have h2 := halfError_identity r
  have hp := r.property
  grind only

theorem rational_basis_neighborhood {D : Scalar → Prop} (hD : IsOpen D) (a : Scalar) (ha : D a) :
    ∃ (q : QComplex) (r : QPos), rationalBall q r a ∧ ∀ z, rationalBall q r z → D z := by
  obtain ⟨r,hr⟩ := hD.neighborhood a ha
  exact ⟨rationalCenter a r,halfError r,rationalRefinement_contains a r,
    fun z hz => hr z (rationalRefinement_bound a r z hz)⟩

def rationalNeighborhood {D : Scalar → Prop} (hD : OpenData D) (a : Scalar) (ha : D a) : QComplex × QPos :=
  (rationalCenter a (hD.radius a ha),halfError (hD.radius a ha))

theorem rationalNeighborhood_contains {D : Scalar → Prop} (hD : OpenData D) (a : Scalar) (ha : D a) :
    rationalBall (rationalNeighborhood hD a ha).1 (rationalNeighborhood hD a ha).2 a :=
  rationalRefinement_contains a (hD.radius a ha)

theorem rationalNeighborhood_inside {D : Scalar → Prop} (hD : OpenData D) (a : Scalar) (ha : D a)
    (z : Scalar) (hz : rationalBall (rationalNeighborhood hD a ha).1 (rationalNeighborhood hD a ha).2 z) : D z :=
  hD.inside a ha z (rationalRefinement_bound a (hD.radius a ha) z hz)

end ComputableAnalysis.RiemannHilbert.ScalarTopology
