import ComputableAnalysis.RiemannHilbert.ContourBisection
import ComputableAnalysis.RiemannHilbert.UnitIntervalTopology

/-! Pointwise relative-open coverage yields a finite rational bisection
cover of every represented unit parameter. The proof uses valid nested
rational interval names and their proved neighborhood convergence. It is an
existence theorem, not a noncomputable chart selector or an executable
extraction of a witness from arbitrary propositional continuity evidence. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
universe u
open ComplexRaw FunctionTheory DomainFunctions RectangularContour
set_option autoImplicit false
variable {I : Type u}

def intervalContains (J : QInterval) (t : Point) : Prop :=
  (RealRaw.ofRat J.lo).Le t.value ∧ t.value.Le (RealRaw.ofRat J.hi)

/-- Endpoint comparisons control every represented point in the interval,
including names whose early boxes extend beyond its rational endpoints. -/
theorem intervalNear_small (J : QInterval) (s t : Point) (eps : QPos)
    (hne : intervalNear J s.value eps) (ht : intervalContains J t) :
    Small (sub (scalar t).val (scalar s).val) eps.val := by
  have hJ : J.lo≤J.hi := (RealRaw.le_trans t.valid ht.1 ht.2) 0 0
  have hl := hne J.lo Rat.le_refl hJ
  have hu := hne J.hi hJ Rat.le_refl
  refine ⟨?_,?_,?_,?_⟩
  · intro k l
    have htl := ht.1 0 l
    have hsu := hl.2 l 0
    change J.lo≤(t.value.compute l).hi at htl
    change (s.value.compute l).lo≤J.lo+eps.val at hsu
    change -eps.val≤(t.value.compute l).hi + -(s.value.compute l).lo
    grind only
  · intro k l
    have htu := ht.2 k 0
    have hsl := hu.1 0 k
    change (t.value.compute k).lo≤J.hi at htu
    change J.hi-eps.val≤(s.value.compute k).hi at hsl
    change (t.value.compute k).lo + -(s.value.compute k).hi≤eps.val
    grind only
  · intro k l
    change -eps.val≤(0 : Rat)+ -0
    have hp := eps.property
    grind only
  · intro k l
    change (0 : Rat)+ -0≤eps.val
    have hp := eps.property
    grind only

inductive RationalOpenCover (U : I → Point → Prop) : QInterval → Prop where
  | cell (J : QInterval) (i : I) (inside : ∀ t, intervalContains J t → U i t) : RationalOpenCover U J
  | split (J : QInterval) (left : RationalOpenCover U (bisectInterval J false))
      (right : RationalOpenCover U (bisectInterval J true)) : RationalOpenCover U J

/-- Pointwise open coverage, without a supplied finite cover or uniform
parameter radius, supplies a finite whole-interval bisection cover. -/
theorem rational_open_cover (U : I → Point → Prop) (hU : ∀ i, IsOpen (U i))
    (cover : ∀ t, ∃ i, U i t) : RationalOpenCover U ⟨0,1⟩ := by
  apply represented_interval_cover (RationalOpenCover U) ⟨0,1⟩ (by decide +kernel)
    (fun J hl hr => RationalOpenCover.split J hl hr)
  intro x hx h0 h1
  let s : Point := ⟨x,hx,h0,h1⟩
  obtain ⟨i,hi⟩ := cover s
  obtain ⟨r,hr⟩ := (hU i).neighborhood s hi
  refine ⟨r,?_⟩
  intro J hnear
  exact RationalOpenCover.cell J i (fun t ht => hr t (intervalNear_small J s t r hnear ht))

def singleCell (U : I → Point → Prop) (J : QInterval) : Prop :=
  ∃ i, ∀ t, intervalContains J t → U i t

/-- A finite bisection proof also supplies a common depth after which every
subinterval lies wholly in one member. The depth remains a proved
existential; no representative or numerical schedule is silently selected. -/
theorem RationalOpenCover.uniform_depth (U : I → Point → Prop) (J : QInterval) (hJ : J.lo≤J.hi)
    (hc : RationalOpenCover U J) :
    ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n → singleCell U (bisectionInterval J choice n) := by
  induction hc with
  | cell J i inside =>
    refine ⟨0,?_⟩
    intro choice n _
    have hsub := bisectionInterval_nested J hJ choice 0 n (Nat.zero_le n)
    change J.lo≤(bisectionInterval J choice n).lo ∧
      (bisectionInterval J choice n).lo≤(bisectionInterval J choice n).hi ∧
      (bisectionInterval J choice n).hi≤J.hi at hsub
    refine ⟨i,fun t ht => inside t ⟨?_,?_⟩⟩
    · intro k l
      exact Rat.le_trans hsub.1 (ht.1 0 l)
    · intro k l
      exact Rat.le_trans (ht.2 k 0) hsub.2.2
  | split J hl hr il ir =>
    obtain ⟨L,hL⟩ := il (bisectInterval_bounds J hJ false).2.1
    obtain ⟨R,hR⟩ := ir (bisectInterval_bounds J hJ true).2.1
    refine ⟨max L R+1,?_⟩
    intro choice n hn
    have hnpos : 0<n := by omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    subst n
    rw [bisectionInterval_shift]
    cases h : choice 0
    · exact hL (fun j => choice (j+1)) k (by omega)
    · exact hR (fun j => choice (j+1)) k (by omega)

end ComputableAnalysis.RiemannHilbert.UnitInterval
