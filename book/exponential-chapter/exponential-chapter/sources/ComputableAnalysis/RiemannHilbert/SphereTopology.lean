import ComputableAnalysis.RiemannHilbert.ScalarTopology
import ComputableAnalysis.RiemannHilbert.SphereChartSwap

/-! The topology glued from the two represented sphere coordinate charts.
Both chart domains are proved open. Chart lifts of arbitrary scalar open
sets are open by the actual reciprocal continuity law on the overlap. -/
namespace ComputableAnalysis.RiemannHilbert.SphereTopology
open ComplexRaw FunctionTheory SphereCoordinates

structure IsOpen (U : Name → Prop) : Prop where
  invariant : ∀ p q, p ≈ q → (U p ↔ U q)
  finite : ScalarTopology.IsOpen (fun z => U (.finite z))
  infinity : ScalarTopology.IsOpen (fun z => U (.infinity z))

theorem isOpen_univ : IsOpen (fun _ => True) :=
  ⟨fun _ _ _ => Iff.rfl, ScalarTopology.isOpen_univ, ScalarTopology.isOpen_univ⟩

theorem isOpen_empty : IsOpen (fun _ => False) :=
  ⟨fun _ _ _ => Iff.rfl, ScalarTopology.isOpen_empty, ScalarTopology.isOpen_empty⟩

theorem isOpen_inter {U V : Name → Prop} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (fun p => U p ∧ V p) where
  invariant p q hpq := ⟨fun h => ⟨(hU.invariant p q hpq).1 h.1,(hV.invariant p q hpq).1 h.2⟩,
    fun h => ⟨(hU.invariant p q hpq).2 h.1,(hV.invariant p q hpq).2 h.2⟩⟩
  finite := ScalarTopology.isOpen_inter hU.finite hV.finite
  infinity := ScalarTopology.isOpen_inter hU.infinity hV.infinity

theorem isOpen_union {I : Sort u} (U : I → Name → Prop) (hU : ∀ i, IsOpen (U i)) :
    IsOpen (fun p => ∃ i, U i p) where
  invariant p q hpq := ⟨fun ⟨i,hi⟩ => ⟨i,(hU i).invariant p q hpq |>.1 hi⟩,
    fun ⟨i,hi⟩ => ⟨i,(hU i).invariant p q hpq |>.2 hi⟩⟩
  finite := ScalarTopology.isOpen_union (fun i z => U i (.finite z)) (fun i => (hU i).finite)
  infinity := ScalarTopology.isOpen_union (fun i z => U i (.infinity z)) (fun i => (hU i).infinity)

theorem isOpen_congr {U V : Name → Prop} (hUV : ∀ p, U p ↔ V p) (hU : IsOpen U) : IsOpen V where
  invariant p q hpq := ⟨fun h => (hUV q).1 ((hU.invariant p q hpq).1 ((hUV p).2 h)),
    fun h => (hUV p).1 ((hU.invariant p q hpq).2 ((hUV q).2 h))⟩
  finite := ScalarTopology.isOpen_congr (fun z => hUV (.finite z)) hU.finite
  infinity := ScalarTopology.isOpen_congr (fun z => hUV (.infinity z)) hU.infinity

def liftFinite (D : Scalar → Prop) (p : Name) : Prop := ∃ hp : finiteDomain p, D (finiteCoordinate p hp)

def liftInfinity (D : Scalar → Prop) (p : Name) : Prop := ∃ hp : infinityDomain p, D (infinityCoordinate p hp)

theorem liftFinite_finite (D : Scalar → Prop) (z : Scalar) : liftFinite D (.finite z) ↔ D z :=
  ⟨fun ⟨_,h⟩ => h,fun h => ⟨trivial,h⟩⟩

theorem liftInfinity_infinity (D : Scalar → Prop) (z : Scalar) : liftInfinity D (.infinity z) ↔ D z :=
  ⟨fun ⟨_,h⟩ => h,fun h => ⟨trivial,h⟩⟩

theorem isOpen_liftFinite (D : Scalar → Prop) (hD : ScalarTopology.IsOpen D) : IsOpen (liftFinite D) where
  invariant p q hpq := by
    constructor
    · rintro ⟨hp,hDp⟩
      have hq := (finiteDomain_congr hpq).1 hp
      exact ⟨hq,(hD.invariant _ _ (finiteCoordinate_congr hp hq hpq)).1 hDp⟩
    · rintro ⟨hq,hDq⟩
      have hp := (finiteDomain_congr hpq).2 hq
      exact ⟨hp,(hD.invariant _ _ (finiteCoordinate_congr hp hq hpq)).2 hDq⟩
  finite := ScalarTopology.isOpen_congr (fun z => (liftFinite_finite D z).symm) hD
  infinity := ScalarTopology.isOpen_preimage ReciprocalHolomorphic.function
    ReciprocalHolomorphic.holomorphic.openDomain ReciprocalHolomorphic.holomorphic.continuous D hD

theorem isOpen_liftInfinity (D : Scalar → Prop) (hD : ScalarTopology.IsOpen D) : IsOpen (liftInfinity D) where
  invariant p q hpq := by
    constructor
    · rintro ⟨hp,hDp⟩
      have hq := (infinityDomain_congr hpq).1 hp
      exact ⟨hq,(hD.invariant _ _ (infinityCoordinate_congr hp hq hpq)).1 hDp⟩
    · rintro ⟨hq,hDq⟩
      have hp := (infinityDomain_congr hpq).2 hq
      exact ⟨hp,(hD.invariant _ _ (infinityCoordinate_congr hp hq hpq)).2 hDq⟩
  finite := ScalarTopology.isOpen_preimage ReciprocalHolomorphic.function
    ReciprocalHolomorphic.holomorphic.openDomain ReciprocalHolomorphic.holomorphic.continuous D hD
  infinity := ScalarTopology.isOpen_congr (fun z => (liftInfinity_infinity D z).symm) hD

theorem isOpen_finiteDomain : IsOpen finiteDomain :=
  ⟨fun _ _ h => finiteDomain_congr h, ScalarTopology.isOpen_univ, ScalarTopology.isOpen_nonzero⟩

theorem isOpen_infinityDomain : IsOpen infinityDomain :=
  ⟨fun _ _ h => infinityDomain_congr h, ScalarTopology.isOpen_nonzero, ScalarTopology.isOpen_univ⟩

theorem isOpen_overlap : IsOpen (fun p => finiteDomain p ∧ infinityDomain p) :=
  isOpen_inter isOpen_finiteDomain isOpen_infinityDomain

theorem isOpen_swap {U : Name → Prop} (hU : IsOpen U) : IsOpen (fun p => U (swap p)) :=
  ⟨fun _ _ hpq => hU.invariant _ _ (swap_equiv hpq),hU.infinity,hU.finite⟩

def finiteBall (a : Scalar) (r : QPos) : Name → Prop := liftFinite (ScalarTopology.ball a r)

def infinityBall (a : Scalar) (r : QPos) : Name → Prop := liftInfinity (ScalarTopology.ball a r)

theorem isOpen_finiteBall (a : Scalar) (r : QPos) : IsOpen (finiteBall a r) :=
  isOpen_liftFinite _ (ScalarTopology.isOpen_ball a r)

theorem isOpen_infinityBall (a : Scalar) (r : QPos) : IsOpen (infinityBall a r) :=
  isOpen_liftInfinity _ (ScalarTopology.isOpen_ball a r)

theorem finiteBall_center (a : Scalar) (r : QPos) : finiteBall a r (.finite a) :=
  ⟨trivial,ScalarTopology.ball_center a r⟩

theorem infinityBall_center (a : Scalar) (r : QPos) : infinityBall a r (.infinity a) :=
  ⟨trivial,ScalarTopology.ball_center a r⟩

theorem finite_neighborhood {U : Name → Prop} (hU : IsOpen U) (p : Name)
    (hp : finiteDomain p) (hUp : U p) :
    ∃ r : QPos, finiteBall (finiteCoordinate p hp) r p ∧ ∀ q, finiteBall (finiteCoordinate p hp) r q → U q := by
  have hcenter : U (.finite (finiteCoordinate p hp)) :=
    (hU.invariant _ _ (finiteCoordinate_name p hp)).2 hUp
  obtain ⟨r,hr⟩ := hU.finite.neighborhood _ hcenter
  refine ⟨r,⟨hp,ScalarTopology.ball_center _ r⟩,?_⟩
  rintro q ⟨hq,hqball⟩
  exact (hU.invariant _ _ (finiteCoordinate_name q hq)).1 (hr _ (ScalarTopology.ball_bound _ _ _ hqball))

theorem infinity_neighborhood {U : Name → Prop} (hU : IsOpen U) (p : Name)
    (hp : infinityDomain p) (hUp : U p) :
    ∃ r : QPos, infinityBall (infinityCoordinate p hp) r p ∧ ∀ q, infinityBall (infinityCoordinate p hp) r q → U q := by
  have hcenter : U (.infinity (infinityCoordinate p hp)) :=
    (hU.invariant _ _ (infinityCoordinate_name p hp)).2 hUp
  obtain ⟨r,hr⟩ := hU.infinity.neighborhood _ hcenter
  refine ⟨r,⟨hp,ScalarTopology.ball_center _ r⟩,?_⟩
  rintro q ⟨hq,hqball⟩
  exact (hU.invariant _ _ (infinityCoordinate_name q hq)).1 (hr _ (ScalarTopology.ball_bound _ _ _ hqball))

end ComputableAnalysis.RiemannHilbert.SphereTopology
