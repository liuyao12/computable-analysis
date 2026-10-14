import ComputableAnalysis.RiemannHilbert.RepresentedFiber

/-! Gluing represented finite fibers from supplied transition cocycles.
Local names retain their chart and executable coordinates. Their value
equality is constructed from transition maps. Reflexivity, symmetry, local
trivializations and inverse-transition agreement are consequences of the
cocycle and the already justified linear isomorphisms. This module makes
no topological or holomorphic bundle assertion. -/
namespace ComputableAnalysis.RiemannHilbert
universe u v

structure TransitionAtlas (X : Type u) (I : Type v) (n : Nat) where
  domain : I → X → Prop
  transition : (p : X) → (i j : I) → domain i p → domain j p → LinearIso n n
  cocycle : ∀ p i j k hi hj hk,
    ((transition p i j hi hj).toValueIso.forward.followedBy
      (transition p j k hj hk).toValueIso.forward).Equiv
      (transition p i k hi hk).toValueIso.forward

namespace TransitionAtlas
variable {X : Type u} {I : Type v} {n : Nat}

theorem transition_self (a : TransitionAtlas X I n) (p : X) (i : I) (hi : a.domain i p) :
    (a.transition p i i hi hi).toValueIso.forward.Equiv ValueMap.identity := by
  intro x
  exact (a.transition p i i hi hi).toValueIso.forward_reflects (a.cocycle p i i i hi hi hi x)

theorem transition_return (a : TransitionAtlas X I n) (p : X) (i j : I)
    (hi : a.domain i p) (hj : a.domain j p) (x : Fiber n) :
    (a.transition p j i hj hi).toValueIso.forward.eval
      ((a.transition p i j hi hj).toValueIso.forward.eval x) ≈ x :=
  Setoid.trans (a.cocycle p i j i hi hj hi x) (a.transition_self p i hi x)

theorem transition_reverse_inverse (a : TransitionAtlas X I n) (p : X) (i j : I)
    (hi : a.domain i p) (hj : a.domain j p) :
    (a.transition p j i hj hi).toValueIso.forward.Equiv
      (a.transition p i j hi hj).toValueIso.backward := by
  intro x
  apply (a.transition p i j hi hj).toValueIso.forward_reflects
  exact Setoid.trans (a.transition_return p j i hj hi x)
    (Setoid.symm ((a.transition p i j hi hj).toValueIso.forward_backward x))

end TransitionAtlas

structure AtlasFiber {X : Type u} {I : Type v} {n : Nat}
    (a : TransitionAtlas X I n) (p : X) where
  chart : I
  mem : a.domain chart p
  coordinates : Fiber n

namespace AtlasFiber
variable {X : Type u} {I : Type v} {n : Nat} {a : TransitionAtlas X I n} {p : X}

def Rel (x y : AtlasFiber a p) : Prop :=
  (a.transition p x.chart y.chart x.mem y.mem).toValueIso.forward.eval x.coordinates ≈ y.coordinates

instance : Setoid (AtlasFiber a p) where
  r := Rel
  iseqv := {
    refl := fun x => a.transition_self p x.chart x.mem x.coordinates
    symm := fun {x y} h => Setoid.trans
      ((a.transition p y.chart x.chart y.mem x.mem).toValueIso.forward.congr (Setoid.symm h))
      (a.transition_return p x.chart y.chart x.mem y.mem x.coordinates)
    trans := fun {x y z} hxy hyz => Setoid.trans
      (Setoid.symm (a.cocycle p x.chart y.chart z.chart x.mem y.mem z.mem x.coordinates))
      (Setoid.trans ((a.transition p y.chart z.chart y.mem z.mem).toValueIso.forward.congr hxy) hyz) }

def inChart (i : I) (hi : a.domain i p) (x : Fiber n) : AtlasFiber a p := ⟨i,hi,x⟩

def coordinatesIn (i : I) (hi : a.domain i p) (x : AtlasFiber a p) : Fiber n :=
  (a.transition p x.chart i x.mem hi).toValueIso.forward.eval x.coordinates

theorem coordinatesIn_congr (i : I) (hi : a.domain i p) {x y : AtlasFiber a p} (hxy : x ≈ y) :
    coordinatesIn i hi x ≈ coordinatesIn i hi y :=
  Setoid.trans (Setoid.symm (a.cocycle p x.chart y.chart i x.mem y.mem hi x.coordinates))
    ((a.transition p y.chart i y.mem hi).toValueIso.forward.congr hxy)

theorem inChart_congr (i : I) (hi : a.domain i p) {x y : Fiber n} (hxy : x ≈ y) :
    inChart i hi x ≈ inChart i hi y := by
  change (a.transition p i i hi hi).toValueIso.forward.eval x ≈ y
  exact Setoid.trans (a.transition_self p i hi x) hxy

theorem coordinatesIn_inChart (i : I) (hi : a.domain i p) (x : Fiber n) :
    coordinatesIn i hi (inChart i hi x) ≈ x :=
  a.transition_self p i hi x

theorem inChart_coordinatesIn (i : I) (hi : a.domain i p) (x : AtlasFiber a p) :
    inChart i hi (coordinatesIn i hi x) ≈ x :=
  a.transition_return p x.chart i x.mem hi x.coordinates

def chartIso (i : I) (hi : a.domain i p) : ValueIso (AtlasFiber a p) (Fiber n) where
  forward := ⟨coordinatesIn i hi, coordinatesIn_congr i hi⟩
  backward := ⟨inChart i hi, inChart_congr i hi⟩
  forward_backward := coordinatesIn_inChart i hi
  backward_forward := inChart_coordinatesIn i hi

theorem change_coordinates (i j : I) (hi : a.domain i p) (hj : a.domain j p) (x : AtlasFiber a p) :
    (a.transition p i j hi hj).toValueIso.forward.eval (coordinatesIn i hi x) ≈
      coordinatesIn j hj x :=
  a.cocycle p x.chart i j x.mem hi hj x.coordinates

theorem coordinatesIn_reflects (i : I) (hi : a.domain i p) {x y : AtlasFiber a p}
    (h : coordinatesIn i hi x ≈ coordinatesIn i hi y) : x ≈ y :=
  (chartIso i hi).forward_reflects h

end AtlasFiber
end ComputableAnalysis.RiemannHilbert
