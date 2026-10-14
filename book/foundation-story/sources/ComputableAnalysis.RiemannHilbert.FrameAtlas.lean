import ComputableAnalysis.RiemannHilbert.TransitionAtlas

/-! A family of varying frames constructs a transition atlas. Its cocycle
is proved by cancellation of the middle frame; the constructor is useful for
concrete clients, while general atlases need not have a global frame. -/
namespace ComputableAnalysis.RiemannHilbert.TransitionAtlas
universe u v
variable {X : Type u} {I : Type v} {n : Nat}

def ofFrames (D : I → X → Prop)
    (F : (i : I) → (p : X) → D i p → LinearIso n n) : TransitionAtlas X I n where
  domain := D
  transition p i j hi hj := (F i p hi).inverse.followedBy (F j p hj)
  cocycle p i j k hi hj hk x :=
    (F k p hk).toValueIso.forward.congr
      ((F j p hj).toValueIso.backward_forward ((F i p hi).toValueIso.backward.eval x))

theorem ofFrames_transition (D : I → X → Prop)
    (F : (i : I) → (p : X) → D i p → LinearIso n n) (p : X) (i j : I)
    (hi : D i p) (hj : D j p) (x : Fiber n) :
    ((ofFrames D F).transition p i j hi hj).toValueIso.forward.eval x =
      (F j p hj).toValueIso.forward.eval ((F i p hi).toValueIso.backward.eval x) := rfl

end ComputableAnalysis.RiemannHilbert.TransitionAtlas
