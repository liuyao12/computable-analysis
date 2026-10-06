import ComputableAnalysis.RiemannHilbert.RepresentedFiber

/-!
# The conditional horizontal-morphism descent law

For supplied justified transport maps, a based-loop intertwiner determines
fiber maps everywhere, independently of the chosen route frames. The law
is purely algebraic: it does not assert analytic continuation exists or that
the resulting fiberwise maps are holomorphic. Those remain separate bridges.
-/
namespace ComputableAnalysis.RiemannHilbert.HorizontalDescent

variable {X E : Type} {n m : Nat}

/-- Frame `a` transports from the base fiber to the fiber at a point. -/
def extend (a : LinearIso n n) (b : LinearIso m m)
    (f : ValueMap (Fiber n) (Fiber m)) : ValueMap (Fiber n) (Fiber m) :=
  (a.toValueIso.backward.followedBy f).followedBy b.toValueIso.forward

theorem extend_linear (a : LinearIso n n) (b : LinearIso m m)
    (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f) :
    IsLinear (extend a b f) :=
  IsLinear.followedBy (IsLinear.followedBy (IsLinear.inverse a.toValueIso a.linear) hf)
    b.linear

/-- Frame-normalized loop associated to an edge from source to target. -/
def basedLoop (source edge target : LinearIso n n) : LinearIso n n :=
  (source.followedBy edge).followedBy target.inverse

/-- Intertwining the based loop gives naturality on the original edge. -/
theorem extend_natural (aₛ aₜ A : LinearIso n n) (bₛ bₜ B : LinearIso m m)
    (f : ValueMap (Fiber n) (Fiber m))
    (h : ∀ x, f.eval ((basedLoop aₛ A aₜ).toValueIso.forward.eval x) ≈
      (basedLoop bₛ B bₜ).toValueIso.forward.eval (f.eval x)) (x : Fiber n) :
    (extend aₜ bₜ f).eval (A.toValueIso.forward.eval x) ≈
      B.toValueIso.forward.eval ((extend aₛ bₛ f).eval x) := by
  let v := aₛ.toValueIso.backward.eval x
  have h1 := aₛ.toValueIso.forward_backward x
  have h2 := bₜ.toValueIso.forward.congr (h v)
  have h3 := bₜ.toValueIso.forward_backward
    (B.toValueIso.forward.eval (bₛ.toValueIso.forward.eval (f.eval v)))
  exact Setoid.trans
    (bₜ.toValueIso.forward.congr (f.congr (aₜ.toValueIso.backward.congr
      (A.toValueIso.forward.congr (Setoid.symm h1)))))
    (Setoid.trans h2 h3)

/-- A connected supplied family of route frames determines all fiber maps
from the base map. The conclusion follows from naturality on those frames. -/
theorem extend_unique (a : X → LinearIso n n) (b : X → LinearIso m m)
    (f : ValueMap (Fiber n) (Fiber m))
    (g : X → ValueMap (Fiber n) (Fiber m))
    (h : ∀ p x, (g p).eval ((a p).toValueIso.forward.eval x) ≈
      (b p).toValueIso.forward.eval (f.eval x)) (p : X) :
    (g p).Equiv (extend (a p) (b p) f) := by
  intro x
  exact Setoid.trans ((g p).congr
    (Setoid.symm ((a p).toValueIso.forward_backward x)))
    (h p ((a p).toValueIso.backward.eval x))

/-- Comparing two choices of base-to-point routes yields a based loop.
Its equivariance proves frame independence instead of assuming it. -/
theorem extend_independent (a a' : LinearIso n n) (b b' : LinearIso m m)
    (f : ValueMap (Fiber n) (Fiber m))
    (h : ∀ x, f.eval ((a.followedBy a'.inverse).toValueIso.forward.eval x) ≈
      (b.followedBy b'.inverse).toValueIso.forward.eval (f.eval x)) :
    (extend a b f).Equiv (extend a' b' f) := by
  intro x
  let v := a.toValueIso.backward.eval x
  have h1 := b'.toValueIso.forward.congr (h v)
  have h2 := b'.toValueIso.forward_backward
    (b.toValueIso.forward.eval (f.eval v))
  have h3 := b'.toValueIso.forward.congr (f.congr (a'.toValueIso.backward.congr
    (a.toValueIso.forward_backward x)))
  exact Setoid.trans (Setoid.symm (Setoid.trans h1 h2)) h3

/-- Generator intertwiners suffice for descent along any word-normalized edge. -/
theorem extend_natural_of_word {I : Type}
    (u : I → LinearIso n n) (v : I → LinearIso m m)
    (f : ValueMap (Fiber n) (Fiber m))
    (h : ∀ i x, f.eval ((u i).toValueIso.forward.eval x) ≈
      (v i).toValueIso.forward.eval (f.eval x))
    (aₛ aₜ A : LinearIso n n) (bₛ bₜ B : LinearIso m m)
    (w : List (Letter I))
    (hu : (basedLoop aₛ A aₜ).toValueIso.forward.Equiv
      (ValueTransport.wordMap (fun i => (u i).toValueIso) w).forward)
    (hv : (basedLoop bₛ B bₜ).toValueIso.forward.Equiv
      (ValueTransport.wordMap (fun i => (v i).toValueIso) w).forward)
    (x : Fiber n) :
    (extend aₜ bₜ f).eval (A.toValueIso.forward.eval x) ≈
      B.toValueIso.forward.eval ((extend aₛ bₛ f).eval x) := by
  apply extend_natural aₛ aₜ A bₛ bₜ B f
  intro y
  exact Setoid.trans (f.congr (hu y))
    (Setoid.trans (ValueTransport.intertwine_run
      (fun i => (u i).toValueIso) (fun i => (v i).toValueIso) f h w y)
      (Setoid.symm (hv (f.eval y))))

end ComputableAnalysis.RiemannHilbert.HorizontalDescent
