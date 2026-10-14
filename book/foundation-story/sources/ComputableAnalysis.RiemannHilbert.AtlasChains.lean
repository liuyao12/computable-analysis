import ComputableAnalysis.RiemannHilbert.AtlasChartComparison

/-! Finite continuation chains in represented atlas fibers. Each edge uses
an actual coefficient chart; crossing to the next frame is already handled
by the constructed fiber trivializations. All inverse, concatenation and
within-chart refinement laws follow from the actual local transports. -/
namespace ComputableAnalysis.RiemannHilbert
universe u

inductive AtlasChain {I : Type u} {n : Nat} (a : CoefficientAtlas I n) : Scalar → Scalar → Type u where
  | nil (p : Scalar) : AtlasChain a p p
  | step {p q r : Scalar} (chart : I) (start_mem : (a.chart chart).domain p)
      (end_mem : (a.chart chart).domain q) (tail : AtlasChain a q r) : AtlasChain a p r

namespace AtlasChain
variable {I : Type u} {n : Nat} {a : CoefficientAtlas I n} {p q r : Scalar}

def append : {p q r : Scalar} → AtlasChain a p q → AtlasChain a q r → AtlasChain a p r
  | _, _, _, .nil _, b => b
  | _, _, _, .step i hp hq tail, b => .step i hp hq (append tail b)

def transport : {p q : Scalar} → AtlasChain a p q → ValueIso (a.PointFiber p) (a.PointFiber q)
  | _, _, .nil _ => ValueIso.identity
  | p, q, .step (q := s) i hp hs tail => (a.localTransport i p s hp hs).followedBy (transport tail)

def edge (i : I) (p q : Scalar) (hp : (a.chart i).domain p) (hq : (a.chart i).domain q) : AtlasChain a p q :=
  .step i hp hq (.nil q)

def reverse : {p q : Scalar} → AtlasChain a p q → AtlasChain a q p
  | _, _, .nil p => .nil p
  | p, _, .step (q := q) i hp hq tail => append (reverse tail) (edge i q p hq hp)

theorem transport_append (c : AtlasChain a p q) (d : AtlasChain a q r) :
    (transport (append c d)).forward.Equiv ((transport c).forward.followedBy (transport d).forward) := by
  induction c with
  | nil => exact fun _ => Setoid.refl _
  | step i hp hq tail ih => exact fun x => ih d ((a.localTransport i _ _ hp hq).forward.eval x)

theorem transport_reverse (c : AtlasChain a p q) :
    (transport (reverse c)).forward.Equiv (transport c).backward := by
  induction c with
  | nil => exact fun _ => Setoid.refl _
  | @step p q r i hp hq tail ih =>
    intro x
    exact Setoid.trans (transport_append (reverse tail) (edge i q p hq hp) x)
      (Setoid.trans ((a.localTransport i q p hq hp).forward.congr (ih x))
        (a.localTransport_reverse i p q hp hq ((transport tail).backward.eval x)))

theorem reverse_forward (c : AtlasChain a p q) (x : a.PointFiber p) :
    (transport (reverse c)).forward.eval ((transport c).forward.eval x) ≈ x :=
  Setoid.trans (transport_reverse c _) ((transport c).backward_forward x)

theorem forward_reverse (c : AtlasChain a p q) (x : a.PointFiber q) :
    (transport c).forward.eval ((transport (reverse c)).forward.eval x) ≈ x :=
  Setoid.trans ((transport c).forward.congr (transport_reverse c x)) ((transport c).forward_backward x)

theorem edge_transport (i : I) (p q : Scalar) (hp : (a.chart i).domain p) (hq : (a.chart i).domain q) :
    (transport (edge i p q hp hq)).forward.Equiv (a.localTransport i p q hp hq).forward :=
  fun _ => Setoid.refl _

theorem edge_split (i : I) (p q r : Scalar) (hp : (a.chart i).domain p)
    (hq : (a.chart i).domain q) (hr : (a.chart i).domain r) :
    (transport (append (edge i p q hp hq) (edge i q r hq hr))).forward.Equiv
      (transport (edge i p r hp hr)).forward :=
  fun x => Setoid.trans (transport_append (edge i p q hp hq) (edge i q r hq hr) x)
    (a.localTransport_compose i p q r hp hq hr x)

theorem transport_add (c : AtlasChain a p q) (x y : a.PointFiber p) :
    (transport c).forward.eval (AtlasFiber.add x y) ≈
      AtlasFiber.add ((transport c).forward.eval x) ((transport c).forward.eval y) := by
  induction c with
  | nil => exact Setoid.refl _
  | step i hp hq tail ih =>
    exact Setoid.trans ((transport tail).forward.congr (a.localTransport_add i _ _ hp hq x y))
      (ih _ _)

theorem transport_scale (c : AtlasChain a p q) (s : Scalar) (x : a.PointFiber p) :
    (transport c).forward.eval (AtlasFiber.scale s x) ≈
      AtlasFiber.scale s ((transport c).forward.eval x) := by
  induction c with
  | nil => exact Setoid.refl _
  | step i hp hq tail ih =>
    exact Setoid.trans ((transport tail).forward.congr (a.localTransport_scale i _ _ hp hq s x)) (ih _)

end AtlasChain
end ComputableAnalysis.RiemannHilbert
