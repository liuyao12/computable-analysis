import ComputableAnalysis.RiemannHilbert.ScalarPathConcatenation
import ComputableAnalysis.RiemannHilbert.SpherePaths
import ComputableAnalysis.RiemannHilbert.UnitIntervalSegmentOrder

/-! Continuous paths in represented complex coordinates. Every parameter is
a valid represented real in the unit interval; endpoints and path comparisons
use equality of values. These paths embed in the finite sphere chart. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarPaths
open ComplexRaw FunctionTheory DomainFunctions UnitInterval

structure Path (p q : Scalar) where
  eval : Point → Scalar
  congr : ∀ s t, s ≈ t → eval s ≈ eval t
  continuous : ScalarContinuous eval
  source : eval UnitInterval.zero ≈ p
  target : eval UnitInterval.one ≈ q

def Path.Equiv {p q : Scalar} (a b : Path p q) : Prop := ∀ t, a.eval t ≈ b.eval t

instance {p q : Scalar} : Setoid (Path p q) where
  r := Path.Equiv
  iseqv := ⟨fun a t => Setoid.refl (a.eval t), fun h t => Setoid.symm (h t),
    fun h k t => Setoid.trans (h t) (k t)⟩

def toSphere {p q : Scalar} (a : Path p q) : SpherePaths.Path (.finite p) (.finite q) :=
  SpherePaths.ofFinite p q a.eval a.congr a.continuous a.source a.target

def constant (p : Scalar) : Path p p where
  eval _ := p
  congr _ _ _ := Setoid.refl p
  continuous := (constantContinuousData p).continuous
  source := Setoid.refl p
  target := Setoid.refl p

def affine (p q : Scalar) : Path p q where
  eval := RepresentedAffineSegment.point p q
  congr _ _ h := RepresentedAffineSegment.point_congr (Setoid.refl p) (Setoid.refl q) h
  continuous := RepresentedAffineSegment.continuous p q
  source := RepresentedAffineSegment.point_zero p q
  target := RepresentedAffineSegment.point_one p q

def reverse {p q : Scalar} (a : Path p q) : Path q p where
  eval t := a.eval (UnitInterval.reverse t)
  congr _ _ h := a.congr _ _ (UnitInterval.reverse_congr h)
  continuous U hU := UnitInterval.continuous_reverse (fun t => U (a.eval t)) (a.continuous U hU)
  source := Setoid.trans (a.congr _ _ UnitInterval.reverse_zero) a.target
  target := Setoid.trans (a.congr _ _ UnitInterval.reverse_one) a.source

theorem reverse_reverse {p q : Scalar} (a : Path p q) : reverse (reverse a) ≈ a :=
  fun t => a.congr _ _ (UnitInterval.reverse_reverse t)

def concatenate {p q r : Scalar} (a : Path p q) (b : Path q r) : Path p r where
  eval := ScalarPathConcatenation.value a.eval b.eval q
  congr := ScalarPathConcatenation.point_congr a.eval b.eval q a.congr b.congr
  continuous := ScalarPathConcatenation.continuous a.eval b.eval q a.congr b.congr a.continuous b.continuous
  source := ScalarPathConcatenation.source a.eval b.eval p q a.congr b.congr a.source b.source
  target := ScalarPathConcatenation.target a.eval b.eval q r a.congr b.congr a.target b.target

def subpath {p q : Scalar} (a : Path p q) (s t : Point) : Path (a.eval s) (a.eval t) where
  eval u := a.eval (segment s t u)
  congr _ _ h := a.congr _ _ (segment_congr (Setoid.refl s) (Setoid.refl t) h)
  continuous U hU := (segmentContinuousData s t).continuous _ (a.continuous U hU)
  source := a.congr _ _ (segment_zero s t)
  target := a.congr _ _ (segment_one s t)

theorem subpath_whole {p q : Scalar} (a : Path p q) (u : Point) :
    (subpath a UnitInterval.zero UnitInterval.one).eval u ≈ a.eval u :=
  a.congr _ _ (segment_identity u)

theorem subpath_nested {p q : Scalar} (a : Path p q) (s t u v w : Point) :
    (subpath (subpath a s t) u v).eval w ≈
      (subpath a (segment s t u) (segment s t v)).eval w :=
  a.congr _ _ (Setoid.symm (segment_compose s t u v w))

theorem first_restriction {p q : Scalar} (a : Path p q) (s t u v : Point) :
    (subpath a s (segment s t u)).eval v ≈ (subpath a s t).eval (segment UnitInterval.zero u v) :=
  a.congr _ _ (segment_first_restriction s t u v)

theorem second_restriction {p q : Scalar} (a : Path p q) (s t u v : Point) :
    (subpath a (segment s t u) t).eval v ≈ (subpath a s t).eval (segment u UnitInterval.one v) :=
  a.congr _ _ (segment_second_restriction s t u v)

end ComputableAnalysis.RiemannHilbert.ScalarPaths
