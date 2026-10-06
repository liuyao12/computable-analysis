import ComputableAnalysis.RiemannHilbert.RepresentedAffineSegments
import ComputableAnalysis.RiemannHilbert.SphereSubspaceTopology

/-! Continuous sphere paths have every represented real unit parameter.
The definition permits arbitrary continuous paths. Explicit affine chart
paths, reversal, chart swapping and relative-domain continuity are proved. -/
namespace ComputableAnalysis.RiemannHilbert.SpherePaths
open SphereCoordinates ComplexRaw FunctionTheory DomainFunctions

def Continuous (f : UnitInterval.Point → Name) : Prop :=
  ∀ U, SphereTopology.IsOpen U → UnitInterval.IsOpen (fun t => U (f t))

structure Path (p q : Name) where
  eval : UnitInterval.Point → Name
  congr : ∀ s t, s ≈ t → eval s ≈ eval t
  continuous : Continuous eval
  source : eval UnitInterval.zero ≈ p
  target : eval UnitInterval.one ≈ q

def Path.Equiv {p q : Name} (a b : Path p q) : Prop := ∀ t, a.eval t ≈ b.eval t

instance {p q : Name} : Setoid (Path p q) where
  r := Path.Equiv
  iseqv := ⟨fun a t => Setoid.refl (a.eval t),fun h t => Setoid.symm (h t),
    fun h k t => Setoid.trans (h t) (k t)⟩

def constant (p : Name) : Path p p where
  eval _ := p
  congr _ _ _ := Setoid.refl p
  continuous U _ := ⟨fun _ _ _ => Iff.rfl,fun _ hp => ⟨unitError,fun _ _ => hp⟩⟩
  source := Setoid.refl p
  target := Setoid.refl p

def reverse {p q : Name} (a : Path p q) : Path q p where
  eval t := a.eval (UnitInterval.reverse t)
  congr _ _ hst := a.congr _ _ (UnitInterval.reverse_congr hst)
  continuous U hU := UnitInterval.continuous_reverse _ (a.continuous U hU)
  source := Setoid.trans (a.congr _ _ UnitInterval.reverse_zero) a.target
  target := Setoid.trans (a.congr _ _ UnitInterval.reverse_one) a.source

theorem reverse_congr {p q : Name} {a b : Path p q} (h : a ≈ b) : reverse a ≈ reverse b :=
  fun t => h (UnitInterval.reverse t)

theorem reverse_reverse {p q : Name} (a : Path p q) : reverse (reverse a) ≈ a :=
  fun t => a.congr _ _ (UnitInterval.reverse_reverse t)

def swapChart {p q : Name} (a : Path p q) : Path (swap p) (swap q) where
  eval t := swap (a.eval t)
  congr s t hst := swap_equiv (a.congr s t hst)
  continuous U hU := a.continuous (fun p => U (swap p)) (SphereTopology.isOpen_swap hU)
  source := swap_equiv a.source
  target := swap_equiv a.target

theorem swapChart_congr {p q : Name} {a b : Path p q} (h : a ≈ b) : swapChart a ≈ swapChart b :=
  fun t => swap_equiv (h t)

def finiteAffine (p q : Scalar) : Path (.finite p) (.finite q) where
  eval t := .finite (RepresentedAffineSegment.point p q t)
  congr _ _ hst := RepresentedAffineSegment.point_congr (Setoid.refl p) (Setoid.refl q) hst
  continuous U hU := RepresentedAffineSegment.continuous p q (fun z => U (.finite z)) hU.finite
  source := RepresentedAffineSegment.point_zero p q
  target := RepresentedAffineSegment.point_one p q

def ofFinite (p q : Scalar) (f : UnitInterval.Point → Scalar)
    (hf : ∀ s t, s ≈ t → f s ≈ f t) (hc : UnitInterval.ScalarContinuous f)
    (h0 : f UnitInterval.zero ≈ p) (h1 : f UnitInterval.one ≈ q) : Path (.finite p) (.finite q) where
  eval t := .finite (f t)
  congr := hf
  continuous U hU := hc (fun z => U (.finite z)) hU.finite
  source := h0
  target := h1

def infinityAffine (p q : Scalar) : Path (.infinity p) (.infinity q) := swapChart (finiteAffine p q)

theorem finiteAffine_reverse (p q : Scalar) : reverse (finiteAffine p q) ≈ finiteAffine q p :=
  fun t => RepresentedAffineSegment.reverse p q t

theorem infinityAffine_reverse (p q : Scalar) : reverse (infinityAffine p q) ≈ infinityAffine q p :=
  fun t => RepresentedAffineSegment.reverse p q t

structure InDomain (D : Name → Prop) (p q : Name) where
  path : Path p q
  inside : ∀ t, D (path.eval t)

def InDomain.reverse {D : Name → Prop} {p q : Name} (a : InDomain D p q) : InDomain D q p :=
  ⟨SpherePaths.reverse a.path,fun t => a.inside (UnitInterval.reverse t)⟩

def InDomain.constant {D : Name → Prop} (p : Name) (hp : D p) : InDomain D p p :=
  ⟨SpherePaths.constant p,fun _ => hp⟩

theorem InDomain.continuous {D : Name → Prop} {p q : Name} (a : InDomain D p q)
    (U : {p : Name // D p} → Prop) (hU : SphereTopology.IsOpenOn D U) :
    UnitInterval.IsOpen (fun t => U ⟨a.path.eval t,a.inside t⟩) := by
  obtain ⟨V,hV,hUV⟩ := hU
  exact UnitInterval.isOpen_congr (fun t => (hUV ⟨a.path.eval t,a.inside t⟩).symm)
    (a.path.continuous V hV)

theorem InDomain.endpoints {D : Name → Prop} (hD : ∀ p q, p ≈ q → (D p ↔ D q))
    {p q : Name} (a : InDomain D p q) : D p ∧ D q :=
  ⟨(hD _ _ a.path.source).1 (a.inside UnitInterval.zero),
    (hD _ _ a.path.target).1 (a.inside UnitInterval.one)⟩

end ComputableAnalysis.RiemannHilbert.SpherePaths
