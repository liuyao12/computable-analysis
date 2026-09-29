import ComputableAnalysis.Continuation.Germ
import ComputableAnalysis.Continuation.FinitePath

/-! Polygonal-domain geometry with arbitrary represented vertices and real
parameters. Filled triangles are domain-containment facts, independent of
functions, germs, or transport. -/
namespace ComputableAnalysis.Continuation
open ComplexRaw FunctionTheory

structure UnitParameter where
  raw : RealRaw
  valid : raw.Valid
  nonneg : (RealRaw.ofRat 0).Le raw
  le_one : raw.Le (RealRaw.ofRat 1)

def segmentPoint (a b : Point) (t : UnitParameter) : Point :=
  ⟨add a.val (mul (ofRealRaw t.raw) (sub b.val a.val)),
    add_valid a.property (mul_valid (ofRealRaw_valid t.raw t.valid)
      (sub_valid b.property a.property))⟩

structure Region where
  mem : Point → Prop
  congr : ∀ {a b}, a.val.Equiv b.val → (mem a ↔ mem b)

namespace Region
abbrev Vertex (D : Region) := {a : Point // D.mem a}

def Edge (D : Region) (a b : D.Vertex) : Prop :=
  ∀ t : UnitParameter, D.mem (segmentPoint a.val b.val t)

/-- Every point of the filled triangle lies in the domain, using a nested
barycentric parameterization. Both parameters may be irrational. -/
def Face (D : Region) (a b c : D.Vertex) : Prop :=
  ∀ t u : UnitParameter, D.mem (segmentPoint a.val (segmentPoint b.val c.val u) t)

def Convex (D : Region) : Prop :=
  ∀ a b, D.mem a → D.mem b → ∀ t : UnitParameter, D.mem (segmentPoint a b t)

theorem convex_edge (D : Region) (h : D.Convex) (a b : D.Vertex) : D.Edge a b :=
  h a.val b.val a.property b.property

theorem convex_face (D : Region) (h : D.Convex) (a b c : D.Vertex) : D.Face a b c :=
  fun t u => h a.val (segmentPoint b.val c.val u) a.property
    (h b.val c.val b.property c.property u) t

/-- Convexity supplies an explicit route and finite contractions. No compact
cover is selected and no topological theorem about Mathlib reals is used. -/
def simplyConnectedOfConvex (D : Region) (h : D.Convex) : FiniteSimplyConnected D.Edge D.Face :=
  convexFiniteSimplyConnected (D.convex_edge h) (D.convex_face h)

end Region

def wholePlane : Region where
  mem := fun _ => True
  congr := fun _ => Iff.rfl

theorem wholePlane_convex : wholePlane.Convex := fun _ _ _ _ _ => True.intro

end ComputableAnalysis.Continuation
