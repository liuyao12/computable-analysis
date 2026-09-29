import ComputableAnalysis.Continuation.Domain
import ComputableAnalysis.Continuation.Gluing

/-!
# Actual chains of local holomorphic functions along polygonal paths

These witnesses contain charts, whole-segment domain coverage, and equality
on open transition neighborhoods. They do not assume uniqueness or homotopy
invariance. In particular, the abstract transport theorem alone does not
manufacture these witnesses.
-/
namespace ComputableAnalysis.Continuation
open ComplexRaw FunctionTheory

def Chart.at (c : Chart) (a : Point) (ha : c.map.domain a.val) : LocalFunction a :=
  ⟨c.map,c.holomorphic,ha⟩

def Chart.Covers (c : Chart) (a b : Point) : Prop :=
  ∀ t : UnitParameter, c.map.domain (segmentPoint a b t).val

inductive Along {D : Region} : {a b : D.Vertex} → Path D.Edge a b →
    LocalFunction a.val → LocalFunction b.val → Type
  | nil {a : D.Vertex} {f g : LocalFunction a.val} (agree : f ≈ g) :
      Along (.nil a) f g
  | cons {a b c : D.Vertex} {p : Path D.Edge b c}
      {f : LocalFunction a.val} {g : LocalFunction c.val}
      (edge : D.Edge a b) (chart : Chart)
      (ha : chart.map.domain a.val.val) (hb : chart.map.domain b.val.val)
      (covers : chart.Covers a.val b.val)
      (agree : f ≈ chart.at a.val ha)
      (rest : Along p (chart.at b.val hb) g) : Along (.cons edge p) f g

namespace Along
variable {D : Region}

def changeStart {a b : D.Vertex} {p : Path D.Edge a b}
    {f f' : LocalFunction a.val} {g : LocalFunction b.val}
    (h : f' ≈ f) (c : Along p f g) : Along p f' g :=
  match c with
  | .nil k => .nil (Setoid.trans h k)
  | .cons e chart ha hb covered k rest =>
      .cons e chart ha hb covered (Setoid.trans h k) rest

/-- Concatenation preserves the semantic chain property. This is an existence
statement; `singleChart` below is a directly executable chain constructor. -/
theorem append_exists {a b c : D.Vertex} {p : Path D.Edge a b} {q : Path D.Edge b c}
    {f : LocalFunction a.val} {g : LocalFunction b.val} {h : LocalFunction c.val}
    (first : Along p f g) (second : Along q g h) : Nonempty (Along (p.append q) f h) := by
  induction first with
  | nil k => exact ⟨second.changeStart k⟩
  | cons e chart ha hb covered k rest ih =>
      obtain ⟨tail⟩ := ih second
      exact ⟨.cons e chart ha hb covered k tail⟩

/-- An already constructed chart covering a route supplies an actual
continuation, with its exact evaluator unchanged. No terminal identity is an
input and no analytic continuation search is used. -/
def singleChart (chart : Chart) {a b : D.Vertex} (p : Path D.Edge a b)
    (inside : ∀ x : D.Vertex, chart.map.domain x.val.val)
    (covered : ∀ x y : D.Vertex, D.Edge x y → chart.Covers x.val y.val) :
    Along p (chart.at a.val (inside a)) (chart.at b.val (inside b)) :=
  match p with
  | .nil _ => .nil (Setoid.refl _)
  | .cons e p => .cons e chart (inside _) (inside _) (covered _ _ e)
      (Setoid.refl _) (singleChart chart p inside covered)

end Along
end ComputableAnalysis.Continuation
