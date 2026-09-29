import ComputableAnalysis.Continuation.Chain
import ComputableAnalysis.Continuation.Affine

/-!
# The finite monodromy theorem for a supplied system of analytic germs

Fibers contain a chosen family of continuable germs, not every holomorphic
germ at a point. Local transports must be realized by actual chart chains.
The local transport laws and geometric fillings imply global path independence;
neither global conclusion is an assumed field. Constructing these local data
for arbitrary holomorphic germs is the remaining analytic theorem.
-/
namespace ComputableAnalysis.Continuation
open ComplexRaw FunctionTheory
universe v

structure GermSystem (D : Region) (F : D.Vertex → Type v) [∀ x, Setoid (F x)] where
  transport : Transport D.Edge D.Face F
  germ : ∀ x, F x → LocalFunction x.val
  germ_congr : ∀ x {s t : F x}, s ≈ t → germ x s ≈ germ x t
  germ_reflects : ∀ x {s t : F x}, germ x s ≈ germ x t → s ≈ t
  along_edge : ∀ {a b} (e : D.Edge a b) (s : F a),
    Along (.cons e (.nil b)) (germ a s) (germ b (transport.step e s))

namespace GermSystem
variable {D : Region} {F : D.Vertex → Type v} [∀ x, Setoid (F x)]
variable (S : GermSystem D F)

/-- Every finite transported value is realized by a chain of local
holomorphic functions, including overlap and whole-edge domain evidence. -/
theorem run_along {a b} (p : Path D.Edge a b) (s : F a) :
    Nonempty (Along p (S.germ a s) (S.germ b (S.transport.run p s))) := by
  induction p with
  | nil => exact ⟨.nil (Setoid.refl _)⟩
  | cons e p ih =>
      obtain ⟨tail⟩ := ih (S.transport.step e s)
      exact (S.along_edge e s).append_exists tail

/-- Unique terminal germ within the supplied locally coherent continuation
system on a domain with supplied finite fillings. -/
theorem terminal_germ_independent (H : FiniteSimplyConnected D.Edge D.Face)
    {a b} (p q : Path D.Edge a b) (s : F a) :
    S.germ b (S.transport.run p s) ≈ S.germ b (S.transport.run q s) :=
  S.germ_congr b (S.transport.path_independent H p q s)

/-- Equivalent initial germs may use different state representatives and
routes; terminal agreement follows from reflection, local congruence, and
finite homotopy invariance. -/
theorem terminal_from_equal_germs (H : FiniteSimplyConnected D.Edge D.Face)
    {a b} (p q : Path D.Edge a b) {s t : F a}
    (h : S.germ a s ≈ S.germ a t) :
    S.germ b (S.transport.run p s) ≈ S.germ b (S.transport.run q t) :=
  Setoid.trans (S.terminal_germ_independent H p q s)
    (S.germ_congr b (S.transport.run_congr q (S.germ_reflects a h)))

/-- Exact endpoint equality of represented computations. -/
theorem terminal_value_independent (H : FiniteSimplyConnected D.Edge D.Face)
    {a b} (p q : Path D.Edge a b) (s : F a) :
    (S.germ b (S.transport.run p s)).value.Equiv
      (S.germ b (S.transport.run q s)).value :=
  LocalFunction.value_congr (S.terminal_germ_independent H p q s)

end GermSystem

/-- A fully instantiated analytic germ system. The affine identity theorem
separately justifies using coefficient equivalence to represent these germs. -/
def Affine.germSystem (D : Region) : GermSystem D (fun _ => Affine) where
  transport := Affine.transport D
  germ := fun x f => f.localFunction x.val
  germ_congr := by intro x s t h; exact Affine.localFunction_congr h x.val
  germ_reflects := by intro x s t h; exact Affine.coefficients_of_germ x.val h
  along_edge := by
    intro a b e f
    let c : Chart := ⟨f.chart,(f.localFunction a.val).holomorphic⟩
    exact Along.singleChart c (.cons e (.nil b))
      (fun _ => True.intro) (fun _ _ _ _ => True.intro)

end ComputableAnalysis.Continuation
