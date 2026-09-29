import ComputableAnalysis.Continuation.FinitePath

/-!
# Transport along finite paths and the finite monodromy theorem

Local stationary, inverse, and filled-triangle laws imply homotopy invariance
by induction on an explicit filling. No global uniqueness/path-independence
field is assumed. Applying this theorem to analytic germs still requires
constructing their local transport and proving these local laws.
-/
namespace ComputableAnalysis.Continuation
universe u v
variable {X : Type u} {E : X → X → Prop} {Face : X → X → X → Prop}

structure Transport (E : X → X → Prop) (Face : X → X → X → Prop)
    (F : X → Type v) [∀ x, Setoid (F x)] where
  step : ∀ {a b}, E a b → F a → F b
  congr : ∀ {a b} (e : E a b) {s t : F a}, s ≈ t → step e s ≈ step e t
  stationary : ∀ {a} (e : E a a) (s : F a), step e s ≈ s
  inverse : ∀ {a b} (e : E a b) (f : E b a) (s : F a), step f (step e s) ≈ s
  triangle : ∀ {a b c} (e : E a b) (f : E b c) (g : E a c), Face a b c →
    ∀ s : F a, step f (step e s) ≈ step g s

namespace Transport
variable {F : X → Type v} [∀ x, Setoid (F x)]
variable (T : Transport E Face F)

def run {a b} (p : Path E a b) (s : F a) : F b :=
  match p with
  | .nil _ => s
  | .cons e p => run p (T.step e s)

@[simp] theorem run_nil {a} (s : F a) : T.run (.nil a) s = s := rfl
@[simp] theorem run_cons {a b c} (e : E a b) (p : Path E b c) (s : F a) :
    T.run (.cons e p) s = T.run p (T.step e s) := rfl

theorem run_congr {a b} (p : Path E a b) {s t : F a} (h : s ≈ t) :
    T.run p s ≈ T.run p t := by
  induction p with
  | nil => exact h
  | cons e p ih => exact ih (T.congr e h)

theorem run_append {a b c} (p : Path E a b) (q : Path E b c) (s : F a) :
    T.run (p.append q) s = T.run q (T.run p s) := by
  induction p with
  | nil => rfl
  | cons e p ih => exact ih q (T.step e s)

/-- The local laws, rather than a uniqueness field, prove invariance under a
finite filling. This theorem does not assert that a filling always exists. -/
theorem homotopy_invariant {a b} {p q : Path E a b}
    (h : Homotopy E Face p q) (s : F a) : T.run p s ≈ T.run q s := by
  induction h with
  | refl => exact Setoid.refl _
  | symm h ih => exact Setoid.symm (ih s)
  | trans h k ih ik => exact Setoid.trans (ih s) (ik s)
  | cons e h ih => exact ih (T.step e s)
  | stationary e => exact T.stationary e s
  | backtrack e f => exact T.inverse e f s
  | triangle e f g h => exact T.triangle e f g h s
  | append h r ih =>
      simp only [run_append]
      exact T.run_congr r (ih s)

theorem path_independent (D : FiniteSimplyConnected E Face) {a b}
    (p q : Path E a b) (s : F a) : T.run p s ≈ T.run q s :=
  T.homotopy_invariant (D.fill p q) s

theorem reverse_left (symm : ∀ {a b}, E a b → E b a) {a b}
    (p : Path E a b) (s : F a) : T.run (p.reverse symm) (T.run p s) ≈ s := by
  induction p with
  | nil => exact Setoid.refl _
  | cons e p ih =>
      simp only [Path.reverse, run_append, run_cons, run_nil]
      exact Setoid.trans (T.congr (symm e) (ih (T.step e s))) (T.inverse e (symm e) s)

/-- A section compatible with the local transports. For analytic germs,
turning such a section into a holomorphic map requires local realization. -/
def Parallel (section_ : ∀ x, F x) : Prop :=
  ∀ {a b} (e : E a b), T.step e (section_ a) ≈ section_ b

def sectionFrom (D : FiniteSimplyConnected E Face) (a : X) (s : F a) : ∀ b, F b :=
  fun b => T.run (D.route a b) s

theorem section_base (D : FiniteSimplyConnected E Face) (a : X) (s : F a) :
    T.sectionFrom D a s a ≈ s :=
  T.path_independent D (D.route a a) (.nil a) s

theorem section_parallel (D : FiniteSimplyConnected E Face) (a : X) (s : F a) :
    T.Parallel (T.sectionFrom D a s) := by
  intro b c e
  have h := T.path_independent D ((D.route a b).append (.cons e (.nil c)))
    (D.route a c) s
  simpa only [run_append, run_cons, run_nil, sectionFrom] using h

theorem parallel_run (g : ∀ x, F x) (hg : T.Parallel g) {a b}
    (p : Path E a b) : T.run p (g a) ≈ g b := by
  induction p with
  | nil => exact Setoid.refl _
  | cons e p ih => exact Setoid.trans (T.run_congr p (hg e)) ih

/-- Uniqueness of compatible sections uses only a connecting path. Simple
connectedness is needed to construct a section independently of routes, not
to compare two sections that are already compatible with every edge. -/
theorem parallel_unique_on_path (g h : ∀ x, F x)
    (hg : T.Parallel g) (hh : T.Parallel h) {a b : X}
    (p : Path E a b) (hbase : g a ≈ h a) : g b ≈ h b :=
  Setoid.trans (Setoid.symm (T.parallel_run g hg p))
    (Setoid.trans (T.run_congr p hbase) (T.parallel_run h hh p))

/-- The finite monodromy conclusion: a supplied seed has a unique parallel
extension, modulo the fiber equivalence, with executable route evaluation. -/
theorem section_unique (D : FiniteSimplyConnected E Face) (a : X) (s : F a)
    (g : ∀ x, F x) (hg : T.Parallel g) (hbase : g a ≈ s) (b : X) :
    g b ≈ T.sectionFrom D a s b :=
  Setoid.trans (Setoid.symm (T.parallel_run g hg (D.route a b)))
    (T.run_congr (D.route a b) hbase)

end Transport
end ComputableAnalysis.Continuation
