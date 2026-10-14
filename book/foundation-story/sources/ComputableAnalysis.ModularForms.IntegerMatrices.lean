import ComputableAnalysis.Basic

/-! Integer determinant-one matrices for the modular action. -/
namespace ComputableAnalysis.ModularForms

structure SL2Z where
  a : Int
  b : Int
  c : Int
  d : Int
  determinant : a * d - b * c = 1

namespace SL2Z

@[ext] theorem ext {g h : SL2Z} (ha : g.a = h.a) (hb : g.b = h.b)
    (hc : g.c = h.c) (hd : g.d = h.d) : g = h := by
  cases g; cases h; simp_all

def identity : SL2Z := ⟨1, 0, 0, 1, by decide⟩

def multiply (g h : SL2Z) : SL2Z where
  a := g.a*h.a + g.b*h.c
  b := g.a*h.b + g.b*h.d
  c := g.c*h.a + g.d*h.c
  d := g.c*h.b + g.d*h.d
  determinant := by
    have hg := g.determinant
    have hh := h.determinant
    calc
      _ = (g.a*g.d-g.b*g.c)*(h.a*h.d-h.b*h.c) := by grind
      _ = 1 := by rw [hg, hh]; decide

def inverse (g : SL2Z) : SL2Z :=
  ⟨g.d, -g.b, -g.c, g.a, by have h := g.determinant; grind⟩

/-- Translation by one. -/
def T : SL2Z := ⟨1, 1, 0, 1, by decide⟩

/-- The transformation sending `z` to `-1/z`. -/
def S : SL2Z := ⟨0, -1, 1, 0, by decide⟩

/-- The central matrix whose fractional-linear action is the identity. -/
def minusIdentity : SL2Z := ⟨-1, 0, 0, -1, by decide⟩

theorem multiply_assoc (f g h : SL2Z) :
    multiply (multiply f g) h = multiply f (multiply g h) := by
  apply ext <;> simp only [multiply] <;> grind

theorem identity_multiply (g : SL2Z) : multiply identity g = g := by
  apply ext <;> simp [multiply, identity]

theorem multiply_identity (g : SL2Z) : multiply g identity = g := by
  apply ext <;> simp [multiply, identity]

theorem multiply_inverse (g : SL2Z) : multiply g (inverse g) = identity := by
  have h := g.determinant
  apply ext <;> simp only [multiply, inverse, identity] <;> grind

theorem inverse_multiply (g : SL2Z) : multiply (inverse g) g = identity := by
  have h := g.determinant
  apply ext <;> simp only [multiply, inverse, identity] <;> grind

theorem S_square : multiply S S = minusIdentity := by
  apply ext <;> decide

theorem ST_cube : multiply (multiply (multiply S T) (multiply S T)) (multiply S T) =
    minusIdentity := by
  apply ext <;> decide

/-- A determinant-one matrix has a nonzero bottom row. -/
theorem bottom_row_nonzero (g : SL2Z) : g.c ≠ 0 ∨ g.d ≠ 0 := by
  have h := g.determinant
  by_cases hc : g.c = 0
  · right; intro hd; simp [hc, hd] at h
  · exact Or.inl hc

end SL2Z
end ComputableAnalysis.ModularForms
