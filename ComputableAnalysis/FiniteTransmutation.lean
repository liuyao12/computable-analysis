import ComputableAnalysis.RationalGeometry

/-! # Finite transmutation of polygonal areas
Exact trapezoid and triangle identities replace the infinitesimal area steps.
These statements concern finite rational polygons, with their orientations.
-/
namespace ComputableAnalysis.RationalGeometry

/-- Signed area of the trapezoid under a directed edge. -/
def trapezoid (p q : Point) : Rat := (p.y + q.y) * (q.x - p.x) / 2

/-- Twice the oriented triangle with the sign used in transmutation. -/
def interceptMoment (p q : Point) : Rat := p.y * q.x - p.x * q.y

/-- The exact finite counterpart of `2 y dx = d(xy) + z dx`. -/
theorem trapezoid_transmutation (p q : Point) :
    2 * trapezoid p q = q.x*q.y - p.x*p.y + interceptMoment p q := by
  unfold trapezoid interceptMoment
  simp only [Rat.div_def]
  grind

/-- Interchanging the axes complements the two trapezoids in the endpoint rectangle. -/
theorem trapezoid_complement (p q : Point) :
    trapezoid p q + trapezoid ⟨p.y,p.x⟩ ⟨q.y,q.x⟩ = q.x*q.y-p.x*p.y := by
  unfold trapezoid
  simp only [Rat.div_def]
  grind

/-- If the chord has equation `y = m*x + z`, its triangle contribution is `z*dx`. -/
theorem interceptMoment_eq (p q : Point) (m z : Rat)
    (hp : p.y = m*p.x+z) (hq : q.y = m*q.x+z) :
    interceptMoment p q = z*(q.x-p.x) := by
  unfold interceptMoment
  grind

/-- Transmutation on an arbitrary finite rational chain, including its last edge. -/
theorem walk_trapezoid_transmutation (a b : Point) (ps : List Point) :
    2 * walk trapezoid b a ps = b.x*b.y-a.x*a.y + walk interceptMoment b a ps := by
  induction ps generalizing a with
  | nil => exact trapezoid_transmutation a b
  | cons p ps ih =>
      simp only [walk]
      have h := trapezoid_transmutation a p
      have ht := ih p
      grind

end ComputableAnalysis.RationalGeometry
