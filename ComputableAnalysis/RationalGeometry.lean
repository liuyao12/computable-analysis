import ComputableAnalysis.Basic

/-!
# Finite rational geometry

A polygon is an ordered finite list, read cyclically. Area carries orientation:
changing the first vertex has no effect; reversal changes the sign. No simple
polygon, convexity, angle, square root, integral, or completed real is required.
For a nonconvex or self-crossing cycle a vertex fan is an oriented sum, not a
claim that its triangles are disjoint subsets of a region.
-/
namespace ComputableAnalysis.RationalGeometry

structure Point where
  x : Rat
  y : Rat
  deriving Repr, DecidableEq

abbrev Polygon := List Point

def zero : Point := ⟨0, 0⟩
def add (p q : Point) : Point := ⟨p.x + q.x, p.y + q.y⟩
def sub (p q : Point) : Point := ⟨p.x - q.x, p.y - q.y⟩
def scale (s : Rat) (p : Point) : Point := ⟨s * p.x, s * p.y⟩
def det (p q : Point) : Rat := p.x * q.y - p.y * q.x

theorem det_self (p : Point) : det p p = 0 := by unfold det; grind
theorem det_swap (p q : Point) : det q p = -det p q := by unfold det; grind
theorem det_add_left (p q r : Point) : det (add p q) r = det p r + det q r := by
  unfold det add; grind

theorem det_add_right (p q r : Point) : det p (add q r) = det p q + det p r := by
  unfold det add; grind

theorem det_scale_left (s : Rat) (p q : Point) : det (scale s p) q = s * det p q := by
  unfold det scale; grind

theorem det_scale_right (s : Rat) (p q : Point) : det p (scale s q) = s * det p q := by
  unfold det scale; grind

/-- Finite area rules, treated as a specification rather than global axioms. -/
structure AreaForm where
  value : Point → Point → Rat
  add_left : ∀ u v w, value (add u v) w = value u w + value v w
  add_right : ∀ u v w, value u (add v w) = value u v + value u w
  scale_left : ∀ s u v, value (scale s u) v = s * value u v
  scale_right : ∀ s u v, value u (scale s v) = s * value u v
  alternating : ∀ u, value u u = 0
  normalized : value ⟨1,0⟩ ⟨0,1⟩ = 1

def determinantAreaForm : AreaForm where
  value := det
  add_left := det_add_left
  add_right := det_add_right
  scale_left := det_scale_left
  scale_right := det_scale_right
  alternating := det_self
  normalized := by decide +kernel

theorem AreaForm.swap (A : AreaForm) (u v : Point) : A.value v u = -A.value u v := by
  have h := A.alternating (add u v)
  rw [A.add_left, A.add_right, A.add_right, A.alternating, A.alternating] at h
  grind

/-- The finite rules characterize the determinant on rational vectors. -/
theorem AreaForm.unique (A : AreaForm) (u v : Point) : A.value u v = det u v := by
  let e1 : Point := ⟨1,0⟩
  let e2 : Point := ⟨0,1⟩
  have decomp (p : Point) : p = add (scale p.x e1) (scale p.y e2) := by
    cases p
    simp only [add, scale, e1, e2]
    congr 1 <;> grind
  have h12 : A.value e1 e2 = 1 := A.normalized
  have h21 : A.value e2 e1 = -1 := by rw [A.swap, h12]
  calc
    A.value u v = A.value (add (scale u.x e1) (scale u.y e2))
        (add (scale v.x e1) (scale v.y e2)) := by
          exact congr (congrArg A.value (decomp u)) (decomp v)
    _ = det u v := by
      rw [A.add_left, A.add_right, A.add_right]
      simp only [A.scale_left, A.scale_right, A.alternating, h12, h21]
      unfold det
      grind

/-- Area of the ordered parallelogram. -/
def parallelogramArea (u v : Point) : Rat := det u v

/-- Area of the ordered triangle; orientation is not discarded. -/
def triangleArea (p q r : Point) : Rat := det (sub q p) (sub r p) / 2

/-- The contribution of a directed boundary edge. -/
def edgeArea (p q : Point) : Rat := det p q / 2

theorem edgeArea_self (p : Point) : edgeArea p p = 0 := by
  simp [edgeArea, det_self, Rat.div_def]

theorem edgeArea_swap (p q : Point) : edgeArea q p = -edgeArea p q := by
  unfold edgeArea det; simp only [Rat.div_def]; grind

theorem triangle_boundary (p q r : Point) :
    triangleArea p q r = edgeArea p q + edgeArea q r + edgeArea r p := by
  unfold triangleArea edgeArea det sub; simp only [Rat.div_def]; grind

theorem triangle_cyclic (p q r : Point) : triangleArea q r p = triangleArea p q r := by
  rw [triangle_boundary, triangle_boundary]; grind

theorem triangle_reverse (p q r : Point) : triangleArea p r q = -triangleArea p q r := by
  unfold triangleArea det sub; simp only [Rat.div_def]; grind

theorem triangle_repeated_left (p q : Point) : triangleArea p p q = 0 := by
  simp only [triangleArea, sub, det, Rat.div_def]; grind

theorem triangle_repeated_right (p q : Point) : triangleArea p q p = 0 := by
  simp only [triangleArea, sub, det, Rat.div_def]; grind

/-- Subdivision with orientations; no interior-point assumption is needed. -/
theorem triangle_subdivision (o p q r : Point) :
    triangleArea p q r = triangleArea o q r + triangleArea p o r + triangleArea p q o := by
  unfold triangleArea det sub; simp only [Rat.div_def]; grind

/-- Sum over a walk, including the final edge to `finish`. -/
def walk (weight : Point → Point → Rat) (finish : Point) : Point → List Point → Rat
  | p, [] => weight p finish
  | p, q :: ps => weight p q + walk weight finish q ps

/-- Closing edge is implicit; the initial point is not repeated in the list. -/
def cycleSum (weight : Point → Point → Rat) : Polygon → Rat
  | [] => 0
  | p :: ps => walk weight p p ps

def area (P : Polygon) : Rat := cycleSum edgeArea P

/-- Use any point as the origin of the oriented triangle fan. -/
def fanArea (o : Point) (P : Polygon) : Rat := cycleSum (triangleArea o) P

/-- Choose a different first vertex; indices beyond the list return the list. -/
def startAt (P : Polygon) (k : Nat) : Polygon := P.drop k ++ P.take k

private theorem walk_snoc (w : Point → Point → Rat) (finish p q : Point) (ps : List Point) :
    walk w finish p (ps ++ [q]) = walk w q p ps + w q finish := by
  induction ps generalizing p with
  | nil => simp [walk]
  | cons r ps ih => simp only [List.cons_append, walk, ih]; grind

private theorem cycleSum_moveFirst (w : Point → Point → Rat) (p : Point) (ps : Polygon) :
    cycleSum w (ps ++ [p]) = cycleSum w (p :: ps) := by
  cases ps with
  | nil => rfl
  | cons q ps => simp only [List.cons_append, cycleSum, walk_snoc, walk]; grind

/-- Boundary sums do not depend on where a cyclic list is cut. -/
theorem cycleSum_append_comm (w : Point → Point → Rat) (P Q : Polygon) :
    cycleSum w (P ++ Q) = cycleSum w (Q ++ P) := by
  induction P generalizing Q with
  | nil => simp
  | cons p ps ih =>
    calc
      cycleSum w ((p :: ps) ++ Q) = cycleSum w ((ps ++ Q) ++ [p]) :=
        (cycleSum_moveFirst w p (ps ++ Q)).symm
      _ = cycleSum w (ps ++ (Q ++ [p])) := by rw [List.append_assoc]
      _ = cycleSum w ((Q ++ [p]) ++ ps) := ih (Q ++ [p])
      _ = cycleSum w (Q ++ (p :: ps)) := by simp [List.append_assoc]

theorem area_startAt (P : Polygon) (k : Nat) : area (startAt P k) = area P := by
  unfold startAt area
  rw [cycleSum_append_comm, List.take_append_drop]

private theorem walk_fan (o finish p : Point) (ps : List Point) :
    walk (triangleArea o) finish p ps =
      walk edgeArea finish p ps + edgeArea o p - edgeArea o finish := by
  induction ps generalizing p with
  | nil =>
    simp only [walk, triangle_boundary, edgeArea_swap finish o]; grind
  | cons q ps ih =>
    simp only [walk, triangle_boundary, ih, edgeArea_swap q o]; grind

/-- Every oriented fan has the same area, even if the fan origin is external. -/
theorem fanArea_eq_area (o : Point) (P : Polygon) : fanArea o P = area P := by
  cases P with
  | nil => rfl
  | cons p ps => simp only [fanArea, area, cycleSum, walk_fan]; grind

/-- The particular statement: change both the starting vertex and the fan. -/
theorem fanArea_startAt (o : Point) (P : Polygon) (k : Nat) :
    fanArea o (startAt P k) = area P := by
  rw [fanArea_eq_area, area_startAt]

/-- An open fan, with one triangle for each successive edge. -/
def fanFrom (o : Point) : Point → List Point → Rat
  | _, [] => 0
  | p, q :: ps => triangleArea o p q + fanFrom o q ps

/-- The vertex-fan algorithm; its first triangle is degenerate. -/
def triangulationArea : Polygon → Rat
  | [] => 0
  | p :: ps => fanFrom p p ps

private theorem fanFrom_eq_walk (o p : Point) (ps : List Point) :
    fanFrom o p ps = walk (triangleArea o) o p ps := by
  induction ps generalizing p with
  | nil => simp [fanFrom, walk, triangle_repeated_right]
  | cons q ps ih => simp only [fanFrom, walk, ih]

theorem triangulationArea_eq_area (P : Polygon) : triangulationArea P = area P := by
  cases P with
  | nil => rfl
  | cons p ps =>
    change fanFrom p p ps = area (p :: ps)
    rw [fanFrom_eq_walk]
    exact fanArea_eq_area p (p :: ps)

/-- Triangulating from any starting vertex gives exactly the same rational. -/
theorem triangulationArea_startAt (P : Polygon) (k : Nat) :
    triangulationArea (startAt P k) = area P := by
  rw [triangulationArea_eq_area, area_startAt]

private theorem walk_reverse (p q : Point) (ps : List Point) :
    walk edgeArea q p ps.reverse = -walk edgeArea p q ps := by
  induction ps generalizing p q with
  | nil => exact edgeArea_swap q p
  | cons r ps ih =>
    rw [List.reverse_cons, walk_snoc, ih]
    simp only [walk, edgeArea_swap r q]; grind

theorem area_reverse (P : Polygon) : area P.reverse = -area P := by
  cases P with
  | nil => simp [area, cycleSum]
  | cons p ps =>
    rw [List.reverse_cons]
    unfold area
    rw [cycleSum_moveFirst]
    exact walk_reverse p p ps

structure AffineMap where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  offset : Point

namespace AffineMap

def apply (M : AffineMap) (p : Point) : Point :=
  ⟨M.a * p.x + M.b * p.y + M.offset.x,
   M.c * p.x + M.d * p.y + M.offset.y⟩
def determinant (M : AffineMap) : Rat := M.a * M.d - M.b * M.c

theorem triangleArea_apply (M : AffineMap) (p q r : Point) :
    triangleArea (M.apply p) (M.apply q) (M.apply r) =
      M.determinant * triangleArea p q r := by
  unfold triangleArea sub det apply determinant
  simp only [Rat.div_def]
  grind

private theorem walk_apply (M : AffineMap) (o finish p : Point) (ps : List Point) :
    walk (triangleArea (M.apply o)) (M.apply finish) (M.apply p) (ps.map M.apply) =
      M.determinant * walk (triangleArea o) finish p ps := by
  induction ps generalizing p with
  | nil => exact M.triangleArea_apply o p finish
  | cons q ps ih =>
    simp only [List.map_cons, walk, triangleArea_apply, ih]; grind

theorem area_apply (M : AffineMap) (P : Polygon) :
    area (P.map M.apply) = M.determinant * area P := by
  rw [← fanArea_eq_area (M.apply zero), ← fanArea_eq_area zero P]
  cases P with
  | nil => simp [fanArea, cycleSum]
  | cons p ps => exact M.walk_apply zero p p ps

/-- Orientation is part of the isometry certificate. -/
def Orthogonal (M : AffineMap) : Prop :=
  M.a*M.a + M.c*M.c = 1 ∧ M.b*M.b + M.d*M.d = 1 ∧ M.a*M.b + M.c*M.d = 0

theorem determinant_sq_of_orthogonal (M : AffineMap) (h : M.Orthogonal) :
    M.determinant * M.determinant = 1 := by
  have h1 := h.1; have h2 := h.2.1; have h3 := h.2.2
  unfold determinant
  grind

/-- Proper rigid motions preserve area; reflections reverse it. -/
theorem area_of_determinant_one (M : AffineMap) (h : M.determinant = 1) (P : Polygon) :
    area (P.map M.apply) = area P := by rw [area_apply, h, Rat.one_mul]

end AffineMap

def translation (v : Point) : AffineMap := ⟨1,0,0,1,v⟩
def homothety (o : Point) (s : Rat) : AffineMap := ⟨s,0,0,s,sub o (scale s o)⟩

theorem area_translation (v : Point) (P : Polygon) :
    area (P.map (translation v).apply) = area P := by
  rw [AffineMap.area_apply]
  simp only [translation, AffineMap.determinant]; grind

theorem area_homothety (o : Point) (s : Rat) (P : Polygon) :
    area (P.map (homothety o s).apply) = s*s*area P := by
  rw [AffineMap.area_apply]
  simp only [homothety, AffineMap.determinant]; grind

/-- A three-dimensional point/vector, still entirely rational. -/
structure Point3 where
  x : Rat
  y : Rat
  z : Rat
  deriving Repr, DecidableEq

def sub3 (p q : Point3) : Point3 := ⟨p.x-q.x,p.y-q.y,p.z-q.z⟩
def scale3 (s : Rat) (p : Point3) : Point3 := ⟨s*p.x,s*p.y,s*p.z⟩
def det3 (u v w : Point3) : Rat :=
  u.x*(v.y*w.z-v.z*w.y)-u.y*(v.x*w.z-v.z*w.x)+u.z*(v.x*w.y-v.y*w.x)
def tetrahedronVolume (p q r s : Point3) : Rat :=
  det3 (sub3 q p) (sub3 r p) (sub3 s p) / 6

theorem tetrahedron_swap (p q r s : Point3) :
    tetrahedronVolume p r q s = -tetrahedronVolume p q r s := by
  unfold tetrahedronVolume det3 sub3; simp only [Rat.div_def]; grind

theorem tetrahedron_subdivision (o p q r s : Point3) :
    tetrahedronVolume p q r s = tetrahedronVolume o q r s +
      tetrahedronVolume p o r s + tetrahedronVolume p q o s + tetrahedronVolume p q r o := by
  unfold tetrahedronVolume det3 sub3; simp only [Rat.div_def]; grind

theorem tetrahedron_scale (c : Rat) (p q r s : Point3) :
    tetrahedronVolume (scale3 c p) (scale3 c q) (scale3 c r) (scale3 c s) =
      c*c*c*tetrahedronVolume p q r s := by
  unfold tetrahedronVolume det3 sub3 scale3; simp only [Rat.div_def]; grind

end ComputableAnalysis.RationalGeometry
