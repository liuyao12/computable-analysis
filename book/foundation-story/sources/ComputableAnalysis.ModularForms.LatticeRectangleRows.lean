import ComputableAnalysis.ModularForms.CMFiniteSquaresNodup163

/-! Executable rectangular lattice enumeration by rows, with exact multiplicities. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

/-- All integers in the coordinate interval, in increasing order. -/
def latticeCoordinates (N : Nat) : List Int :=
  (List.range (2*N+1)).map (fun (i : Nat) => (i:Int)-(N:Int))

theorem mem_latticeCoordinates (x : Int) (N : Nat) :
    x ∈ latticeCoordinates N ↔ -(N:Int)≤x ∧ x≤(N:Int) := by
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi
    omega
  · intro hx
    apply List.mem_map.mpr
    refine ⟨(x+(N:Int)).toNat,List.mem_range.mpr (by omega),?_⟩
    omega

theorem latticeCoordinates_nodup (N : Nat) : (latticeCoordinates N).Nodup := by
  apply List.Pairwise.map _ _ (List.nodup_range (n := 2*N+1))
  intro i j hij he
  exact hij (by omega)

/-- The nonzero points in one horizontal row of a finite square. -/
def latticeRowPoints (N : Nat) (y : Int) : List QuadraticOrder163 :=
  ((latticeCoordinates N).map (fun x => (⟨x,y⟩ : QuadraticOrder163))).filter
    (fun u => decide (u≠zero))

theorem mem_latticeRowPoints (u : QuadraticOrder163) (N : Nat) (y : Int) :
    u ∈ latticeRowPoints N y ↔ u≠zero ∧ u.y=y ∧ -(N:Int)≤u.x ∧ u.x≤(N:Int) := by
  simp only [latticeRowPoints,List.mem_filter,decide_eq_true_eq,List.mem_map]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hu⟩
    exact ⟨hu,rfl,(mem_latticeCoordinates x N).mp hx⟩
  · rintro ⟨hu,hy,hx⟩
    exact ⟨⟨u.x,(mem_latticeCoordinates u.x N).mpr hx,ext rfl hy.symm⟩,hu⟩

theorem latticeRowPoints_nodup (N : Nat) (y : Int) : (latticeRowPoints N y).Nodup := by
  apply List.Pairwise.filter
  apply List.Pairwise.map _ _ (latticeCoordinates_nodup N)
  intro x x' hne he
  exact hne (congrArg QuadraticOrder163.x he)

/-- A full finite square, enumerated row by row with the origin omitted. -/
def latticeRectanglePoints (N : Nat) : List QuadraticOrder163 :=
  (latticeCoordinates N).flatMap (latticeRowPoints N)

theorem mem_latticeRectanglePoints (u : QuadraticOrder163) (N : Nat) :
    u ∈ latticeRectanglePoints N ↔ u≠zero ∧ shellRadius u≤N := by
  simp only [latticeRectanglePoints,List.mem_flatMap]
  constructor
  · rintro ⟨y,hy,hu⟩
    have hrow := (mem_latticeRowPoints u N y).mp hu
    have hcoord := (mem_latticeCoordinates y N).mp hy
    exact ⟨hrow.1,(shellRadius_le_iff u N).mpr ⟨hrow.2.2.1,hrow.2.2.2,
      by omega,by omega⟩⟩
  · intro hu
    have hb := (shellRadius_le_iff u N).mp hu.2
    refine ⟨u.y,(mem_latticeCoordinates u.y N).mpr ⟨hb.2.2.1,hb.2.2.2⟩,?_⟩
    exact (mem_latticeRowPoints u N u.y).mpr ⟨hu.1,rfl,hb.1,hb.2.1⟩

theorem latticeRectanglePoints_nodup (N : Nat) : (latticeRectanglePoints N).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro y _
    exact latticeRowPoints_nodup N y
  · apply (latticeCoordinates_nodup N).imp
    intro y y' hne u hu v hv he
    have hu' := (mem_latticeRowPoints u N y).mp hu
    have hv' := (mem_latticeRowPoints v N y').mp hv
    exact hne (by rw [← hu'.2.1,← hv'.2.1,he])

/-- Changing from square shells to rows preserves every lattice point exactly once. -/
theorem latticeRectanglePoints_square_perm (N : Nat) :
    (latticeRectanglePoints N).Perm (squarePoints N) := by
  apply (List.perm_ext_iff_of_nodup (latticeRectanglePoints_nodup N)
    (squarePoints_nodup N)).mpr
  intro u
  rw [mem_latticeRectanglePoints,mem_squarePoints]

end ComputableAnalysis.ModularForms.QuadraticOrder163
