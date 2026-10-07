import ComputableAnalysis.ModularForms.LatticeRectangleRows

/-! Finite wide lattice rectangles, as selected square points and as actual rows. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

def wideRectangleKeep (N : Nat) (u : QuadraticOrder163) : Bool :=
  decide (-(N:Int)≤u.y ∧ u.y≤(N:Int))

def latticeWideRectanglePoints (M N : Nat) : List QuadraticOrder163 :=
  (squarePoints M).filter (wideRectangleKeep N)

theorem mem_latticeWideRectanglePoints (u : QuadraticOrder163) (M N : Nat) :
    u ∈ latticeWideRectanglePoints M N ↔
      u≠zero ∧ shellRadius u≤M ∧ -(N:Int)≤u.y ∧ u.y≤(N:Int) := by
  simp only [latticeWideRectanglePoints,List.mem_filter,wideRectangleKeep,
    decide_eq_true_eq,mem_squarePoints,and_assoc]

theorem latticeWideRectanglePoints_nodup (M N : Nat) :
    (latticeWideRectanglePoints M N).Nodup :=
  List.Pairwise.filter _ (squarePoints_nodup M)

private theorem rows_nodup (M N : Nat) :
    ((latticeCoordinates N).flatMap (latticeRowPoints M)).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro y _
    exact latticeRowPoints_nodup M y
  · apply (latticeCoordinates_nodup N).imp
    intro y y' hne u hu v hv he
    have h1 := (mem_latticeRowPoints u M y).mp hu
    have h2 := (mem_latticeRowPoints v M y').mp hv
    exact hne (by rw [← h1.2.1,← h2.2.1,he])

/-- A wide rectangle contains each selected point exactly once in its row assembly. -/
theorem latticeWideRectanglePoints_rows_perm (M N : Nat) (hNM : N≤M) :
    (latticeWideRectanglePoints M N).Perm
      ((latticeCoordinates N).flatMap (latticeRowPoints M)) := by
  apply (List.perm_ext_iff_of_nodup (latticeWideRectanglePoints_nodup M N) (rows_nodup M N)).mpr
  intro u
  constructor
  · intro hu
    have hb := (mem_latticeWideRectanglePoints u M N).mp hu
    have hr := (shellRadius_le_iff u M).mp hb.2.1
    apply List.mem_flatMap.mpr
    refine ⟨u.y,(mem_latticeCoordinates u.y N).mpr ⟨hb.2.2.1,hb.2.2.2⟩,?_⟩
    exact (mem_latticeRowPoints u M u.y).mpr ⟨hb.1,rfl,hr.1,hr.2.1⟩
  · intro hu
    obtain ⟨y,hy,hrow⟩ := List.mem_flatMap.mp hu
    have hb := (mem_latticeRowPoints u M y).mp hrow
    have hc := (mem_latticeCoordinates y N).mp hy
    apply (mem_latticeWideRectanglePoints u M N).mpr
    refine ⟨hb.1,?_,by omega,by omega⟩
    apply (shellRadius_le_iff u M).mpr
    exact ⟨hb.2.2.1,hb.2.2.2,by omega,by omega⟩

/-- Every discarded point lies outside the inner square, uniformly in the width. -/
theorem wideRectangle_discarded_annulus (M N : Nat) (u : QuadraticOrder163)
    (hu : u ∈ (squarePoints M).filter (fun u => !wideRectangleKeep N u)) :
    u≠zero ∧ N<shellRadius u ∧ shellRadius u≤N+M := by
  obtain ⟨hs,hkeep⟩ := List.mem_filter.mp hu
  have hb := (mem_squarePoints u M).mp hs
  have hr := shellRadius_bounds u
  have hnot : ¬(-(N:Int)≤u.y ∧ u.y≤(N:Int)) := by
    intro h
    simp [wideRectangleKeep,h] at hkeep
  exact ⟨hb.1,by omega,by omega⟩

end ComputableAnalysis.ModularForms.QuadraticOrder163
