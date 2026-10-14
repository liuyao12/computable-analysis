import ComputableAnalysis.ModularForms.CMLatticeShellBounds163

/-! Executable enumeration of square coordinate shells. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

def shellPoint (r : Nat) (i : Fin (8*r)) : QuadraticOrder163 :=
  if i.val<2*r then ⟨-(r:Int)+(i.val:Int),(r:Int)⟩
  else if i.val<4*r then ⟨(r:Int),3*(r:Int)-(i.val:Int)⟩
  else if i.val<6*r then ⟨5*(r:Int)-(i.val:Int),-(r:Int)⟩
  else ⟨-(r:Int),(i.val:Int)-7*(r:Int)⟩

theorem shellPoint_bounds (r : Nat) (i : Fin (8*r)) :
    -(r:Int)≤(shellPoint r i).x ∧ (shellPoint r i).x≤(r:Int) ∧
    -(r:Int)≤(shellPoint r i).y ∧ (shellPoint r i).y≤(r:Int) ∧
    ((shellPoint r i).x=(r:Int) ∨ (shellPoint r i).x= -(r:Int) ∨
      (shellPoint r i).y=(r:Int) ∨ (shellPoint r i).y= -(r:Int)) := by
  have hi := i.isLt
  unfold shellPoint
  split <;> (try split) <;> (try split) <;> dsimp only <;> omega

theorem shellPoint_nonzero (r : Nat) (hr : 0<r) (i : Fin (8*r)) : shellPoint r i≠zero := by
  have h := shellPoint_bounds r i
  intro hz
  rw [hz] at h
  simp only [zero] at h
  omega

theorem shellPoint_injective (r : Nat) (i j : Fin (8*r))
    (h : shellPoint r i=shellPoint r j) : i=j := by
  have hi := i.isLt
  have hj := j.isLt
  have hx := congrArg QuadraticOrder163.x h
  have hy := congrArg QuadraticOrder163.y h
  apply Fin.ext
  by_cases hi2 : i.val<2*r <;> by_cases hi4 : i.val<4*r <;>
    by_cases hi6 : i.val<6*r <;> by_cases hj2 : j.val<2*r <;>
    by_cases hj4 : j.val<4*r <;> by_cases hj6 : j.val<6*r <;>
    simp only [shellPoint,hi2,hi4,hi6,hj2,hj4,hj6,ite_true,ite_false] at hx hy <;>
    omega

theorem shellPoint_surjective (r : Nat) (hr : 0<r) (u : QuadraticOrder163)
    (hx : -(r:Int)≤u.x ∧ u.x≤(r:Int)) (hy : -(r:Int)≤u.y ∧ u.y≤(r:Int))
    (hs : u.x=(r:Int) ∨ u.x= -(r:Int) ∨ u.y=(r:Int) ∨ u.y= -(r:Int)) :
    ∃ i : Fin (8*r), shellPoint r i=u := by
  by_cases htop : u.y=(r:Int) ∧ u.x<(r:Int)
  · let k := (u.x+(r:Int)).toNat
    have hk : (k:Int)=u.x+(r:Int) := by dsimp [k]; omega
    refine ⟨⟨k,by omega⟩,?_⟩
    simp only [shellPoint,if_pos (show k<2*r by omega)]
    apply ext <;> dsimp only <;> omega
  · by_cases hright : u.x=(r:Int) ∧ -(r:Int)<u.y
    · let k := (3*(r:Int)-u.y).toNat
      have hk : (k:Int)=3*(r:Int)-u.y := by dsimp [k]; omega
      refine ⟨⟨k,by omega⟩,?_⟩
      simp only [shellPoint,if_neg (show ¬k<2*r by omega),if_pos (show k<4*r by omega)]
      apply ext <;> dsimp only <;> omega
    · by_cases hbottom : u.y= -(r:Int) ∧ -(r:Int)<u.x
      · let k := (5*(r:Int)-u.x).toNat
        have hk : (k:Int)=5*(r:Int)-u.x := by dsimp [k]; omega
        refine ⟨⟨k,by omega⟩,?_⟩
        simp only [shellPoint,if_neg (show ¬k<2*r by omega),
          if_neg (show ¬k<4*r by omega),if_pos (show k<6*r by omega)]
        apply ext <;> dsimp only <;> omega
      · let k := (u.y+7*(r:Int)).toNat
        have hk : (k:Int)=u.y+7*(r:Int) := by dsimp [k]; omega
        refine ⟨⟨k,by omega⟩,?_⟩
        simp only [shellPoint,if_neg (show ¬k<2*r by omega),
          if_neg (show ¬k<4*r by omega),if_neg (show ¬k<6*r by omega)]
        apply ext <;> dsimp only <;> omega

end ComputableAnalysis.ModularForms.QuadraticOrder163
