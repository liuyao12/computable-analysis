import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

/-! Finite translation of symmetric lattice sums leaves exactly two boundary terms. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

def symmetricLatticeSum (f : Int → ScalarAlgebra.Value) : Nat → ScalarAlgebra.Value
  | 0 => f 0
  | N+1 => symmetricLatticeSum f N+f (-((N+1:Nat):Int))+f ((N+1:Nat):Int)

theorem symmetricLatticeSum_shift (f : Int → ScalarAlgebra.Value) (N : Nat) :
    symmetricLatticeSum (fun k => f (k+1)) N-symmetricLatticeSum f N =
      f ((N:Int)+1)-f (-(N:Int)) := by
  induction N with
  | zero => change f 1-f 0=f 1-f 0; rfl
  | succ N ih =>
    simp only [symmetricLatticeSum.eq_2]
    have hm : -((N+1:Nat):Int)+1= -(N:Int) := by omega
    have hp : ((N+1:Nat):Int)+1=(N:Int)+2 := by omega
    have hs : ((N+1:Nat):Int)=(N:Int)+1 := by omega
    rw [hm,hp,hs]
    let A := symmetricLatticeSum (fun k => f (k+1)) N
    let B := symmetricLatticeSum f N
    let U := f ((N:Int)+1)
    let V := f (-(N:Int))
    let W := f ((N:Int)+2)
    let X := f (-((N:Int)+1))
    change A-B=U-V at ih
    change (A+V+W)-(B+X+U)=W-X
    grind only

end ComputableAnalysis.ModularForms
