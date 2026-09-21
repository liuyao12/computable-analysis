import ComputableAnalysis.FiniteSampleCalculus

/-! Powers of a local derivative model. Extracted from UnitPowerCalculus so
ordinary calculus clients do not depend on the Cartwright application. -/
namespace ComputableAnalysis.UnitPowerCalculus
open FiniteSampleCalculus

def slopePower (F D : SampleFunction) : Nat → SampleFunction
  | 0 => fun _ _ => 0
  | n+1 => fun x q => ((n+1:Nat):Rat)*F x q^n*D x q

def modelPower {F D : SampleFunction} (f : Model F D) :
    (n : Nat) → Model (fun x q => F x q^n) (slopePower F D n)
  | 0 => (Model.const 1).congr (by intro x q;rw [Rat.pow_zero]) (fun _ _ => rfl)
  | n+1 => ((modelPower f n).mul f).congr
      (by intro x q;rw [Rat.pow_succ])
      (by
        intro x q
        cases n with
        | zero => simp only [slopePower,Rat.pow_zero,Rat.natCast_add,Rat.natCast_ofNat]; grind only
        | succ n =>
          simp only [slopePower,Rat.pow_succ,Rat.natCast_add,Rat.natCast_ofNat]
          grind only)

end ComputableAnalysis.UnitPowerCalculus
