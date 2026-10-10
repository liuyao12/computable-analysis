import RationalHalfspaceElimination
open ComputableAnalysis.RationalPolytopeVolume
open ComputableAnalysis.RationalConvexBodies

def intervalSystem : Finset (RationalConstraint 1 1) :=
  {⟨fun _ => 1,fun _ => 0,1⟩,
   ⟨fun _ => -1,fun _ => 1,0⟩,
   ⟨fun _ => 0,fun _ => -1,0⟩}
#eval (eliminateAll 1 1 intervalSystem).card
#eval ((eliminateAll 1 1 intervalSystem).image (fun r => r.normal 0)).sort (· ≤ ·)
#eval ((eliminateAll 1 1 intervalSystem).image (fun r => r.bound)).sort (· ≤ ·)
#eval ((eliminateAll 1 1 intervalSystem).filter (fun r => r.bound < dot r.normal (fun _ => 1/2))).card == 0
#eval ((eliminateAll 1 1 intervalSystem).filter (fun r => r.bound < dot r.normal (fun _ => 2))).card == 0

def impossibleSystem : Finset (RationalConstraint 1 1) :=
  {⟨fun _ => 1,0,0⟩,⟨fun _ => -1,0,-1⟩}
#eval ((eliminateAll 1 1 impossibleSystem).filter (fun r => r.bound < dot r.normal 0)).card == 0

def lowerOnlySystem : Finset (RationalConstraint 1 1) := {⟨fun _ => -1,fun _ => 1,0⟩}
#eval (eliminateAll 1 1 lowerOnlySystem).card
