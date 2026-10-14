import ComputableAnalysis.ModularForms.DyadicSampleFlattening

/-! Exact affine covariance of the executable dyadic midpoint list. -/
namespace ComputableAnalysis.ModularForms

def affineInterval (b s : Rat) (I : QInterval) : QInterval :=
  ⟨b+s*I.lo,b+s*I.hi⟩

theorem affineInterval_midpoint (b s : Rat) (I : QInterval) :
    (affineInterval b s I).midpoint=b+s*I.midpoint := by
  unfold affineInterval QInterval.midpoint
  grind only

theorem affineInterval_bisect (b s : Rat) (I : QInterval) (r : Bool) :
    affineInterval b s (bisectInterval I r)=bisectInterval (affineInterval b s I) r := by
  cases r <;> simp [affineInterval,bisectInterval,QInterval.midpoint]
  all_goals congr 1 <;> grind only

theorem dyadicMidpoints_affine (b s : Rat) (I : QInterval) (n : Nat) :
    dyadicMidpoints (affineInterval b s I) n =
      (dyadicMidpoints I n).map (fun u => b+s*u) := by
  induction n generalizing I with
  | zero => simp [dyadicMidpoints,affineInterval_midpoint]
  | succ n ih =>
    rw [dyadicMidpoints,← affineInterval_bisect,← affineInterval_bisect,ih,ih,
      dyadicMidpoints,List.map_append]

theorem unitDyadicMidpoints_subdivision (n : Nat) :
    dyadicMidpoints ⟨0,1⟩ (n+1)=
      (dyadicMidpoints ⟨0,1⟩ n).map (fun u => u/2) ++
      (dyadicMidpoints ⟨0,1⟩ n).map (fun u => (1+u)/2) := by
  have hl := dyadicMidpoints_affine 0 (1/2) (⟨0,1⟩ : QInterval) n
  have hr := dyadicMidpoints_affine (1/2) (1/2) (⟨0,1⟩ : QInterval) n
  have el : affineInterval 0 (1/2) ⟨0,1⟩=bisectInterval ⟨0,1⟩ false := by decide +kernel
  have er : affineInterval (1/2) (1/2) ⟨0,1⟩=bisectInterval ⟨0,1⟩ true := by decide +kernel
  rw [el] at hl
  rw [er] at hr
  rw [dyadicMidpoints,hl,hr]
  have fl : (fun u : Rat => 0+(1/2)*u)=(fun u => u/2) := by
    funext u
    grind only
  have fr : (fun u : Rat => 1/2+(1/2)*u)=(fun u => (1+u)/2) := by
    funext u
    grind only
  rw [fl,fr]

end ComputableAnalysis.ModularForms
