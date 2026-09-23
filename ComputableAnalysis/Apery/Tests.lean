import ComputableAnalysis.Apery.Companion

namespace ComputableAnalysis.Apery.Tests
open FormalPowerSeries

/-- Independent finite sums reproduce the classical initial Apéry numbers. -/
example : number 0=1 ∧ number 1=5 ∧ number 2=73 ∧ number 3=1445 ∧ number 4=33001 := by
  decide +kernel

/-- The companion is rational, not generally integral. -/
example : companion 0=0 ∧ companion 1=6 ∧ companion 2=351/4 ∧ companion 3=62531/36 := by
  decide +kernel

example : approximant 1=6/5 ∧ approximant 2=351/292 := by decide +kernel

/-- Non-singleton series computations are valid at both ends of the certified chart. -/
example : (value 0 (-1)).Valid ∧ (value 3 1).Valid :=
  ⟨value_valid (by decide) (by decide +kernel), value_valid (by decide) (by decide +kernel)⟩

example : ((value 0 (1/2)).compute 12).width = 1/1024 := by
  change ((geometricRaw _ 1 _).compute 12).width = _
  rw [geometricRaw_width]
  decide +kernel

/-- The formal operator is genuinely third order in ordinary derivatives. -/
example : operator 1 (ofPolynomial [0,0,0,1]) 3=27 := by decide +kernel

/-- The arithmetic identity excludes coinciding consecutive approximants at every index. -/
example (n : Nat) : approximant n ≠ approximant (n+1) :=
  Rat.ne_of_lt (approximant_increasing n)

end ComputableAnalysis.Apery.Tests
