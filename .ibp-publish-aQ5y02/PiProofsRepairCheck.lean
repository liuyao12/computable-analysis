import ComputableAnalysis.ArctanPresentations

namespace ComputableAnalysis

example {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    arctan.series.raw.definedAt x := by
  change qabs x <= 1
  rw [qabs_eq_self_of_nonneg hx0]
  exact hx1

example (rep : Nat) (hrep : rep ∈ [1, 2, 3]) : True := by
  rcases List.mem_cons.mp hrep with h | hrep
  · subst rep
    trivial
  rcases List.mem_cons.mp hrep with h | hrep
  · subst rep
    trivial
  have h := List.mem_singleton.mp hrep
  subst rep
  trivial

end ComputableAnalysis
