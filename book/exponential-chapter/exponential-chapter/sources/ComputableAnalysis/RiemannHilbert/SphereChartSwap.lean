import ComputableAnalysis.RiemannHilbert.SphereChartIsomorphisms

/-! Interchanging the two sphere charts is an executable involution.
It transports chart-domain and coordinate names, including the zero
coordinate representing the infinity point. -/
namespace ComputableAnalysis.RiemannHilbert.SphereCoordinates
open ComplexRaw

def swap : Name → Name
  | .finite z => .infinity z
  | .infinity z => .finite z

theorem swap_equiv {p q : Name} (hpq : p ≈ q) : swap p ≈ swap q := by
  cases p <;> cases q <;> exact hpq

theorem swap_swap (p : Name) : swap (swap p) = p := by cases p <;> rfl

def swapIso : ValueIso Name Name where
  forward := { eval := swap, congr := swap_equiv }
  backward := { eval := swap, congr := swap_equiv }
  forward_backward p := by change swap (swap p) ≈ p; rw [swap_swap]; exact Setoid.refl p
  backward_forward p := by change swap (swap p) ≈ p; rw [swap_swap]; exact Setoid.refl p

theorem swap_finiteDomain (p : Name) : finiteDomain (swap p) ↔ infinityDomain p := by
  cases p <;> exact Iff.rfl

theorem swap_infinityDomain (p : Name) : infinityDomain (swap p) ↔ finiteDomain p := by
  cases p <;> exact Iff.rfl

theorem swap_finiteCoordinate (p : Name) (hp : infinityDomain p) :
    (finiteCoordinate (swap p) ((swap_finiteDomain p).2 hp)).val.Equiv
      (infinityCoordinate p hp).val := by
  cases p with
  | finite z => exact equiv_refl _ (RepresentedReciprocal.inverse z hp).property
  | infinity z => exact equiv_refl _ z.property

theorem swap_infinityCoordinate (p : Name) (hp : finiteDomain p) :
    (infinityCoordinate (swap p) ((swap_infinityDomain p).2 hp)).val.Equiv
      (finiteCoordinate p hp).val := by
  cases p with
  | finite z => exact equiv_refl _ z.property
  | infinity z => exact equiv_refl _ (RepresentedReciprocal.inverse z hp).property

end ComputableAnalysis.RiemannHilbert.SphereCoordinates
