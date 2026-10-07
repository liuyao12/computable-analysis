import ComputableAnalysis.RiemannHilbert.PrecisionSearch

/-! Executable nearest-integer selection from a rational interval sample,
with a proved semantic error bound for arbitrary valid represented reals. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

private def roundingStage (x : RealRaw) (hx : x.Valid) : Nat :=
  PrecisionSearch.stage (ofRealRaw x) (ofRealRaw_valid _ hx) ⟨1/8,by decide +kernel⟩

/-- A nearest integer of an adequately precise rational midpoint. -/
def representedIntegerRounding (x : RealRaw) (hx : x.Valid) : Int :=
  ((x.compute (roundingStage x hx)).midpoint+1/2).floor

/-- The executable selected integer is within five eighths of the actual
represented value. Its precision stage is chosen internally. -/
theorem representedIntegerRounding_bounds (x : RealRaw) (hx : x.Valid) :
    (RealRaw.ofRat ((representedIntegerRounding x hx:Rat)-5/8)).Le x ∧
      x.Le (RealRaw.ofRat ((representedIntegerRounding x hx:Rat)+5/8)) := by
  let N := roundingStage x hx
  let t := (x.compute N).midpoint
  let k := representedIntegerRounding x hx
  have hfloor := Rat.floor_le (t+1/2)
  have hceil := Rat.lt_floor_add_one (t+1/2)
  change (k:Rat)≤t+1/2 at hfloor
  change t+1/2<((k+1:Int):Rat) at hceil
  rw [Rat.intCast_add] at hceil
  have hone : ((1:Int):Rat)=(1:Rat) := by decide +kernel
  rw [hone] at hceil
  have hw := (PrecisionSearch.stage_spec (ofRealRaw x) (ofRealRaw_valid _ hx) ⟨1/8,by decide +kernel⟩).1
  change (x.compute N).hi-(x.compute N).lo≤1/8 at hw
  have ho := RealRaw.interval_order_of_valid x hx N
  have hm := QInterval.midpoint_mem ho
  change (x.compute N).lo≤t ∧ t≤(x.compute N).hi at hm
  have hl : (k:Rat)-5/8≤(x.compute N).lo := by grind only
  have hu : (x.compute N).hi≤(k:Rat)+5/8 := by grind only
  constructor
  · intro n m
    have h := RealRaw.le_refl x hx N m
    change (k:Rat)-5/8≤(x.compute m).hi
    exact Rat.le_trans hl h
  · intro n m
    have h := RealRaw.le_refl x hx n N
    change (x.compute n).lo≤(k:Rat)+5/8
    exact Rat.le_trans h hu

end ComputableAnalysis.ModularForms
