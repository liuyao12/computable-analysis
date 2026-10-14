import ComputableAnalysis.ComplexAffine
import ComputableAnalysis.ModularForms.IntegerMatrices

/-! The represented upper half-plane and its translation action.
Domain membership is invariant under valid equivalent representations. -/
namespace ComputableAnalysis.ModularForms

/-- Strict positivity survives a change of valid interval representation. -/
theorem positive_of_equiv {x y : RealRaw} (hx : x.Valid) (hy : y.Valid)
    (hxy : x.Equiv y) (hp : x.Pos) : y.Pos := by
  obtain ⟨N, hN⟩ := hp
  let eps : QPos := ⟨(x.compute N).lo / 2, by grind⟩
  obtain ⟨K, hK⟩ := hy.2.2 eps
  let M := max N K
  have hn := hx.2.1 N M (Nat.le_max_left _ _)
  have ho := (RealRaw.compareAt_overlap_iff x y M M).mp (hxy M)
  have hw := hK M (Nat.le_max_right _ _)
  refine ⟨M, ?_⟩
  change 0 < (y.compute M).lo
  change (y.compute M).hi - (y.compute M).lo ≤ (x.compute N).lo / 2 at hw
  have hb : (x.compute N).lo ≤ (y.compute M).hi := Rat.le_trans hn.1 ho.1
  grind only

/-- Every represented point with strictly positive imaginary coordinate. -/
def InUpperHalfPlane (z : ComplexRaw) : Prop := z.imagPart.Pos

theorem upperHalfPlane_congr {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid)
    (hzw : z.Equiv w) : InUpperHalfPlane z ↔ InUpperHalfPlane w := by
  constructor
  · exact positive_of_equiv (ComplexRaw.imagPart_valid hz)
      (ComplexRaw.imagPart_valid hw) (ComplexRaw.imagPart_equiv hzw)
  · exact positive_of_equiv (ComplexRaw.imagPart_valid hw)
      (ComplexRaw.imagPart_valid hz) (ComplexRaw.imagPart_equiv (ComplexRaw.equiv_symm hzw))

/-- Translation by an arbitrary rational real number, preserving executability. -/
def translate (r : Rat) (z : ComplexRaw) : ComplexRaw :=
  ComplexRaw.add z (ComplexRaw.ofQComplex ⟨r, 0⟩)

theorem translate_valid (r : Rat) {z : ComplexRaw} (hz : z.Valid) :
    (translate r z).Valid :=
  ComplexRaw.add_valid hz (ComplexRaw.ofQComplex_valid _)

/-- Translation leaves the imaginary-coordinate interval algorithm unchanged. -/
theorem translate_imagPart (r : Rat) (z : ComplexRaw) :
    (translate r z).imagPart.compute = z.imagPart.compute := by
  cases z
  simp [translate, ComplexRaw.add, ComplexRaw.ofQComplex, ComplexRaw.imagPart,
    QBox.add, QComplex.add, Rat.add_zero]

theorem translate_mem (r : Rat) {z : ComplexRaw} (hz : InUpperHalfPlane z) :
    InUpperHalfPlane (translate r z) := by
  unfold InUpperHalfPlane RealRaw.Pos
  rw [translate_imagPart]
  exact hz

theorem translate_equiv (r : Rat) {z w : ComplexRaw} (hzw : z.Equiv w) :
    (translate r z).Equiv (translate r w) :=
  ComplexRaw.add_equiv hzw (ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _))

/-- Successive translations implement addition on the represented value. -/
theorem translate_compose (r s : Rat) {z : ComplexRaw} (hz : z.Valid) :
    (translate r (translate s z)).Equiv (translate (r+s) z) := by
  have he : (translate r (translate s z)).compute = (translate (r+s) z).compute := by
    funext n
    simp [translate, ComplexRaw.add, ComplexRaw.ofQComplex, QBox.add, QComplex.add]
    congr 1 <;> grind [Rat.add_assoc, Rat.add_comm]
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).mpr
  rw [show (translate r (translate s z)).compute n = (translate (r+s) z).compute n from congrFun he n]
  exact (ComplexRaw.compareAt_overlap_iff _ _ n n).mp
    (ComplexRaw.equiv_refl _ (translate_valid (r+s) hz) n)

end ComputableAnalysis.ModularForms
