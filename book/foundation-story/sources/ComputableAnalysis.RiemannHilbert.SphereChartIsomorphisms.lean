import ComputableAnalysis.RiemannHilbert.SphereCoordinates

/-! Executable chart isomorphisms for sphere names and the nonzero
overlap. The induced change of coordinates agrees with the constructed,
proved holomorphic reciprocal. These are coordinate isomorphisms;
SphereSubspaceTopology supplies the separate chart homeomorphism laws. -/
namespace ComputableAnalysis.RiemannHilbert

namespace Scalar
instance : Setoid Scalar where
  r z w := z.val.Equiv w.val
  iseqv := ⟨fun z => ComplexRaw.equiv_refl _ z.property,
    fun h => ComplexRaw.equiv_symm h,
    fun {z w u} h k => ComplexRaw.equiv_trans z.property w.property u.property h k⟩
end Scalar

namespace SphereCoordinates
open ComplexRaw NonzeroBoxSearch RepresentedReciprocal

abbrev FinitePatch := {p : Name // finiteDomain p}
abbrev InfinityPatch := {p : Name // infinityDomain p}
abbrev Overlap := {p : Name // finiteDomain p ∧ infinityDomain p}
abbrev NonzeroScalar := {z : Scalar // Nonzero z}

instance : Setoid FinitePatch where
  r p q := p.val ≈ q.val
  iseqv := ⟨fun p => Setoid.refl p.val, fun h => Setoid.symm h, fun h k => Setoid.trans h k⟩

instance : Setoid InfinityPatch where
  r p q := p.val ≈ q.val
  iseqv := ⟨fun p => Setoid.refl p.val, fun h => Setoid.symm h, fun h k => Setoid.trans h k⟩

instance : Setoid Overlap where
  r p q := p.val ≈ q.val
  iseqv := ⟨fun p => Setoid.refl p.val, fun h => Setoid.symm h, fun h k => Setoid.trans h k⟩

instance : Setoid NonzeroScalar where
  r z w := z.val ≈ w.val
  iseqv := ⟨fun z => Setoid.refl z.val, fun h => Setoid.symm h, fun h k => Setoid.trans h k⟩

def finiteChart : ValueIso FinitePatch Scalar where
  forward := {
    eval p := finiteCoordinate p.val p.property
    congr {p q} hpq := finiteCoordinate_congr p.property q.property hpq }
  backward := {
    eval z := ⟨.finite z, trivial⟩
    congr {z w} hzw := hzw }
  backward_forward p := finiteCoordinate_name p.val p.property
  forward_backward z := equiv_refl _ z.property

def infinityChart : ValueIso InfinityPatch Scalar where
  forward := {
    eval p := infinityCoordinate p.val p.property
    congr {p q} hpq := infinityCoordinate_congr p.property q.property hpq }
  backward := {
    eval z := ⟨.infinity z, trivial⟩
    congr {z w} hzw := hzw }
  backward_forward p := infinityCoordinate_name p.val p.property
  forward_backward z := equiv_refl _ z.property

def finiteOverlap : ValueIso Overlap NonzeroScalar where
  forward := {
    eval p := ⟨finiteCoordinate p.val p.property.1,
      finiteCoordinate_nonzero p.val p.property.1 p.property.2⟩
    congr {p q} hpq := finiteCoordinate_congr p.property.1 q.property.1 hpq }
  backward := {
    eval z := ⟨.finite z.val, ⟨trivial,z.property⟩⟩
    congr {z w} hzw := hzw }
  backward_forward p := finiteCoordinate_name p.val p.property.1
  forward_backward z := equiv_refl _ z.val.property

def infinityOverlap : ValueIso Overlap NonzeroScalar where
  forward := {
    eval p := ⟨infinityCoordinate p.val p.property.2,
      infinityCoordinate_nonzero p.val p.property.1 p.property.2⟩
    congr {p q} hpq := infinityCoordinate_congr p.property.2 q.property.2 hpq }
  backward := {
    eval z := ⟨.infinity z.val, ⟨z.property,trivial⟩⟩
    congr {z w} hzw := hzw }
  backward_forward p := infinityCoordinate_name p.val p.property.2
  forward_backward z := equiv_refl _ z.val.property

def reciprocalIso : ValueIso NonzeroScalar NonzeroScalar where
  forward := {
    eval z := ⟨inverse z.val z.property, inverse_nonzero z.val z.property⟩
    congr {z w} hzw := inverse_congr z.val w.val z.property w.property hzw }
  backward := {
    eval z := ⟨inverse z.val z.property, inverse_nonzero z.val z.property⟩
    congr {z w} hzw := inverse_congr z.val w.val z.property w.property hzw }
  forward_backward z := involutive z.val z.property
  backward_forward z := involutive z.val z.property

def transition : ValueIso NonzeroScalar NonzeroScalar :=
  finiteOverlap.inverse.followedBy infinityOverlap

theorem transition_reciprocal :
    transition.forward.Equiv reciprocalIso.forward := by
  intro z
  exact equiv_refl _ (inverse z.val z.property).property

theorem transition_backward_reciprocal :
    transition.backward.Equiv reciprocalIso.backward := by
  intro z
  exact equiv_refl _ (inverse z.val z.property).property

theorem transition_forward_backward (z : NonzeroScalar) :
    transition.forward.eval (transition.backward.eval z) ≈ z := transition.forward_backward z

theorem transition_backward_forward (z : NonzeroScalar) :
    transition.backward.eval (transition.forward.eval z) ≈ z := transition.backward_forward z

end SphereCoordinates
end ComputableAnalysis.RiemannHilbert
