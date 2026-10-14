import ComputableAnalysis.RiemannHilbert.SphereTopology

/-! Subspace topology on supplied represented sphere domains, and the
topological chart identities for the constructed coordinate value maps.
Arbitrary unions are proved without selecting an executable witness from
an arbitrary existential open-set membership. -/
namespace ComputableAnalysis.RiemannHilbert.SphereTopology
open SphereCoordinates

def IsOpenOn (D : Name → Prop) (U : {p : Name // D p} → Prop) : Prop :=
  ∃ V : Name → Prop, IsOpen V ∧ ∀ p, U p ↔ V p.val

theorem isOpenOn_univ (D : Name → Prop) : IsOpenOn D (fun _ => True) :=
  ⟨fun _ => True,isOpen_univ,fun _ => Iff.rfl⟩

theorem isOpenOn_empty (D : Name → Prop) : IsOpenOn D (fun _ => False) :=
  ⟨fun _ => False,isOpen_empty,fun _ => Iff.rfl⟩

theorem isOpenOn_inter {D : Name → Prop} {U V : {p : Name // D p} → Prop}
    (hU : IsOpenOn D U) (hV : IsOpenOn D V) : IsOpenOn D (fun p => U p ∧ V p) := by
  obtain ⟨A,hA,hUA⟩ := hU
  obtain ⟨B,hB,hVB⟩ := hV
  exact ⟨fun p => A p ∧ B p,isOpen_inter hA hB,fun p =>
    ⟨fun h => ⟨(hUA p).1 h.1,(hVB p).1 h.2⟩,fun h => ⟨(hUA p).2 h.1,(hVB p).2 h.2⟩⟩⟩

theorem isOpenOn_union {D : Name → Prop} {I : Sort u} (U : I → {p : Name // D p} → Prop)
    (hU : ∀ i, IsOpenOn D (U i)) : IsOpenOn D (fun p => ∃ i, U i p) := by
  let J := {V : Name → Prop // IsOpen V ∧ ∃ i, ∀ p, U i p ↔ V p.val}
  let W : Name → Prop := fun p => ∃ j : J, j.val p
  refine ⟨W,isOpen_union (fun j : J => j.val) (fun j => j.property.1),?_⟩
  intro p
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨V,hV,hUV⟩ := hU i
    exact ⟨⟨V,hV,i,hUV⟩,(hUV p).1 hi⟩
  · rintro ⟨j,hj⟩
    obtain ⟨i,hij⟩ := j.property.2
    exact ⟨i,(hij p).2 hj⟩

theorem isOpenOn_congr {D : Name → Prop} {U V : {p : Name // D p} → Prop}
    (hUV : ∀ p, U p ↔ V p) (hU : IsOpenOn D U) : IsOpenOn D V := by
  obtain ⟨W,hW,hUW⟩ := hU
  exact ⟨W,hW,fun p => (hUV p).symm.trans (hUW p)⟩

theorem isOpenOn_invariant {D : Name → Prop} {U : {p : Name // D p} → Prop}
    (hU : IsOpenOn D U) (p q : {p : Name // D p}) (hpq : p.val ≈ q.val) : U p ↔ U q := by
  obtain ⟨V,hV,hUV⟩ := hU
  exact (hUV p).trans ((hV.invariant p.val q.val hpq).trans (hUV q).symm)

theorem isOpenOn_of_open {D U : Name → Prop} (hU : IsOpen U) : IsOpenOn D (fun p => U p.val) :=
  ⟨U,hU,fun _ => Iff.rfl⟩

theorem finiteChart_continuous (D : Scalar → Prop) (hD : ScalarTopology.IsOpen D) :
    IsOpenOn finiteDomain (fun p => D (finiteChart.forward.eval p)) := by
  refine ⟨liftFinite D,isOpen_liftFinite D hD,?_⟩
  intro p
  exact ⟨fun h => ⟨p.property,h⟩,fun ⟨_,h⟩ => h⟩

theorem infinityChart_continuous (D : Scalar → Prop) (hD : ScalarTopology.IsOpen D) :
    IsOpenOn infinityDomain (fun p => D (infinityChart.forward.eval p)) := by
  refine ⟨liftInfinity D,isOpen_liftInfinity D hD,?_⟩
  intro p
  exact ⟨fun h => ⟨p.property,h⟩,fun ⟨_,h⟩ => h⟩

theorem finiteChart_inverse_continuous (U : FinitePatch → Prop) (hU : IsOpenOn finiteDomain U) :
    ScalarTopology.IsOpen (fun z => U (finiteChart.backward.eval z)) := by
  obtain ⟨V,hV,hUV⟩ := hU
  exact ScalarTopology.isOpen_congr (fun z => (hUV (finiteChart.backward.eval z)).symm) hV.finite

theorem infinityChart_inverse_continuous (U : InfinityPatch → Prop) (hU : IsOpenOn infinityDomain U) :
    ScalarTopology.IsOpen (fun z => U (infinityChart.backward.eval z)) := by
  obtain ⟨V,hV,hUV⟩ := hU
  exact ScalarTopology.isOpen_congr (fun z => (hUV (infinityChart.backward.eval z)).symm) hV.infinity

theorem finiteChart_open_iff (U : FinitePatch → Prop) :
    IsOpenOn finiteDomain U ↔
      (∀ p q : FinitePatch, p ≈ q → (U p ↔ U q)) ∧
      ScalarTopology.IsOpen (fun z => U (finiteChart.backward.eval z)) := by
  constructor
  · intro hU
    exact ⟨fun p q hpq => isOpenOn_invariant hU p q hpq,finiteChart_inverse_continuous U hU⟩
  · rintro ⟨hInv,hOpen⟩
    let D := fun z => U (finiteChart.backward.eval z)
    refine ⟨liftFinite D,isOpen_liftFinite D hOpen,?_⟩
    intro p
    have he := hInv (finiteChart.backward.eval (finiteChart.forward.eval p)) p (finiteChart.backward_forward p)
    exact ⟨fun h => ⟨p.property,he.2 h⟩,fun ⟨_,h⟩ => he.1 h⟩

theorem infinityChart_open_iff (U : InfinityPatch → Prop) :
    IsOpenOn infinityDomain U ↔
      (∀ p q : InfinityPatch, p ≈ q → (U p ↔ U q)) ∧
      ScalarTopology.IsOpen (fun z => U (infinityChart.backward.eval z)) := by
  constructor
  · intro hU
    exact ⟨fun p q hpq => isOpenOn_invariant hU p q hpq,infinityChart_inverse_continuous U hU⟩
  · rintro ⟨hInv,hOpen⟩
    let D := fun z => U (infinityChart.backward.eval z)
    refine ⟨liftInfinity D,isOpen_liftInfinity D hOpen,?_⟩
    intro p
    have he := hInv (infinityChart.backward.eval (infinityChart.forward.eval p)) p (infinityChart.backward_forward p)
    exact ⟨fun h => ⟨p.property,he.2 h⟩,fun ⟨_,h⟩ => he.1 h⟩

end ComputableAnalysis.RiemannHilbert.SphereTopology
