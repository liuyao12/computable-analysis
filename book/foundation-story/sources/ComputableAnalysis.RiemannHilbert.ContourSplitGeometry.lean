import ComputableAnalysis.RiemannHilbert.ContourContinuousEdgeInvariance

/-! Literal interval cuts and exact concatenation when the rational meshes
align. The alignment data are constructed beneath the later public law. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

def splitIntervalLeft (I : QInterval) (c : Rat) : QInterval := ⟨I.lo,c⟩
def splitIntervalRight (I : QInterval) (c : Rat) : QInterval := ⟨c,I.hi⟩

theorem splitIntervalLeft_contains (I : QInterval) (c t : Rat) (hc : c≤I.hi)
    (ht : (splitIntervalLeft I c).lo≤t ∧ t≤(splitIntervalLeft I c).hi) : I.lo≤t ∧ t≤I.hi :=
  ⟨ht.1,Rat.le_trans ht.2 hc⟩

theorem splitIntervalRight_contains (I : QInterval) (c t : Rat) (hc : I.lo≤c)
    (ht : (splitIntervalRight I c).lo≤t ∧ t≤(splitIntervalRight I c).hi) : I.lo≤t ∧ t≤I.hi :=
  ⟨Rat.le_trans hc ht.1,ht.2⟩

theorem intervalGridSplit_left_tag (I : QInterval) (c : Rat) (L R j : Nat)
    (hs : intervalGridStep I (L+R)=intervalGridStep (splitIntervalLeft I c) L) :
    intervalGridTag I (L+R) j=intervalGridTag (splitIntervalLeft I c) L j := by
  change I.lo+((j:Rat)+1/2)*intervalGridStep I (L+R)=
    I.lo+((j:Rat)+1/2)*intervalGridStep (splitIntervalLeft I c) L
  rw [hs]

theorem intervalGridSplit_right_tag (I : QInterval) (c : Rat) (L R j : Nat)
    (hs : intervalGridStep I (L+R)=intervalGridStep (splitIntervalRight I c) R)
    (hcut : I.lo+(L:Rat)*intervalGridStep I (L+R)=c) :
    intervalGridTag I (L+R) (L+j)=intervalGridTag (splitIntervalRight I c) R j := by
  change I.lo+(((L+j:Nat):Rat)+1/2)*intervalGridStep I (L+R)=
    c+((j:Rat)+1/2)*intervalGridStep (splitIntervalRight I c) R
  rw [Rat.natCast_add,←hs]
  grind only

theorem intervalGridPrefix_split_aligned (sample : Rat → Scalar) (I : QInterval) (c : Rat) (L R : Nat)
    (hL : intervalGridStep I (L+R)=intervalGridStep (splitIntervalLeft I c) L)
    (hR : intervalGridStep I (L+R)=intervalGridStep (splitIntervalRight I c) R)
    (hcut : I.lo+(L:Rat)*intervalGridStep I (L+R)=c) :
    intervalGridPrefix sample I (L+R) ≈ scalarSum
      (intervalGridPrefix sample (splitIntervalLeft I c) L)
      (intervalGridPrefix sample (splitIntervalRight I c) R) := by
  let term := fun j => scale (intervalGridStep I (L+R)) (sample (intervalGridTag I (L+R) j))
  have hl : gridScalarSum L term ≈ intervalGridPrefix sample (splitIntervalLeft I c) L := by
    apply gridScalarSum_congr L
    intro j
    dsimp [term]
    rw [intervalGridSplit_left_tag I c L R j hL,hL]
    exact equiv_refl _ (scale _ _).property
  have hr : gridScalarSum R (fun j => term (L+j)) ≈ intervalGridPrefix sample (splitIntervalRight I c) R := by
    apply gridScalarSum_congr R
    intro j
    dsimp [term]
    rw [intervalGridSplit_right_tag I c L R j hR hcut,hR]
    exact equiv_refl _ (scale _ _).property
  exact Setoid.trans (gridScalarSum_concat term L R) (add_equiv hl hr)

end ComputableAnalysis.RiemannHilbert.RectangularContour
