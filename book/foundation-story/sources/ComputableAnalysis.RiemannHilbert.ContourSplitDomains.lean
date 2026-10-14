import ComputableAnalysis.RiemannHilbert.ContourIntervalSplit

/-! Whole-edge domain evidence restricts to every closed rational subedge.
The local sampler agrees with the shared whole-edge sampler on that subedge. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem representedRectangle_subrectangle (J K : QInterval × QInterval) (z : Scalar)
    (hxl : J.1.lo≤K.1.lo) (hxu : K.1.hi≤J.1.hi) (hyl : J.2.lo≤K.2.lo) (hyu : K.2.hi≤J.2.hi)
    (hz : representedRectangleContains K z) : representedRectangleContains J z :=
  ⟨fun n m => Rat.le_trans hxl (hz.1 n m),fun n m => Rat.le_trans (hz.2.1 n m) hxu,
    fun n m => Rat.le_trans hyl (hz.2.2.1 n m),fun n m => Rat.le_trans (hz.2.2.2 n m) hyu⟩

theorem intervalGridCell_contains_initial (I : QInterval) (M j : Nat) (hI : I.lo≤I.hi)
    (hM : 0<M) (hj : j<M) (t : Rat)
    (ht : (intervalGridCell I M j).lo≤t ∧ t≤(intervalGridCell I M j).hi) : I.lo≤t ∧ t≤I.hi := by
  have hp : rationalRectangleContains (rectangleGridCell (horizontalIntervalRectangle I 0) M j 0) ⟨t,0⟩ := by
    rw [horizontalIntervalRectangle_cell]
    exact ⟨ht.1,ht.2,Rat.le_refl,Rat.le_refl⟩
  have hb := rectangleGridCell_contains_initial (horizontalIntervalRectangle I 0) M j 0 hM hj hM
    hI Rat.le_refl ⟨t,0⟩ hp
  exact ⟨hb.1,hb.2.1⟩

theorem intervalGridTag_mem_interval (I : QInterval) (M j : Nat) (hI : I.lo≤I.hi)
    (hM : 0<M) (hj : j<M) : I.lo≤intervalGridTag I M j ∧ intervalGridTag I M j≤I.hi :=
  intervalGridCell_contains_initial I M j hI hM hj _ (intervalGridTag_mem_cell I M j hI hM)

theorem intervalCellOscillation_congr (f g : Rat → Scalar) (I : QInterval) (hI : I.lo≤I.hi)
    (he : ∀ t : Rat, I.lo≤t ∧ t≤I.hi → f t ≈ g t) (hf : intervalCellOscillation f I) :
    intervalCellOscillation g I := by
  intro eps
  obtain ⟨N,hN⟩ := hf eps
  refine ⟨N, ?_⟩
  intro n hn j hj p q hp hq
  exact Small.congr (sub_valid (f q).property (f p).property) (sub_valid (g q).property (g p).property)
    (FunctionTheory.sub_congr
      (he q (intervalGridCell_contains_initial I (2^n) j hI (Nat.two_pow_pos n) hj q hq))
      (he p (intervalGridCell_contains_initial I (2^n) j hI (Nat.two_pow_pos n) hj p hp)))
    (hN n hn j hj p q hp hq)

theorem horizontalInterval_subdomain (f : DomainFunctions.Map) (I K : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (hlo : I.lo≤K.lo) (hhi : K.hi≤I.hi) :
    ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle K y) z → f.domain z :=
  fun z hz => hf z (representedRectangle_subrectangle (horizontalIntervalRectangle I y) (horizontalIntervalRectangle K y)
    z hlo hhi Rat.le_refl Rat.le_refl hz)

theorem verticalInterval_subdomain (f : DomainFunctions.Map) (I K : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (hlo : I.lo≤K.lo) (hhi : K.hi≤I.hi) :
    ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle K x) z → f.domain z :=
  fun z hz => hf z (representedRectangle_subrectangle (verticalIntervalRectangle I x) (verticalIntervalRectangle K x)
    z Rat.le_refl Rat.le_refl hlo hhi hz)

theorem horizontalIntervalSample_subinterval (f : DomainFunctions.Map) (I K : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (hk : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle K y) z → f.domain z)
    (hlo : I.lo≤K.lo) (hhi : K.hi≤I.hi) (t : Rat) (ht : K.lo≤t ∧ t≤K.hi) :
    horizontalIntervalSample f K y hk t ≈ horizontalIntervalSample f I y hf t := by
  have hp : rationalRectangleContains (horizontalIntervalRectangle K y) ⟨t,y⟩ :=
    ⟨ht.1,ht.2,Rat.le_refl,Rat.le_refl⟩
  have hq : rationalRectangleContains (horizontalIntervalRectangle I y) ⟨t,y⟩ :=
    ⟨Rat.le_trans hlo ht.1,Rat.le_trans ht.2 hhi,Rat.le_refl,Rat.le_refl⟩
  let z := rationalRectangleScalar (⟨t,y⟩ : QComplex)
  have hd := hk z (rationalRectangle_represented_mem _ _ hp)
  exact Setoid.trans (continuousRectangleSample_agreement f _ hk _ hp hd)
    (Setoid.symm (continuousRectangleSample_agreement f _ hf _ hq hd))

theorem verticalIntervalSample_subinterval (f : DomainFunctions.Map) (I K : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (hk : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle K x) z → f.domain z)
    (hlo : I.lo≤K.lo) (hhi : K.hi≤I.hi) (t : Rat) (ht : K.lo≤t ∧ t≤K.hi) :
    verticalIntervalSample f K x hk t ≈ verticalIntervalSample f I x hf t := by
  have hp : rationalRectangleContains (verticalIntervalRectangle K x) ⟨x,t⟩ :=
    ⟨Rat.le_refl,Rat.le_refl,ht.1,ht.2⟩
  have hq : rationalRectangleContains (verticalIntervalRectangle I x) ⟨x,t⟩ :=
    ⟨Rat.le_refl,Rat.le_refl,Rat.le_trans hlo ht.1,Rat.le_trans ht.2 hhi⟩
  let z := rationalRectangleScalar (⟨x,t⟩ : QComplex)
  have hd := hk z (rationalRectangle_represented_mem _ _ hp)
  exact Setoid.trans (continuousRectangleSample_agreement f _ hk _ hp hd)
    (Setoid.symm (continuousRectangleSample_agreement f _ hf _ hq hd))

theorem horizontalIntervalSample_subinterval_oscillation (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (I K : QInterval) (y : Rat) (hK : K.lo≤K.hi)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (hlo : I.lo≤K.lo) (hhi : K.hi≤I.hi) : intervalCellOscillation (horizontalIntervalSample f I y hf) K := by
  let hk := horizontalInterval_subdomain f I K y hf hlo hhi
  exact intervalCellOscillation_congr _ _ K hK
    (horizontalIntervalSample_subinterval f I K y hf hk hlo hhi)
    (horizontalIntervalSample_oscillation f hc K y hK hk)

theorem verticalIntervalSample_subinterval_oscillation (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (I K : QInterval) (x : Rat) (hK : K.lo≤K.hi)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (hlo : I.lo≤K.lo) (hhi : K.hi≤I.hi) : intervalCellOscillation (verticalIntervalSample f I x hf) K := by
  let hk := verticalInterval_subdomain f I K x hf hlo hhi
  exact intervalCellOscillation_congr _ _ K hK
    (verticalIntervalSample_subinterval f I K x hf hk hlo hhi)
    (verticalIntervalSample_oscillation f hc K x hK hk)

end ComputableAnalysis.RiemannHilbert.RectangularContour
