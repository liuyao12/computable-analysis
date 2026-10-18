import ComputableAnalysis.CartesianDiracTestDensity

/-! The ORIGINAL closed compact-test Dirac relation is single-valued on
Cartesian norm classes. Test density, pairing continuity and Hermitian
symmetry are proved constructions, not additional operator assumptions. -/
namespace ComputableAnalysis.CartesianDiracActionUnique
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
open ComputableCoefficient QuotientBridge
open CartesianSpinorCauchyFamily (Family Equivalent budget)
open CartesianSpinorCauchyPairing (squaredDistance)
open CartesianSpinorComplexPairing (value)
set_option autoImplicit false
set_option maxHeartbeats 3000000
local instance : Lean.Grind.CommRing ComplexRawQuotient.Value := ComplexRawQuotient.instCommRingValue
local instance (n : Nat) : OfNat ComplexRawQuotient.Value n :=
  (inferInstance : Lean.Grind.CommRing ComplexRawQuotient.Value).ofNat n

private theorem self_difference (z : Scalar) : Small (sub z.val z.val) 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    have h := (valid_ordered z.property j).1
    change (0:Rat)≤(z.val.compute j).hi.re+ -(z.val.compute j).lo.re
    grind only
  · intro i j
    have h := (valid_ordered z.property i).1
    change (z.val.compute i).lo.re+ -(z.val.compute i).hi.re≤(0:Rat)
    grind only
  · intro i j
    have h := (valid_ordered z.property j).2
    change (0:Rat)≤(z.val.compute j).hi.im+ -(z.val.compute j).lo.im
    grind only
  · intro i j
    have h := (valid_ordered z.property i).2
    change (z.val.compute i).lo.im+ -(z.val.compute i).hi.im≤(0:Rat)
    grind only

/-- Equality against every actual Cartesian state separates norm classes.
The proof uses the constructed real coordinate and actual squared-distance
identity, rather than assuming nondegeneracy of an abstract inner product. -/
theorem pairing_separates (F G : Family)
    (h : ∀ X : Family,(value F X).val.Equiv (value G X).val) : Equivalent F G := by
  have real_eq (X : Family) :
      (CartesianSpinorCauchyPairing.value F X).real.preferred.Equiv
        (CartesianSpinorCauchyPairing.value G X).real.preferred := by
    have hF := CartesianSpinorHermitianGram.real_coordinate F X
    have hG := CartesianSpinorHermitianGram.real_coordinate G X
    exact RealRaw.equiv_trans (CartesianSpinorCauchyPairing.value F X).real.valid
      (realPart_valid (value F X).property) (CartesianSpinorCauchyPairing.value G X).real.valid
      (RealRaw.equiv_symm hF)
      (RealRaw.equiv_trans (realPart_valid (value F X).property)
        (realPart_valid (value G X).property) (CartesianSpinorCauchyPairing.value G X).real.valid
        (realPart_equiv (h X)) hG)
  apply CartesianSpinorCauchyNullNorm.zero_distance_equivalent
  have hd := quotient_eq (CartesianSpinorPairingAlgebra.squaredDistance F G)
  have hF := quotient_eq (real_eq F)
  have hG := quotient_eq (real_eq G)
  have hs := quotient_eq (CartesianSpinorPairingAlgebra.symm G F)
  apply raw_equiv_of_quotient_eq (y:=Value.rational 0)
  simp only [CartesianSpinorCauchyPairing.squaredNorm,quotient_add,quotient_sub] at hd hF hG ⊢
  change quotient (squaredDistance F G)=0
  grind only

/-- Tests computed by the existing density algorithm already determine every
complex pairing. The complete approximation errors tend to zero for arbitrary
independent represented Cartesian states. -/
theorem test_pairings_extend (F G : Family)
    (h : ∀ ts : List CartesianCutoffTestGraph.Test,
      (value F (CartesianCutoffTestGraph.sources ts)).val.Equiv
        (value G (CartesianCutoffTestGraph.sources ts)).val) (X : Family) :
    (value F X).val.Equiv (value G X).val := by
  let eps : Nat→QPos := fun n => ⟨RawLimit.allowance n,RawLimit.allowance_pos n⟩
  let T := fun n => CartesianDiracTestDensity.source X (eps n)
  let r := fun n => (budget F+budget X+1)*RawLimit.allowance n
  let s := fun n => (budget G+budget X+1)*RawLimit.allowance n
  have hKF : 0≤budget F+budget X+1 := by
    have hF:=CartesianSpinorCauchyFamily.budget_positive F
    have hX:=CartesianSpinorCauchyFamily.budget_positive X
    grind only
  have hKG : 0≤budget G+budget X+1 := by
    have hG:=CartesianSpinorCauchyFamily.budget_positive G
    have hX:=CartesianSpinorCauchyFamily.budget_positive X
    grind only
  have hError (Y : Family) (n : Nat) :
      Small (sub (value Y X).val (value Y (T n)).val)
        ((budget Y+budget X+1)*RawLimit.allowance n) := by
    have hOne : (eps n).val≤1 := by
      have hh := RawLimit.allowance_antitone (Nat.zero_le n)
      simpa only [eps,RawLimit.allowance,Rat.pow_zero] using hh
    exact RepresentedCauchySum.small_sub_symm _ _ _
      (CartesianCutoffGraphClosure.pairing_error Y X Y (T n) (eps n).val
        (Rat.le_of_lt (eps n).property) hOne
        (CartesianCutoffGraphClosure.self_distance Y (eps n))
        (CartesianDiracTestDensity.approximation X (eps n)))
  apply RepresentedCauchyComparison.compare (value F X) (value G X)
    (fun n => value F (T n)) (fun n => value G (T n)) r s (fun _ => 0)
    (SeriesLimitLaws.shrinks_scale _ RawLimit.allowance_shrinks _ hKF)
    (SeriesLimitLaws.shrinks_scale _ RawLimit.allowance_shrinks _ hKG)
    (fun e => ⟨0,fun _ _ => Rat.le_of_lt e.property⟩)
    (hError F) (hError G)
  intro n
  have he := h (CartesianDiracTestDensity.tests X (eps n))
  exact Small.congr (sub_valid (value G (T n)).property (value G (T n)).property)
    (sub_valid (value F (T n)).property (value G (T n)).property)
    (FunctionTheory.sub_congr (equiv_symm he) (equiv_refl _ (value G (T n)).property))
    (self_difference (value G (T n)))

/-- The actual finite smooth compact-test sources separate all completed
Cartesian states; no density or separation premise is added. -/
theorem test_pairings_separate (F G : Family)
    (h : ∀ ts : List CartesianCutoffTestGraph.Test,
      (value F (CartesianCutoffTestGraph.sources ts)).val.Equiv
        (value G (CartesianCutoffTestGraph.sources ts)).val) : Equivalent F G :=
  pairing_separates F G (test_pairings_extend F G h)

/-- Single-valuedness of the ORIGINAL norm-closed Dirac relation, for every
represented real Coulomb coefficient. No small-coupling cap is needed here. -/
theorem action_unique (alpha : Value) {F G H : Family}
    (hFG : CartesianCutoffGraphClosure.InGraph alpha F G)
    (hFH : CartesianCutoffGraphClosure.InGraph alpha F H) : Equivalent G H := by
  apply test_pairings_separate G H
  intro ts
  have ht := CartesianCutoffGraphClosure.of_test_graph alpha (CartesianCutoffTestGraph.of_tests alpha ts)
  have hG := CartesianCutoffGraphClosure.symmetry alpha hFG ht
  have hH := CartesianCutoffGraphClosure.symmetry alpha hFH ht
  exact equiv_trans (value G (CartesianCutoffTestGraph.sources ts)).property
    (value F (CartesianCutoffTestGraph.actions alpha ts)).property
    (value H (CartesianCutoffTestGraph.sources ts)).property hG (equiv_symm hH)

/-- Independent source and action representations describe the same operator
value whenever their source norm classes agree. -/
theorem equivalent_sources (alpha : Value) {F G H J : Family}
    (hFG : CartesianCutoffGraphClosure.InGraph alpha F G)
    (hHJ : CartesianCutoffGraphClosure.InGraph alpha H J) (hFH : Equivalent F H) : Equivalent G J :=
  action_unique alpha hFG (CartesianCutoffGraphClosure.names alpha hHJ
    (CartesianSpinorCauchyFamily.equivalent_symm hFH) (CartesianSpinorCauchyFamily.equivalent_refl J))

/-- The finite compact-test action also has the unique closed-graph value. -/
theorem test_action_unique (alpha : Value) (ts : List CartesianCutoffTestGraph.Test) {G : Family}
    (hG : CartesianCutoffGraphClosure.InGraph alpha (CartesianCutoffTestGraph.sources ts) G) :
    Equivalent G (CartesianCutoffTestGraph.actions alpha ts) :=
  action_unique alpha hG
    (CartesianCutoffGraphClosure.of_test_graph alpha (CartesianCutoffTestGraph.of_tests alpha ts))

/-- The literal empty finite test list supplies the zero graph pair. -/
theorem zero_in_graph (alpha : Value) :
    CartesianCutoffGraphClosure.InGraph alpha (CartesianSpinorCauchyFamily.constant [])
      (CartesianSpinorCauchyFamily.constant []) :=
  CartesianCutoffGraphClosure.of_test_graph alpha (CartesianCutoffTestGraph.of_tests alpha [])

/-- The original closed graph has no multivalued part at zero. -/
theorem zero_action (alpha : Value) {G : Family}
    (h : CartesianCutoffGraphClosure.InGraph alpha (CartesianSpinorCauchyFamily.constant []) G) :
    Equivalent G (CartesianSpinorCauchyFamily.constant []) := action_unique alpha h (zero_in_graph alpha)

/-- Closability of the actual original finite test action. If test sources
tend to zero and their actions converge, the action limit is zero. Both
convergences have supplied genuine norm errors and complete shrinking tails. -/
theorem closable (alpha : Value) (u v : Nat→Family) (G : Family) (r : Nat→Rat)
    (hr : ∀ n,0≤r n) (hShrink : ShrinksToZero r)
    (hGraph : ∀ n,CartesianCutoffTestGraph.InGraph alpha (u n) (v n))
    (hZero : ∀ n,(squaredDistance (u n) (CartesianSpinorCauchyFamily.constant [])).real.preferred.Le
      (RealRaw.ofRat (r n*r n)))
    (hG : ∀ n,(squaredDistance (v n) G).real.preferred.Le (RealRaw.ofRat (r n*r n))) :
    Equivalent G (CartesianSpinorCauchyFamily.constant []) :=
  zero_action alpha (CartesianCutoffGraphClosure.closed alpha _ G u v r hr hShrink
    (fun n => CartesianCutoffGraphClosure.of_test_graph alpha (hGraph n)) hZero hG)

end ComputableAnalysis.CartesianDiracActionUnique
