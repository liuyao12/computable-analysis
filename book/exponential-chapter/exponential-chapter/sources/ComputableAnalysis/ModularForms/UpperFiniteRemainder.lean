import ComputableAnalysis.ModularForms.UpperFiniteDerivative

/-! Exact decomposition of finite lattice-map remainders into point remainders. -/
namespace ComputableAnalysis.ModularForms
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def upperPointRemainder (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (u : QuadraticOrder163) : ComplexRaw :=
  remainder (upperPointMap k u) a ha ((upperPointMap_holomorphic k u).derivative a ha) z hz

theorem upperPointRemainder_valid (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (u : QuadraticOrder163) :
    (upperPointRemainder a ha z hz k u).Valid := DomainFunctions.remainder_valid _ _ _ _ _ _

private theorem remainderList_valid (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (us : List QuadraticOrder163) :
    ∀ t ∈ us.map (upperPointRemainder a ha z hz k), t.Valid := by
  intro t ht
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
  exact upperPointRemainder_valid a ha z hz k u

theorem upperFiniteMap_remainder_sum (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat) (us : List QuadraticOrder163) :
    (remainder (upperFiniteMap k us) a ha ((upperFiniteMap_holomorphic k us).derivative a ha) z hz).Equiv
      (LocalODE.sum (us.map (upperPointRemainder a ha z hz k))) := by
  induction us with
  | nil =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := DomainFunctions.remainder_valid _ _ _ _ _ _) (hright := ofQComplex_valid _)
    change (0 + -0) + -(0*(ComplexRawQuotient.ofRaw z.val z.property +
      -ComplexRawQuotient.ofRaw a.val a.property)) = 0
    grind only
  | cons u us ih =>
    have he := sum_remainder (upperPointMap k u) (upperFiniteMap k us) (fun _ hz => hz)
      a ha ((upperPointMap_holomorphic k u).derivative a ha)
      ((upperFiniteMap_holomorphic k us).derivative a ha) z hz
    have ht : (remainder (upperFiniteMap k (u::us)) a ha
        ((upperFiniteMap_holomorphic k (u::us)).derivative a ha) z hz).Equiv
        (remainder (sumOn (upperPointMap k u) (upperFiniteMap k us) (fun _ hz => hz)) a ha
          (scalarSum ((upperPointMap_holomorphic k u).derivative a ha)
            ((upperFiniteMap_holomorphic k us).derivative a ha)) z hz) := by
      exact equiv_refl _ (DomainFunctions.remainder_valid _ _ _ _ _ _)
    exact equiv_trans (DomainFunctions.remainder_valid _ _ _ _ _ _) (DomainFunctions.remainder_valid _ _ _ _ _ _)
      (LocalODE.sum_valid _ (remainderList_valid a ha z hz k (u::us))) ht
      (equiv_trans (DomainFunctions.remainder_valid _ _ _ _ _ _)
        (add_valid (upperPointRemainder_valid a ha z hz k u) (DomainFunctions.remainder_valid _ _ _ _ _ _))
        (LocalODE.sum_valid _ (remainderList_valid a ha z hz k (u::us))) he
        (add_equiv (equiv_refl _ (upperPointRemainder_valid a ha z hz k u)) ih))

end ComputableAnalysis.ModularForms
