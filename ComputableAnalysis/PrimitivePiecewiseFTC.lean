import ComputableAnalysis.Calculus

/-!
# Piecewise FTC certificates with a separate primitive

The rectangle construction belongs to an integrand `F`; the endpoint identity
belongs to a primitive `P`.  Keeping these two functions separate is essential
for examples such as `|x|`, whose primitive is `x * |x| / 2`.
-/

namespace ComputableAnalysis
namespace Integral

theorem exactRat_evalRaw_equiv (f : Rat -> Rat) (a b x : Rat)
    (hx : inDomainInterval a b x) :
    ((FunctionOnInterval.exactRat f a b).raw.evalRaw x
      ((FunctionOnInterval.exactRat f a b).defined_on x hx)).Equiv
      (RealRaw.ofRat (f x)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    ((FunctionOnInterval.exactRat f a b).raw.evalRaw x
      ((FunctionOnInterval.exactRat f a b).defined_on x hx))
    (RealRaw.ofRat (f x)) n n).2
  change QInterval.Overlaps
    { lo := f x, hi := f x } { lo := f x, hi := f x }
  exact ⟨Rat.le_refl, Rat.le_refl⟩

theorem ofRat_sub_ofRat_equiv (p q : Rat) :
    (RealRaw.ofRat p - RealRaw.ofRat q).Equiv
      (RealRaw.ofRat (p - q)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    (RealRaw.ofRat p - RealRaw.ofRat q)
    (RealRaw.ofRat (p - q)) n n).2
  change QInterval.Overlaps
    { lo := p - q, hi := p - q } { lo := p - q, hi := p - q }
  exact ⟨Rat.le_refl, Rat.le_refl⟩

def piecewisePrimitiveEndpointDifference
    (P : FunctionOnInterval)
    (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (hP : forall i, i <= c.pieces ->
      inDomainInterval P.lower P.upper (c.point i))
    (k : Nat) (hk : k < c.pieces) : RealRaw :=
  P.raw.evalRaw (c.point (k + 1))
      (P.defined_on (c.point (k + 1)) (hP (k + 1) (Nat.succ_le_of_lt hk))) -
    P.raw.evalRaw (c.point k)
      (P.defined_on (c.point k) (hP k (Nat.le_of_lt hk)))

theorem piecewisePrimitiveEndpointDifference_valid
    (P F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (hP : forall i, i <= c.pieces ->
      inDomainInterval P.lower P.upper (c.point i))
    (k : Nat) (hk : k < c.pieces) :
    (piecewisePrimitiveEndpointDifference P F c hP k hk).Valid := by
  let hx := hP k (Nat.le_of_lt hk)
  let hy := hP (k + 1) (Nat.succ_le_of_lt hk)
  let x := P.raw.evalRaw (c.point k) (P.defined_on _ hx)
  let y := P.raw.evalRaw (c.point (k + 1)) (P.defined_on _ hy)
  have hvalidx : x.Valid := by
    simpa [x, RealRaw.Valid, PartialRealFunRaw.evalRaw] using
      P.valid_on _ (P.defined_on _ hx)
  have hvalidy : y.Valid := by
    simpa [y, RealRaw.Valid, PartialRealFunRaw.evalRaw] using
      P.valid_on _ (P.defined_on _ hy)
  simpa [piecewisePrimitiveEndpointDifference, x, y, hx, hy] using
    RealRaw.sub_valid hvalidy hvalidx

def piecewisePrimitiveEndpointDifferenceList
    (P F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (hP : forall i, i <= c.pieces ->
      inDomainInterval P.lower P.upper (c.point i)) : List RealRaw :=
  (List.range c.pieces).map (fun k =>
    if hk : k < c.pieces then
      piecewisePrimitiveEndpointDifference P F c hP k hk
    else RealRaw.zero)

def piecewisePrimitiveTotalEndpointDifference
    (P F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (hP : forall i, i <= c.pieces ->
      inDomainInterval P.lower P.upper (c.point i)) : RealRaw :=
  P.raw.evalRaw (c.point c.pieces)
      (P.defined_on _ (hP c.pieces (Nat.le_refl _))) -
    P.raw.evalRaw (c.point 0)
      (P.defined_on _ (hP 0 (Nat.zero_le _)))

theorem piecewisePrimitiveTotalEndpointDifference_valid
    (P F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (hP : forall i, i <= c.pieces ->
      inDomainInterval P.lower P.upper (c.point i)) :
    (piecewisePrimitiveTotalEndpointDifference P F c hP).Valid := by
  let hx := hP 0 (Nat.zero_le _)
  let hy := hP c.pieces (Nat.le_refl _)
  let x := P.raw.evalRaw (c.point 0) (P.defined_on _ hx)
  let y := P.raw.evalRaw (c.point c.pieces) (P.defined_on _ hy)
  have hvalidx : x.Valid := by
    simpa [x, RealRaw.Valid, PartialRealFunRaw.evalRaw] using
      P.valid_on _ (P.defined_on _ hx)
  have hvalidy : y.Valid := by
    simpa [y, RealRaw.Valid, PartialRealFunRaw.evalRaw] using
      P.valid_on _ (P.defined_on _ hy)
  simpa [piecewisePrimitiveTotalEndpointDifference, x, y, hx, hy] using
    RealRaw.sub_valid hvalidy hvalidx

/-!
The finite proof is the same transport/telescope argument as the integrand
endpoint API, but its endpoint lists are evaluated by `P` rather than `F`.
All representation changes are explicit premises.
-/
theorem piecewiseMonotoneIntegralFor_equiv_totalPrimitiveEndpointDifference_of_telescope
    (P F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (hP : forall i, i <= c.pieces ->
      inDomainInterval P.lower P.upper (c.point i))
    (hcell : forall k (hk : k < c.pieces),
      (piecewiseMonotoneCellIntegral F c k hk).Equiv
        (piecewisePrimitiveEndpointDifference P F c hP k hk))
    {first : RealRaw} {rest : List RealRaw}
    (hvalues : forall x, x ∈ first :: rest -> x.Valid)
    (htransport :
      FiniteRawListEquiv
        (piecewisePrimitiveEndpointDifferenceList P F c hP)
        (rawAdjacentDifferenceList (first :: rest)))
    (htotal : (rawLast first rest - first).Equiv
      (piecewisePrimitiveTotalEndpointDifference P F c hP)) :
    (piecewiseMonotoneIntegralFor F c).Equiv
      (piecewisePrimitiveTotalEndpointDifference P F c hP) := by
  let cell : Nat -> RealRaw := fun k =>
    if hk : k < c.pieces then piecewiseMonotoneCellIntegral F c k hk
    else RealRaw.zero
  let endpoint : Nat -> RealRaw := fun k =>
    if hk : k < c.pieces then
      piecewisePrimitiveEndpointDifference P F c hP k hk
    else RealRaw.zero
  have hlist_aux : forall (xs : List Nat),
      (forall k, k ∈ xs -> k < c.pieces) ->
      FiniteRawListEquiv (xs.map cell) (xs.map endpoint) := by
    intro xs
    induction xs with
    | nil => intro _; exact .nil
    | cons k ks ih =>
        intro hxs
        have hk : k < c.pieces := hxs k (by simp)
        have htail : forall j, j ∈ ks -> j < c.pieces := by
          intro j hj
          exact hxs j (by simp [hj])
        apply FiniteRawListEquiv.cons
        · simp [cell, endpoint, hk]
          exact hcell k hk
        · exact ih htail
  have hlist := hlist_aux (List.range c.pieces)
    (by intro k hk; exact List.mem_range.1 hk)
  have hendpoint : forall x,
      x ∈ piecewisePrimitiveEndpointDifferenceList P F c hP -> x.Valid := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨k, hk, rfl⟩
    have hk' : k < c.pieces := List.mem_range.1 hk
    simp [piecewisePrimitiveEndpointDifferenceList, hk']
    exact piecewisePrimitiveEndpointDifference_valid P F c hP k hk'
  have hcell_valid : forall x,
      x ∈ (List.range c.pieces).map cell -> x.Valid := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨k, hk, rfl⟩
    simp [cell, List.mem_range.1 hk]
    exact piecewiseMonotoneCellIntegral_valid F c k (List.mem_range.1 hk)
  have hsum := finiteRawSum_equiv_of_forall hlist hcell_valid hendpoint
  have hintegral := piecewiseMonotoneIntegralFor_equiv_finiteRawSum F c
  have hintegral_endpoint := RealRaw.equiv_trans
    (piecewiseMonotoneIntegralFor_valid F c)
    (finiteRawSum_valid _ hcell_valid)
    (finiteRawSum_valid _ hendpoint) hintegral hsum
  have hadjacent : forall x,
      x ∈ rawAdjacentDifferenceList (first :: rest) -> x.Valid :=
    rawAdjacentDifferenceList_valid hvalues
  have htransport_sum := finiteRawSum_equiv_of_forall
    htransport hendpoint hadjacent
  have htel := finiteRawSum_rawAdjacentDifferenceList_equiv_last_sub_first
    hvalues
  have hlast := rawLast_valid hvalues
  have hfirst : first.Valid := hvalues first (by simp)
  have hsub : (rawLast first rest - first).Valid :=
    RealRaw.sub_valid hlast hfirst
  have hintegral_adjacent := RealRaw.equiv_trans
    (piecewiseMonotoneIntegralFor_valid F c)
    (finiteRawSum_valid _ hendpoint)
    (finiteRawSum_valid _ hadjacent) hintegral_endpoint htransport_sum
  have hintegral_last := RealRaw.equiv_trans
    (piecewiseMonotoneIntegralFor_valid F c)
    (finiteRawSum_valid _ hadjacent) hsub hintegral_adjacent htel
  exact RealRaw.equiv_trans
    (piecewiseMonotoneIntegralFor_valid F c) hsub
    (piecewisePrimitiveTotalEndpointDifference_valid P F c hP)
    hintegral_last htotal

end Integral
end ComputableAnalysis
