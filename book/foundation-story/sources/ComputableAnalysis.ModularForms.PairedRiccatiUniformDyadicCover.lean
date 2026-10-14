import ComputableAnalysis.ModularForms.PairedRiccatiFiniteNeighborhoodCover

/-! A common dyadic depth derived from the finite neighborhood cover.
The depth exists; this theorem does not provide an executable selector. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def riccatiCellBound (p q : Scalar) (eps : QPos) (J : QInterval) : Prop :=
  ∃ t : UnitInterval.Point, ∀ u : Rat, J.lo≤u → u≤J.hi → 0≤u → u≤1 →
    Small (sub (pairedEntireRiccatiMap.eval (AffineSegment.point p q u) trivial).val
      (pairedEntireRiccatiMap.eval (RepresentedAffineSegment.point p q t) trivial).val)
      eps.val

theorem riccatiCover_uniform_depth (p q : Scalar) (eps : QPos) (I : QInterval)
    (hI : I.lo≤I.hi) (cover : RiccatiNeighborhoodCover p q eps I) :
    ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n →
      riccatiCellBound p q eps (bisectionInterval I choice n) := by
  induction cover with
  | neighborhood J t bound =>
    refine ⟨0, ?_⟩
    intro choice n hn
    refine ⟨t, ?_⟩
    intro u hl hh hu0 hu1
    have he := bisectionInterval_nested J hI choice 0 n (Nat.zero_le n)
    exact bound u (Rat.le_trans he.1 hl) (Rat.le_trans hh he.2.2) hu0 hu1
  | split J left right ihl ihr =>
    have hl := (bisectInterval_bounds J hI false).2.1
    have hr := (bisectInterval_bounds J hI true).2.1
    obtain ⟨L,hL⟩ := ihl hl
    obtain ⟨R,hR⟩ := ihr hr
    refine ⟨max L R+1, ?_⟩
    intro choice n hn
    have hnpos : 0<n := by omega
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    subst n
    rw [bisectionInterval_shift]
    cases hc : choice 0
    · exact hL (fun k => choice (k+1)) m (by omega)
    · exact hR (fun k => choice (k+1)) m (by omega)

theorem pairedRiccati_uniform_dyadic_cover (p q : Scalar) (W : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val) (eps : QPos) :
    ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n →
      riccatiCellBound p q eps (bisectionInterval ⟨0,1⟩ choice n) :=
  riccatiCover_uniform_depth p q eps ⟨0,1⟩ (by decide +kernel)
    (pairedRiccati_finite_neighborhood_cover p q W hd eps)

theorem riccatiCellBound_pair_variation (p q : Scalar) (eps : QPos) (J : QInterval)
    (hcell : riccatiCellBound p q eps J) (u v : Rat)
    (hu : J.lo≤u ∧ u≤J.hi) (hv : J.lo≤v ∧ v≤J.hi)
    (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) :
    Small (sub (pairedEntireRiccatiMap.eval (AffineSegment.point p q u) trivial).val
      (pairedEntireRiccatiMap.eval (AffineSegment.point p q v) trivial).val) (2*eps.val) := by
  obtain ⟨t,ht⟩ := hcell
  let U := pairedEntireRiccatiMap.eval (AffineSegment.point p q u) trivial
  let V := pairedEntireRiccatiMap.eval (AffineSegment.point p q v) trivial
  let T := pairedEntireRiccatiMap.eval (RepresentedAffineSegment.point p q t) trivial
  have hu' := ht u hu.1 hu.2 hu0 hu1
  have hv' := ht v hv.1 hv.2 hv0 hv1
  have hb := LocalODE.small_add hu' (SeriesLimitLaws.small_neg hv')
  have he : (add (sub U.val T.val) (neg (sub V.val T.val))).Equiv (sub U.val V.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid U.property T.property)
        (neg_valid (sub_valid V.property T.property)))
      (hright := sub_valid U.property V.property)
    let X := ComplexRawQuotient.ofRaw U.val U.property
    let Y := ComplexRawQuotient.ofRaw V.val V.property
    let Z := ComplexRawQuotient.ofRaw T.val T.property
    change (X-Z)+ -(Y-Z)=X-Y
    grind only
  have hb' := Small.congr
    (add_valid (sub_valid U.property T.property) (neg_valid (sub_valid V.property T.property)))
    (sub_valid U.property V.property) he hb
  have hsum : eps.val+eps.val=2*eps.val := by grind only
  rw [hsum] at hb'
  exact hb'

theorem pairedRiccati_uniform_dyadic_variation (p q : Scalar) (W : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val) (eps : QPos) :
    ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n → ∀ u v : Rat,
      (bisectionInterval ⟨0,1⟩ choice n).lo≤u →
      u≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      (bisectionInterval ⟨0,1⟩ choice n).lo≤v →
      v≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      Small (sub (pairedEntireRiccatiMap.eval (AffineSegment.point p q u) trivial).val
        (pairedEntireRiccatiMap.eval (AffineSegment.point p q v) trivial).val) (2*eps.val) := by
  obtain ⟨N,hN⟩ := pairedRiccati_uniform_dyadic_cover p q W hd eps
  refine ⟨N, ?_⟩
  intro choice n hn u v hulo huhi hvlo hvhi
  have he := bisectionInterval_nested (⟨0,1⟩ : QInterval)
    (by decide +kernel) choice 0 n (Nat.zero_le n)
  exact riccatiCellBound_pair_variation p q eps _ (hN choice n hn) u v
    ⟨hulo,huhi⟩ ⟨hvlo,hvhi⟩ (Rat.le_trans he.1 hulo)
    (Rat.le_trans huhi he.2.2) (Rat.le_trans he.1 hvlo) (Rat.le_trans hvhi he.2.2)

end ComputableAnalysis.ModularForms
