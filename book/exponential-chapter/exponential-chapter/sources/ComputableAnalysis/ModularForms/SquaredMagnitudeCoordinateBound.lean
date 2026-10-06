import ComputableAnalysis.ModularForms.NomeExponentHeight
import ComputableAnalysis.ModularForms.ImaginaryIdentity

/-! Coordinate bounds from a justified upper bound on actual squared magnitude. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem persistent_center_lower (z : Scalar) (B L : Rat) (N : Nat)
    (hn : (mul z.val (conj z.val)).realPart.Le (RealRaw.ofRat B))
    (hl : ∀ M, N≤M → L≤QComplex.normSq (z.val.compute M).center) : L≤B := by
  apply Classical.byContradiction
  intro h
  have hgap : 0<L-B := by grind only
  let eps : QPos := ⟨(L-B)/2,by grind only⟩
  have hv := realPart_valid (mul_valid z.property (conj_valid _ z.property))
  obtain ⟨K,hK⟩ := hv.2.2 eps
  let M := max N K
  let p := (z.val.compute M).center
  have hp := QBox.center_mem (valid_ordered z.property M)
  have hc := conjugate_contains z.val M p hp
  have hm := (QBox.mul_contains hp.1 hp.2 hc.1 hc.2).2.1
  have he : (QComplex.mul p (QComplex.conj p)).re=QComplex.normSq p := by
    simp only [QComplex.mul,QComplex.conj,QComplex.normSq]
    grind only
  rw [he] at hm
  change QComplex.normSq p≤((mul z.val (conj z.val)).compute M).hi.re at hm
  have hw := hK M (Nat.le_max_right _ _)
  have hu := hn M 0
  have hb := hl M (Nat.le_max_left _ _)
  change ((mul z.val (conj z.val)).compute M).hi.re-
    ((mul z.val (conj z.val)).compute M).lo.re≤(L-B)/2 at hw
  change ((mul z.val (conj z.val)).compute M).lo.re≤B at hu
  change L≤QComplex.normSq p at hb
  grind only

private theorem square_lower (b x y : Rat) (hb : 0≤b) (hx : b≤x ∨ x≤ -b) :
    b*b≤x*x+y*y := by
  have hy : 0≤y*y := by
    by_cases h : 0≤y
    · exact Rat.mul_nonneg h h
    · have hh : 0≤ -y := by grind only
      have hm := Rat.mul_nonneg hh hh
      grind only
  rcases hx with hx | hx
  · have h := Rat.mul_nonneg (show 0≤x-b by grind only) (show 0≤x+b by grind only)
    grind only
  · have h := Rat.mul_nonneg (show 0≤ -x-b by grind only) (show 0≤ -x+b by grind only)
    grind only

private theorem square_strict (r b : Rat) (hr : 0≤r) (hb : r<b) : r*r<b*b := by
  have h := Rat.mul_pos (show 0<b-r by grind only) (show 0<b+r by grind only)
  grind only

/-- An actual squared-magnitude upper bound implies coordinate bounds for any valid represented complex value. -/
theorem scalar_small_of_squared_magnitude_bound (z : Scalar) (r : Rat) (hr : 0≤r)
    (hn : (mul z.val (conj z.val)).realPart.Le (RealRaw.ofRat (r*r))) : Small z.val r := by
  have hc (N M : Nat) (hNM : N≤M) :=
    QBox.center_mem (valid_ordered z.property M)
  have hnest (N M : Nat) (hNM : N≤M) := z.property.2.1 N M hNM
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    apply Classical.byContradiction
    intro h
    change ¬(-r≤(z.val.compute m).hi.re) at h
    let b := -(z.val.compute m).hi.re
    have hbr : r<b := by grind only
    have hb : 0≤b := by grind only
    have hl : b*b≤r*r := persistent_center_lower z (r*r) (b*b) m hn (by
      intro M hM
      have hp := (hc m M hM).2.1
      have hh := (hnest m M hM).2.1
      apply square_lower b _ _ hb
      right
      change (z.val.compute M).center.re≤ -b
      grind only)
    have hs := square_strict r b hr hbr
    grind only
  · intro n m
    apply Classical.byContradiction
    intro h
    change ¬((z.val.compute n).lo.re≤r) at h
    let b := (z.val.compute n).lo.re
    have hbr : r<b := by grind only
    have hb : 0≤b := by grind only
    have hl : b*b≤r*r := persistent_center_lower z (r*r) (b*b) n hn (by
      intro M hM
      have hp := (hc n M hM).1.1
      have hh := (hnest n M hM).1
      apply square_lower b _ _ hb
      left
      change b≤(z.val.compute M).center.re
      grind only)
    have hs := square_strict r b hr hbr
    grind only
  · intro n m
    apply Classical.byContradiction
    intro h
    change ¬(-r≤(z.val.compute m).hi.im) at h
    let b := -(z.val.compute m).hi.im
    have hbr : r<b := by grind only
    have hb : 0≤b := by grind only
    have hl : b*b≤r*r := persistent_center_lower z (r*r) (b*b) m hn (by
      intro M hM
      have hp := (hc m M hM).2.2
      have hh := (hnest m M hM).2.2.2
      have hs := square_lower b (z.val.compute M).center.im (z.val.compute M).center.re hb (Or.inr (by
        change (z.val.compute M).center.im≤ -b
        grind only))
      unfold QComplex.normSq
      grind only)
    have hs := square_strict r b hr hbr
    grind only
  · intro n m
    apply Classical.byContradiction
    intro h
    change ¬((z.val.compute n).lo.im≤r) at h
    let b := (z.val.compute n).lo.im
    have hbr : r<b := by grind only
    have hb : 0≤b := by grind only
    have hl : b*b≤r*r := persistent_center_lower z (r*r) (b*b) n hn (by
      intro M hM
      have hp := (hc n M hM).1.2
      have hh := (hnest n M hM).2.2.1
      have hs := square_lower b (z.val.compute M).center.im (z.val.compute M).center.re hb (Or.inl (by
        change b≤(z.val.compute M).center.im
        grind only))
      unfold QComplex.normSq
      grind only)
    have hs := square_strict r b hr hbr
    grind only

/-- A justified real height-exponential bound gives a coordinate bound on the actual complex nome. -/
theorem nome_small_of_height_exponential_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r)
    (hb : (entireExponentialValue ⟨ofRealRaw (RealRaw.scaleRat 2 (RealRaw.neg (nomeHeightGrowth z))),
      ofRealRaw_valid _ (RealRaw.scaleRat_valid (RealRaw.neg_valid (nomeHeightGrowth_valid z)))⟩).val.realPart.Le
        (RealRaw.ofRat (r*r))) : Small (nome.eval z hz).val r := by
  apply scalar_small_of_squared_magnitude_bound (nome.eval z hz) r hr
  let e := entireExponentialValue ⟨ofRealRaw (RealRaw.scaleRat 2 (RealRaw.neg (nomeHeightGrowth z))),
    ofRealRaw_valid _ (RealRaw.scaleRat_valid (RealRaw.neg_valid (nomeHeightGrowth_valid z)))⟩
  have he := realPart_equiv (nome_squared_magnitude_height z hz)
  have hn := RealRaw.le_of_equiv
    (realPart_valid (mul_valid (nome.eval z hz).property (conj_valid _ (nome.eval z hz).property)))
    (realPart_valid e.property) he
  exact RealRaw.le_trans (realPart_valid e.property) hn hb

end ComputableAnalysis.ModularForms
