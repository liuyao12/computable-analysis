import ComputableAnalysis.RiemannHilbert.ScalarTopology

/-! The closed unit interval contains arbitrary valid real interval names.
Its order bounds concern represented values, rather than all endpoints of
an early approximation box. All constructors below are executable. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory

structure Point where
  value : RealRaw
  valid : value.Valid
  lower : (RealRaw.ofRat 0).Le value
  upper : value.Le (RealRaw.ofRat 1)

instance : Setoid Point where
  r s t := s.value.Equiv t.value
  iseqv := ⟨fun t => RealRaw.equiv_refl t.value t.valid,
    fun h => RealRaw.equiv_symm h,
    fun {s t u} h k => RealRaw.equiv_trans s.valid t.valid u.valid h k⟩

def scalar (t : Point) : Scalar := ⟨ofRealRaw t.value,ofRealRaw_valid t.value t.valid⟩

theorem scalar_congr {s t : Point} (h : s ≈ t) : scalar s ≈ scalar t :=
  ofRealRaw_equiv_of_equiv s.valid t.valid h

theorem scalar_reflects {s t : Point} (h : scalar s ≈ scalar t) : s ≈ t := by
  intro n
  have hn := (compareAt_overlap_iff (scalar s).val (scalar t).val n n).1 (h n)
  exact (RealRaw.compareAt_overlap_iff s.value t.value n n).2 ⟨hn.1.1,hn.2.1⟩

theorem scalar_small (t : Point) : Small (scalar t).val 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    have h := t.lower 0 m
    change 0 ≤ (t.value.compute m).hi at h
    change -1 ≤ (t.value.compute m).hi
    grind only
  · intro n m
    exact t.upper n m
  · intro n m
    change (-1 : Rat) ≤ 0
    decide +kernel
  · intro n m
    change (0 : Rat) ≤ 1
    decide +kernel

def rational (q : Rat) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Point where
  value := RealRaw.ofRat q
  valid := RealRaw.ofRat_valid q
  lower _ _ := h0
  upper _ _ := h1

def zero : Point := rational 0 (by decide +kernel) (by decide +kernel)
def one : Point := rational 1 (by decide +kernel) (by decide +kernel)

theorem scalar_rational (q : Rat) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (scalar (rational q h0 h1)).val.Equiv (ofQComplex (QComplex.ofRat q)) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  change (q ≤ q ∧ (0 : Rat) ≤ 0) ∧ (q ≤ q ∧ (0 : Rat) ≤ 0)
  exact ⟨⟨Rat.le_refl,Rat.le_refl⟩,⟨Rat.le_refl,Rat.le_refl⟩⟩

def reverse (t : Point) : Point where
  value := RealRaw.sub (RealRaw.ofRat 1) t.value
  valid := RealRaw.sub_valid (RealRaw.ofRat_valid 1) t.valid
  lower n m := by
    have h := t.upper m 0
    change (t.value.compute m).lo ≤ 1 at h
    change 0 ≤ 1-(t.value.compute m).lo
    grind only
  upper n m := by
    have h := t.lower 0 n
    change 0 ≤ (t.value.compute n).hi at h
    change 1-(t.value.compute n).hi ≤ 1
    grind only

theorem reverse_congr {s t : Point} (h : s ≈ t) : reverse s ≈ reverse t :=
  RealRaw.sub_equiv (RealRaw.ofRat_valid 1) (RealRaw.ofRat_valid 1) s.valid t.valid
    (RealRaw.equiv_refl (RealRaw.ofRat 1) (RealRaw.ofRat_valid 1)) h

theorem reverse_zero : reverse zero ≈ one := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change 1-0 ≤ 1 ∧ 1 ≤ 1-0
  decide +kernel

theorem reverse_one : reverse one ≈ zero := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change 1-1 ≤ 0 ∧ 0 ≤ 1-1
  decide +kernel

theorem reverse_rational (r : Rat) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    reverse (rational r h0 h1) ≈ rational (1-r) (by grind only) (by grind only) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change 1-r ≤ 1-r ∧ 1-r ≤ 1-r
  exact ⟨Rat.le_refl,Rat.le_refl⟩

theorem reverse_reverse (t : Point) : reverse (reverse t) ≈ t := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change 1-(1-(t.value.compute n).lo) ≤ (t.value.compute n).hi ∧
    (t.value.compute n).lo ≤ 1-(1-(t.value.compute n).hi)
  have h := RealRaw.interval_order_of_valid t.value t.valid n
  grind only

theorem scalar_reverse (t : Point) : (scalar (reverse t)).val.Equiv
    (sub (ofQComplex QComplex.one) (scalar t).val) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have h := RealRaw.interval_order_of_valid t.value t.valid n
  change ((1-(t.value.compute n).hi ≤ 1+ -(t.value.compute n).lo) ∧ (0 : Rat) ≤ 0+ -0) ∧
    ((1+ -(t.value.compute n).hi ≤ 1-(t.value.compute n).lo) ∧ (0 : Rat)+ -0 ≤ 0)
  grind only

theorem reverse_distance (s t : Point) (R : Rat)
    (h : Small (sub (scalar t).val (scalar s).val) R) :
    Small (sub (scalar (reverse t)).val (scalar (reverse s)).val) R := by
  have he : (sub (scalar (reverse t)).val (scalar (reverse s)).val).Equiv
      (sub (scalar s).val (scalar t).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (scalar (reverse t)).property (scalar (reverse s)).property)
      (hright := sub_valid (scalar s).property (scalar t).property)
    have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (scalar (reverse s)).property)
      (hright := sub_valid (ofQComplex_valid _) (scalar s).property) (scalar_reverse s)
    have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (scalar (reverse t)).property)
      (hright := sub_valid (ofQComplex_valid _) (scalar t).property) (scalar_reverse t)
    let S := ComplexRawQuotient.ofRaw (scalar s).val (scalar s).property
    let T := ComplexRawQuotient.ofRaw (scalar t).val (scalar t).property
    let RS := ComplexRawQuotient.ofRaw (scalar (reverse s)).val (scalar (reverse s)).property
    let RT := ComplexRawQuotient.ofRaw (scalar (reverse t)).val (scalar (reverse t)).property
    change RS=1-S at hs
    change RT=1-T at ht
    change RT-RS=S-T
    grind only
  exact Small.congr (sub_valid (scalar s).property (scalar t).property)
    (sub_valid (scalar (reverse t)).property (scalar (reverse s)).property) (equiv_symm he)
    (RepresentedCauchySum.small_sub_symm _ _ _ h)

end ComputableAnalysis.RiemannHilbert.UnitInterval
