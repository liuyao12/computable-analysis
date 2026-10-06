import ComputableAnalysis.RiemannHilbert.FiniteProducts
import ComputableAnalysis.RiemannHilbert.SeriesLimitLaws

/-! Constructing sums of supplied represented terms with geometric bounds. -/
namespace ComputableAnalysis.RiemannHilbert.ScalarSeries
open ComplexRaw FunctionTheory LocalODE

def block (t : Nat → ComplexRaw) (N : Nat) : Nat → ComplexRaw
  | 0 => zero
  | k+1 => add (block t N k) (t (N+k))

theorem block_valid (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (N k : Nat) :
    (block t N k).Valid := by
  induction k with
  | zero => exact ofQComplex_valid _
  | succ k ih => exact add_valid ih (ht _)

theorem block_image (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (N k : Nat) :
    ComplexRawQuotient.ofRaw (block t N k) (block_valid t ht N k) =
      FiniteProducts.block (fun i => ComplexRawQuotient.ofRaw (t i) (ht i)) N k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ComplexRawQuotient.ofRaw (block t N k) (block_valid t ht N k)+
      ComplexRawQuotient.ofRaw (t (N+k)) (ht _) = _
    rw [ih]; rfl

theorem prefix_image (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (block t 0 N) (block_valid t ht 0 N) =
      FiniteProducts.partialSum (fun i => ComplexRawQuotient.ofRaw (t i) (ht i)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [block.eq_2, Nat.zero_add]
    change ComplexRawQuotient.ofRaw (block t 0 N) (block_valid t ht 0 N)+
      ComplexRawQuotient.ofRaw (t N) (ht N) = _
    rw [ih]; rfl

theorem prefix_difference (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (N k : Nat) :
    (sub (block t 0 (N+k)) (block t 0 N)).Equiv (block t N k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (block_valid t ht 0 (N+k)) (block_valid t ht 0 N))
    (hright := block_valid t ht N k)
  change (ComplexRawQuotient.ofRaw (block t 0 (N+k)) (block_valid t ht 0 (N+k))-
    ComplexRawQuotient.ofRaw (block t 0 N) (block_valid t ht 0 N)) =
    ComplexRawQuotient.ofRaw (block t N k) (block_valid t ht N k)
  rw [prefix_image, prefix_image, block_image, FiniteProducts.prefix_append]
  let f : Nat → ScalarAlgebra.Value := fun i => ComplexRawQuotient.ofRaw (t i) (ht i)
  change (FiniteProducts.partialSum f N + FiniteProducts.block f N k) - FiniteProducts.partialSum f N = FiniteProducts.block f N k
  generalize FiniteProducts.partialSum f N = x
  generalize FiniteProducts.block f N k = y
  grind

theorem block_majorant (t : Nat → ComplexRaw) (C q : Rat)
    (hB : ∀ i, Small (t i) (2*C*q^i)) (N k : Nat) :
    Small (block t N k) (RationalMajorant.geomTailPartial (2*C) q N k) := by
  induction k with
  | zero => exact Small.zero (by change (0 : Rat) ≤ 0; decide)
  | succ k ih => exact small_add ih (hB (N+k))

theorem block_bound (t : Nat → ComplexRaw) (C q : Rat)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2)
    (hB : ∀ i, Small (t i) (2*C*q^i)) (N k : Nat) :
    Small (block t N k) (4*C*q^N) := by
  have hs := block_majorant t C q hB N k
  apply hs.mono
  have ht := RationalMajorant.geometric_tail_partial_bound
    (C := 2*C) (r := q) (N := N) (k := k) (Rat.mul_nonneg (by decide) hC) hq hlocal
  unfold RationalMajorant.geomTailBound at ht
  grind

theorem prefix_cauchy (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (C q : Rat)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2)
    (hB : ∀ i, Small (t i) (2*C*q^i)) (N n : Nat) (hNn : N ≤ n) :
    Small (sub (block t 0 n) (block t 0 N)) (4*C*q^N) := by
  have he := prefix_difference t ht N (n-N)
  rw [Nat.add_sub_of_le hNn] at he
  exact Small.congr (block_valid t ht N (n-N))
    (sub_valid (block_valid t ht 0 n) (block_valid t ht 0 N)) (equiv_symm he)
    (block_bound t C q hC hq hlocal hB N (n-N))

def value (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (C q : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => block t 0 N) (block_valid t ht 0) (fun N => 4*C*q^N)

theorem value_valid (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (C q : Rat)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2)
    (hB : ∀ i, Small (t i) (2*C*q^i)) : (value t ht C q).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (tail_bound_shrinks C q hC hq hlocal)
    (prefix_cauchy t ht C q hC hq hlocal hB)

theorem value_close (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (C q : Rat)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2)
    (hB : ∀ i, Small (t i) (2*C*q^i)) (N : Nat) :
    Small (sub (value t ht C q) (block t 0 N)) (4*C*q^N) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (prefix_cauchy t ht C q hC hq hlocal hB) N

theorem value_bound (t : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (C q : Rat)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2)
    (hB : ∀ i, Small (t i) (2*C*q^i)) : Small (value t ht C q) (4*C) := by
  apply SeriesLimitLaws.small_of_prefix_bound _ (value_valid t ht C q hC hq hlocal hB)
    (fun N => block t 0 N) (block_valid t ht 0) (4*C) (fun N => 4*C*q^N)
    (tail_bound_shrinks C q hC hq hlocal) (value_close t ht C q hC hq hlocal hB)
  intro N
  simpa only [Rat.pow_zero, Rat.mul_one] using block_bound t C q hC hq hlocal hB 0 N

theorem block_congr (t u : Nat → ComplexRaw) (h : ∀ i, (t i).Equiv (u i)) (N k : Nat) :
    (block t N k).Equiv (block u N k) := by
  induction k with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ k ih => exact add_equiv ih (h (N+k))

theorem value_congr (t u : Nat → ComplexRaw) (ht : ∀ i, (t i).Valid) (hu : ∀ i, (u i).Valid)
    (C q D r : Rat) (hC : 0 ≤ C) (hq : 0 ≤ q) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hlocal : q ≤ (1 : Rat)/2) (hrlocal : r ≤ (1 : Rat)/2)
    (hB : ∀ i, Small (t i) (2*C*q^i)) (hU : ∀ i, Small (u i) (2*D*r^i))
    (h : ∀ i, (t i).Equiv (u i)) : (value t ht C q).Equiv (value u hu D r) :=
  RepresentedCauchySum.value_congr _ _ _ _ _ _
    (tail_bound_shrinks C q hC hq hlocal) (tail_bound_shrinks D r hD hr hrlocal)
    (fun N => Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq))
    (fun N => Rat.mul_nonneg (Rat.mul_nonneg (by decide) hD) (Rat.pow_nonneg hr))
    (prefix_cauchy t ht C q hC hq hlocal hB) (prefix_cauchy u hu D r hD hr hrlocal hU)
    (block_congr t u h 0)


theorem block_uniform (t : Nat → ComplexRaw) (B : Rat) (_hB : 0 ≤ B) (N k : Nat)
    (h : ∀ i, i<k → Small (t (N+i)) B) : Small (block t N k) ((k : Rat)*B) := by
  induction k with
  | zero => exact Small.zero (by change (0 : Rat) ≤ 0*B; simp only [Rat.zero_mul]; decide)
  | succ k ih =>
    have hs := small_add (ih (fun i hi => h i (by omega))) (h k (by omega))
    apply hs.mono
    have hc : ((k+1 : Nat) : Rat) = (k : Rat)+1 := by exact_mod_cast Nat.add_one k
    rw [hc]
    grind

end ComputableAnalysis.RiemannHilbert.ScalarSeries
