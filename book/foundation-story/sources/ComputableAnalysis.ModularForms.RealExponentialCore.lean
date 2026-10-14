import ComputableAnalysis.ModularForms.ExponentialQuadraticRemainder
import ComputableAnalysis.ModularForms.ExponentialOrderTransport
import ComputableAnalysis.ModularForms.ExponentialCenterApproximation
import ComputableAnalysis.ModularForms.RealExponentialPrefixes
import ComputableAnalysis.ModularForms.RealComplexBridge

/-! General real-axis exponential laws, independent of CM special values.
These existing proofs are shared by the elementary chapter and modular forms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem entireExponential_real_rational_lower (x : RealRaw) (hx : x.Valid) (hpos : x.Pos)
    (r : Rat) (hr : (RealRaw.ofRat r).Le x) :
    (RealRaw.ofRat (1+r)).Le
      (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart := by
  let z : Scalar := ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩
  obtain ⟨start,hstart⟩ := hpos
  let c := exponentialQuadraticConstant (exponentialInputRadius z)
  have hc : 0 ≤ c := exponentialQuadraticConstant_nonnegative _
  let e := fun n => (c+1)*centerError z.val (n+start)
  have he : ShrinksToZero e := SeriesLimitLaws.shrinks_scale _
    (SeriesLimitLaws.shrinks_shift _ (centerError_shrinks z.val z.property) start)
    (c+1) (Rat.add_nonneg hc (by decide))
  intro i m
  apply RepresentedCauchySum.le_of_shrinking_error e he
  intro n
  let k := n+start
  let t := (x.compute k).midpoint
  have ho := RealRaw.interval_order_of_valid x hx k
  have hn := hx.2.1 start k (show start ≤ k by dsimp [k]; omega)
  have ht : 0 ≤ t := by
    change 0 < (x.compute start).lo at hstart
    have hm := QInterval.midpoint_mem ho
    dsimp [t]
    grind only
  have hcenter : rationalCenter z k = (⟨ofQComplex ⟨t,0⟩,ofQComplex_valid _⟩ : Scalar) := by
    apply Subtype.ext
    change ofQComplex ((ofRealRaw x).compute k).center = ofQComplex ⟨t,0⟩
    congr 1
    change (⟨t,((0:Rat)+0)/2⟩ : QComplex)=⟨t,0⟩
    congr 1
    decide +kernel
  have hl := entireExponential_rational_real_linear_lower t ht
  have hb := exponential_center_error z k
  rw [hcenter] at hb
  have hf := realLower_of_small_difference (entireExponentialValue z)
    (entireExponentialValue ⟨ofQComplex ⟨t,0⟩,ofQComplex_valid _⟩)
    (1+t) (exponentialCenterError z k) hl hb 0 m
  change 1+t-exponentialCenterError z k ≤ ((entireExponentialValue z).val.compute m).hi.re at hf
  have hrk := hr 0 k
  change r ≤ (x.compute k).hi at hrk
  have hm := QInterval.midpoint_mem ho
  have hd : r ≤ t+centerError z.val k := by
    dsimp [t,centerError,z]
    change r ≤ (x.compute k).midpoint +
      (((x.compute k).hi-(x.compute k).lo)+(0-0))
    unfold QInterval.midpoint at *
    grind [Rat.div_def]
  change 1+r ≤ ((entireExponentialValue z).val.compute m).hi.re + e n
  dsimp [e,c,exponentialCenterError,exponentialQuadraticConstant] at *
  grind only

theorem entireExponential_real_linear_lower (x : RealRaw) (hx : x.Valid) (hpos : x.Pos) :
    (RealRaw.add (RealRaw.ofRat 1) x).Le
      (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart := by
  intro n m
  have hr : (RealRaw.ofRat (x.compute n).lo).Le x := by
    intro i j
    exact RealRaw.le_refl x hx n j
  exact entireExponential_real_rational_lower x hx hpos (x.compute n).lo hr 0 m

theorem entireExponential_rational_real_imag_zero (t : Rat) :
    (entireExponentialValue ⟨ofQComplex ⟨t,0⟩,ofQComplex_valid _⟩).val.imagPart.Equiv
      (RealRaw.ofRat 0) := by
  let z : QComplex := ⟨t,0⟩
  let C := qabs t
  have hC : 0 ≤ C := qabs_nonneg t
  have hz : QComplex.normBound z ≤ C := by
    change qabs t+qabs 0 ≤ qabs t
    simp [qabs,Rat.add_zero]
  let f := ComplexExponentialApproximation.exponentialRawAt z C
  have hi : f.imagPart.Equiv (RealRaw.ofRat 0) := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
    have hp := ComplexExponentialApproximation.exponentialRawAt_contains_prefix hC hz n
    have he := real_exponential_prefix_imag_zero t (RationalMajorant.factorialTailStart C+n)
    have hl := hp.1.2
    have hu := hp.2.2
    change (f.compute n).lo.im ≤ (ComplexExponentialApproximation.expPrefix ⟨t,0⟩ _).im at hl
    change (ComplexExponentialApproximation.expPrefix ⟨t,0⟩ _).im ≤ (f.compute n).hi.im at hu
    rw [he] at hl hu
    exact ⟨hl,hu⟩
  exact RealRaw.equiv_trans (imagPart_valid (entireExponentialValue _).property)
    (imagPart_valid (ComplexExponentialApproximation.exponentialRawAt_valid hC hz))
    (RealRaw.ofRat_valid _) (imagPart_equiv (entireExponential_legacy_rational z C hC hz)) hi

theorem imaginaryZero_of_approximations (f : Scalar) (p : Nat → Scalar) (e : Nat → Rat)
    (he : ShrinksToZero e) (hc : ∀ N, Small (sub f.val (p N).val) (e N))
    (hi : ∀ N, (p N).val.imagPart.Equiv (RealRaw.ofRat 0)) :
    f.val.imagPart.Equiv (RealRaw.ofRat 0) := by
  have hs (N : Nat) : Small (sub f.val (ofRealRaw (p N).val.realPart)) (e N) :=
    Small.congr (sub_valid f.property (p N).property)
      (sub_valid f.property (ofRealRaw_valid _ (realPart_valid (p N).property)))
      (FunctionTheory.sub_congr (equiv_refl _ f.property) (equiv_real_embedding (p N) (hi N))) (hc N)
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  constructor
  · apply RepresentedCauchySum.le_of_shrinking_error e he
    intro N
    have h := (hs N).2.2.2 n 0
    change (f.val.compute n).lo.im + -0 ≤ e N at h
    change (f.val.compute n).lo.im ≤ 0+e N
    grind only
  · have hb : -(f.val.compute n).hi.im ≤ 0 :=
      RepresentedCauchySum.le_of_shrinking_error e he _ _ (by
        intro N
        have h := (hs N).2.2.1 0 n
        change -(e N) ≤ (f.val.compute n).hi.im + -0 at h
        change -(f.val.compute n).hi.im ≤ 0+e N
        grind only)
    change (0:Rat) ≤ (f.val.compute n).hi.im
    grind only

theorem entireExponential_real_imag_zero (x : RealRaw) (hx : x.Valid) :
    (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.imagPart.Equiv
      (RealRaw.ofRat 0) := by
  let z : Scalar := ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩
  apply imaginaryZero_of_approximations (entireExponentialValue z)
    (fun n => entireExponentialValue (rationalCenter z n)) (exponentialCenterError z)
    (exponentialCenterError_shrinks z) (exponential_center_error z)
  intro n
  have hcenter : rationalCenter z n =
      (⟨ofQComplex ⟨(x.compute n).midpoint,0⟩,ofQComplex_valid _⟩ : Scalar) := by
    apply Subtype.ext
    change ofQComplex ((ofRealRaw x).compute n).center = ofQComplex ⟨(x.compute n).midpoint,0⟩
    congr 1
    change (⟨(x.compute n).midpoint,((0:Rat)+0)/2⟩ : QComplex)=⟨(x.compute n).midpoint,0⟩
    congr 1
    decide +kernel
  rw [hcenter]
  exact entireExponential_rational_real_imag_zero _

theorem entireExponential_real_embedding (x : RealRaw) (hx : x.Valid) :
    (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.Equiv
      (ofRealRaw (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart) :=
  equiv_real_embedding _ (entireExponential_real_imag_zero x hx)

end ComputableAnalysis.ModularForms
