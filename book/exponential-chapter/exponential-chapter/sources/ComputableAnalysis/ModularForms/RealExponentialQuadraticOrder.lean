import ComputableAnalysis.ModularForms.RealExponentialQuadraticPrefixes

/-! Quadratic exponential lower bounds at valid represented real inputs. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem entireExponential_real_rational_quadratic_lower (x : RealRaw) (hx : x.Valid) (hpos : x.Pos)
    (r : Rat) (hr0 : 0≤r) (hr : (RealRaw.ofRat r).Le x) :
    (RealRaw.ofRat (1+r+r*r/2)).Le
      (entireExponentialValue ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val.realPart := by
  let z : Scalar := ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩
  obtain ⟨start,hstart⟩ := hpos
  let c := exponentialQuadraticConstant (exponentialInputRadius z)
  have hc : 0 ≤ c := exponentialQuadraticConstant_nonnegative _
  let e := fun n => (c+1+r)*centerError z.val (n+start)
  have he : ShrinksToZero e := SeriesLimitLaws.shrinks_scale _
    (SeriesLimitLaws.shrinks_shift _ (centerError_shrinks z.val z.property) start)
    (c+1+r) (Rat.add_nonneg (Rat.add_nonneg hc (by decide)) hr0)
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
  have hl := entireExponential_rational_real_quadratic_lower t ht
  have hb := exponential_center_error z k
  rw [hcenter] at hb
  have hf := realLower_of_small_difference (entireExponentialValue z)
    (entireExponentialValue ⟨ofQComplex ⟨t,0⟩,ofQComplex_valid _⟩)
    (1+t+t*t/2) (exponentialCenterError z k) hl hb 0 m
  change 1+t+t*t/2-exponentialCenterError z k ≤ ((entireExponentialValue z).val.compute m).hi.re at hf
  have hrk := hr 0 k
  change r ≤ (x.compute k).hi at hrk
  have hm := QInterval.midpoint_mem ho
  have hd : r ≤ t+centerError z.val k := by
    dsimp [t,centerError,z]
    change r ≤ (x.compute k).midpoint +
      (((x.compute k).hi-(x.compute k).lo)+(0-0))
    unfold QInterval.midpoint at *
    grind [Rat.div_def]
  change 1+r+r*r/2 ≤ ((entireExponentialValue z).val.compute m).hi.re + e n
  have hsq : 0≤(t-r)*(t-r) := by
    have ht : 0≤t-r ∨ t-r≤0 := Rat.le_total
    rcases ht with hp | hn
    · exact Rat.mul_nonneg hp hp
    · have hp : 0≤ -(t-r) := by grind only
      have h := Rat.mul_nonneg hp hp
      grind only
  have hmul := Rat.mul_le_mul_of_nonneg_left hd hr0
  dsimp [e,c,exponentialCenterError,exponentialQuadraticConstant] at *
  grind only


end ComputableAnalysis.ModularForms
