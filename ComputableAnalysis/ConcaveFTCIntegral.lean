import ComputableAnalysis.ConcaveSecantFTC
import ComputableAnalysis.FiniteRiemannAlgebra

/-! The concave FTC. Its premises certify curvature and a particular
secant-defined derivative, not the desired integral endpoint identity.
Finite primitive widths are accounted for before telescoping. -/
namespace ComputableAnalysis
namespace ConcaveFTC
open IntervalSelections FiniteRiemannAlgebra

private theorem scaled_secant (F : RealFunRaw) {x y : Rat} (hxy : x < y) (n : Nat) :
    (y-x)*((secantRaw F x y).compute n).lo =
        (F.compute y n).lo-(F.compute x n).hi ∧
    (y-x)*((secantRaw F x y).compute n).hi =
        (F.compute y n).hi-(F.compute x n).lo := by
  have hp : 0 < y-x := by grind
  have hi : 0 <= 1/(y-x) := by
    simp only [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 hp)
  have hc := Rat.mul_inv_cancel (y-x) (Rat.ne_of_gt hp)
  simp only [secantRaw, secantSlopeIntervalOfRealFun, QInterval.slopeBetween,
    QInterval.divByRat, QInterval.scaleByRat, QInterval.subInterval, if_pos hi]
  simp only [Rat.div_def, Rat.one_mul]
  constructor <;> grind

/-- Finite-box local FTC estimate. Each source width is kept until a common
late stage has been selected; no cancellation between interval objects occurs. -/
theorem local_residual_bound {F : RealFunRaw} {D : Rat -> RealRaw} {A B x y : Rat}
    (H : DerivativeData F D A B)
    (hx : inDomainInterval A B x) (hy : inDomainInterval A B y) (hxy : x < y)
    (n : Nat) (tau : QPos)
    (wFx : (F.compute x n).width <= tau.val) (wFy : (F.compute y n).width <= tau.val)
    (wDx : ((D x).compute n).width <= tau.val) (wDy : ((D y).compute n).width <= tau.val) :
    qabs ((F.compute y n).lo-(F.compute x n).lo - (y-x)*((D x).compute n).lo) <=
      (H.K : Rat)*(y-x)*(y-x)+(1+(y-x))*tau.val := by
  have hp : 0 <= y-x := by grind
  have hS := H.secants x y hx hy hxy
  have hu := Rat.mul_le_mul_of_nonneg_left (hS.2 n n) hp
  have hl := Rat.mul_le_mul_of_nonneg_left (hS.1 n n) hp
  have hscaled := scaled_secant F hxy n
  rw [hscaled.1] at hu
  rw [hscaled.2] at hl
  have hlip := H.lipschitz y x hy hx n n
  have habs : qabs (x-y) = y-x := by
    rw [show x-y = -(y-x) by grind, qabs_neg, qabs_eq_self_of_nonneg hp]
  rw [habs] at hlip
  have hm := Rat.mul_le_mul_of_nonneg_left hlip hp
  have hwdx := Rat.mul_le_mul_of_nonneg_left wDx hp
  have hwdy := Rat.mul_le_mul_of_nonneg_left wDy hp
  have hk0 : 0 <= (H.K : Rat) := by exact_mod_cast (Nat.zero_le H.K)
  have hk2 : 0 <= (H.K : Rat)*(y-x)*(y-x) :=
    Rat.mul_nonneg (Rat.mul_nonneg hk0 hp) hp
  unfold QInterval.width at wFx wFy wDx wDy hwdx hwdy
  apply qabs_le_of_neg_le_le <;> grind

/-- The primitive endpoint computation, not an assumed integral value. -/
def endpointDifference (F : RealFunRaw) (a b : Rat) : RealRaw :=
  valueRaw F b - valueRaw F a

theorem endpointDifference_valid {F : RealFunRaw} {D : Rat -> RealRaw} {A B a b : Rat}
    (H : DerivativeData F D A B)
    (ha : inDomainInterval A B a) (hb : inDomainInterval A B b) :
    (endpointDifference F a b).Valid :=
  RealRaw.sub_valid (H.concave.valid_on b hb) (H.concave.valid_on a ha)

private theorem endpointSelection_mem {F : RealFunRaw} {D : Rat -> RealRaw} {A B a b : Rat}
    (H : DerivativeData F D A B)
    (ha : inDomainInterval A B a) (hb : inDomainInterval A B b) (n : Nat) :
    InBox ((F.compute b n).lo-(F.compute a n).lo) ((endpointDifference F a b).compute n) :=
  sub_mem
    ⟨Rat.le_refl, RealRaw.interval_order_of_valid (valueRaw F b) (H.concave.valid_on b hb) n⟩
    ⟨Rat.le_refl, RealRaw.interval_order_of_valid (valueRaw F a) (H.concave.valid_on a ha) n⟩

/-- Fixed-mesh FTC estimate. Only finitely many function values are involved
when a common proof-side evaluation stage is chosen. -/
theorem finite_sum_eventually_close
    {F : RealFunRaw} {D : Rat -> RealRaw} {A B a b : Rat}
    (H : DerivativeData F D A B)
    (ha : inDomainInterval A B a) (hb : inDomainInterval A B b) (hab : a <= b)
    (m : Nat) (hm : 0 < m) (E : Rat)
    (hE : (m : Rat)*(H.K : Rat)*mesh a b m*mesh a b m <= E) (eps : QPos) :
    ∃ N, ∀ n, N <= n ->
      qabs ((F.compute b n).lo-(F.compute a n).lo-((leftSum D a b m).compute n).lo) <=
        E+eps.val := by
  by_cases heq : a = b
  · subst b
    have hz : mesh a a m = 0 := by
      simp only [mesh, if_neg (Nat.ne_of_gt hm), Rat.sub_self, Rat.div_def, Rat.zero_mul]
    simp only [hz, Rat.mul_zero] at hE
    refine ⟨0, ?_⟩
    intro n _
    rw [leftSum_lo D hab m hm n, hz]
    simp only [Rat.zero_mul, sum_zero_function, Rat.sub_self]
    have habs : qabs (0 : Rat) = 0 := by decide +kernel
    rw [habs]
    have hp := eps.property
    grind
  · have habp : a < b := by grind
    let h := mesh a b m
    have hp : 0 < h := by
      dsimp [h, mesh]
      rw [if_neg (Nat.ne_of_gt hm), Rat.div_def]
      exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hm))
    have h0 := Rat.le_of_lt hp
    have hmpos : 0 < (m : Rat) := (Rat.natCast_pos).2 hm
    let den : Rat := (m : Rat)*(1+h)
    have hdpos : 0 < den := Rat.mul_pos hmpos (by grind)
    let tau : QPos := ⟨eps.val/den, by
      rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hdpos)⟩
    let P : Nat -> Nat -> Prop := fun i n =>
      (F.compute (leftPoint a b m i) n).width <= tau.val ∧
      ((D (leftPoint a b m i)).compute n).width <= tau.val
    have hgrid : ∀ i, i < m+1 -> ∃ N, ∀ n, N <= n -> P i n := by
      intro i hi
      have hmem := grid_mem ha hb hab hm (by omega : i <= m)
      obtain ⟨NF, hNF⟩ := (H.concave.valid_on _ hmem).2.2 tau
      obtain ⟨ND, hND⟩ := (H.valid _ hmem).2.2 tau
      exact ⟨max NF ND, fun n hn => ⟨hNF n (by omega), hND n (by omega)⟩⟩
    obtain ⟨N, hN⟩ := finite_eventually P (m+1) hgrid
    refine ⟨N, ?_⟩
    intro n hn
    have hcell : ∀ i, i < m ->
        qabs ((F.compute (leftPoint a b m (i+1)) n).lo-
          (F.compute (leftPoint a b m i) n).lo-
          h*(1*((D (leftPoint a b m i)).compute n).lo)) <=
            (H.K : Rat)*h*h+(1+h)*tau.val := by
      intro i hi
      have hx := grid_mem ha hb hab hm (by omega : i <= m)
      have hy := grid_mem ha hb hab hm (by omega : i+1 <= m)
      have hstep := leftPoint_step a b m i
      change leftPoint a b m (i+1)-leftPoint a b m i = h at hstep
      have hxy : leftPoint a b m i < leftPoint a b m (i+1) := by grind
      have hi0 := hN n hn i (by omega)
      have hi1 := hN n hn (i+1) (by omega)
      have hbnd := local_residual_bound H hx hy hxy n tau hi0.1 hi1.1 hi0.2 hi1.2
      rw [hstep] at hbnd
      simpa only [Rat.one_mul] using hbnd
    have ht := telescope_bound
      (fun i => (F.compute (leftPoint a b m i) n).lo)
      (fun i => ((D (leftPoint a b m i)).compute n).lo)
      h 1 ((H.K : Rat)*h*h+(1+h)*tau.val) m hcell
    rw [leftPoint_zero, leftPoint_endpoint hm, Rat.one_mul] at ht
    have hc := Rat.mul_inv_cancel den (Rat.ne_of_gt hdpos)
    have htau : (m : Rat)*(1+h)*tau.val = eps.val := by
      change den*(eps.val/den) = eps.val
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]
    have hsum : (m : Rat)*((H.K : Rat)*h*h+(1+h)*tau.val) =
        (m : Rat)*(H.K : Rat)*h*h+eps.val := by grind
    rw [hsum] at ht
    rw [leftSum_lo D hab m hm n]
    change qabs ((F.compute b n).lo-(F.compute a n).lo-
      sum (fun i => h*((D (leftPoint a b m i)).compute n).lo) m) <= E+eps.val
    change (m : Rat)*(H.K : Rat)*h*h <= E at hE
    exact Rat.le_trans ht (by grind)

/-- General concave FTC: the derivative's finite Riemann computation is
compared with primitive endpoints. No overlap or endpoint identity appears
among the input certificate fields. -/
theorem finite_riemann_overlaps
    {F : RealFunRaw} {D : Rat -> RealRaw} {A B a b : Rat}
    (H : DerivativeData F D A B)
    (ha : inDomainInterval A B a) (hb : inDomainInterval A B b) (hab : a <= b)
    (m : Nat) (hm : 0 < m) (E : Rat)
    (hE : (m : Rat)*(H.K : Rat)*mesh a b m*mesh a b m <= E) :
    ∀ q t, (QInterval.expand ((leftSum D a b m).compute q) E).Overlaps
      ((endpointDifference F a b).compute t) := by
  have hR := leftSum_valid D H.valid ha hb hab m hm
  apply expanded_overlaps_of_selected_error hR (endpointDifference_valid H ha hb)
    (fun n => ((leftSum D a b m).compute n).lo)
    (fun n => (F.compute b n).lo-(F.compute a n).lo)
    (fun n => ⟨Rat.le_refl, RealRaw.interval_order_of_valid _ hR n⟩)
    (endpointSelection_mem H ha hb) E
  exact finite_sum_eventually_close H ha hb hab m hm E hE

/-- One integral algorithm can carry this FTC proof in addition to any
independent direct proof. Its runtime remains the same fixed intersection. -/
theorem integral_equiv_endpoint
    {F : RealFunRaw} {D : Rat -> RealRaw} {A B a b : Rat}
    (H : DerivativeData F D A B)
    (ha : inDomainInterval A B a) (hb : inDomainInterval A B b) (hab : a <= b)
    (radius : Nat -> Rat)
    (hbudget : ∀ k, ((k+1 : Nat) : Rat)*(H.K : Rat)*mesh a b (k+1)*mesh a b (k+1) <= radius k) :
    (Integral.Dovetail.raw (fun k => leftSum D a b (k+1)) radius).Equiv
      (endpointDifference F a b) :=
  Integral.Dovetail.raw_equiv_endpoint (fun k =>
    finite_riemann_overlaps H ha hb hab (k+1) (Nat.succ_pos k) (radius k) (hbudget k))

/-- Validity is established independently of the chosen endpoint-equivalence
proof name. -/
theorem integral_valid
    {F : RealFunRaw} {D : Rat -> RealRaw} {A B a b : Rat}
    (H : DerivativeData F D A B)
    (ha : inDomainInterval A B a) (hb : inDomainInterval A B b) (hab : a <= b)
    (radius : Nat -> Rat) (hshrink : ShrinksToZero radius)
    (hbudget : ∀ k, ((k+1 : Nat) : Rat)*(H.K : Rat)*mesh a b (k+1)*mesh a b (k+1) <= radius k) :
    (Integral.Dovetail.raw (fun k => leftSum D a b (k+1)) radius).Valid :=
  Integral.Dovetail.raw_valid (fun k => leftSum_valid D H.valid ha hb hab (k+1) (Nat.succ_pos k))
    (endpointDifference_valid H ha hb) hshrink
    (fun k => finite_riemann_overlaps H ha hb hab (k+1) (Nat.succ_pos k) (radius k) (hbudget k))

end ConcaveFTC
end ComputableAnalysis
