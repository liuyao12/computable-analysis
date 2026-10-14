import ComputableAnalysis.ModularForms.WeightedGridCellAgreement

/-! Every indexed dyadic interval is an actual bisection cell. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def indexedDyadicInterval (I : QInterval) (n j : Nat) : QInterval :=
  ⟨I.lo+(j:Rat)*I.width*((1:Rat)/2)^n,
    I.lo+((j+1:Nat):Rat)*I.width*((1:Rat)/2)^n⟩

theorem two_pow_half_pow (n : Nat) : ((2^n:Nat):Rat)*((1:Rat)/2)^n=1 := by
  rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow,Rat.div_def,Rat.one_mul]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr (Nat.pow_pos (by omega))))

theorem indexedDyadicInterval_left (I : QInterval) (n j : Nat) :
    indexedDyadicInterval (bisectInterval I false) n j=indexedDyadicInterval I (n+1) j := by
  simp only [indexedDyadicInterval,QInterval.mk.injEq]
  constructor
  · simp only [bisectInterval,Bool.false_eq_true,if_false,Rat.pow_succ,QInterval.width,QInterval.midpoint]
    grind only
  · simp only [bisectInterval,Bool.false_eq_true,if_false,Rat.pow_succ,QInterval.width,QInterval.midpoint]
    grind only

theorem indexedDyadicInterval_right (I : QInterval) (n j : Nat) :
    indexedDyadicInterval (bisectInterval I true) n j=indexedDyadicInterval I (n+1) (2^n+j) := by
  have hp := two_pow_half_pow n
  simp only [indexedDyadicInterval,QInterval.mk.injEq]
  constructor
  · simp only [bisectInterval,if_true,Rat.pow_succ,QInterval.width,QInterval.midpoint,Rat.natCast_add]
    grind only
  · simp only [bisectInterval,if_true,Rat.pow_succ,QInterval.width,QInterval.midpoint,Rat.natCast_add]
    change (I.lo+I.hi)/2+((j:Rat)+1)*(I.hi-(I.lo+I.hi)/2)*((1:Rat)/2)^n=
      I.lo+(((2^n:Nat):Rat)+(j:Rat)+1)*(I.hi-I.lo)*(((1:Rat)/2)^n*(1/2))
    grind only

theorem indexedDyadicInterval_bisection (I : QInterval) (n j : Nat) (hj : j<2^n) :
    ∃ choice : Nat → Bool, bisectionInterval I choice n=indexedDyadicInterval I n j := by
  induction n generalizing I j with
  | zero =>
    have hj0 : j=0 := by simp only [Nat.pow_zero] at hj; omega
    subst j
    refine ⟨fun _ => false, ?_⟩
    simp only [bisectionInterval,indexedDyadicInterval,Rat.pow_zero]
    cases I with
    | mk lo hi =>
      simp only [QInterval.mk.injEq,QInterval.width]
      constructor <;> grind only
  | succ n ih =>
    by_cases hl : j<2^n
    · obtain ⟨choice,hc⟩ := ih (bisectInterval I false) j hl
      let extended : Nat → Bool := fun k => match k with | 0 => false | k+1 => choice k
      refine ⟨extended, ?_⟩
      rw [bisectionInterval_shift]
      change bisectionInterval (bisectInterval I false) choice n=_
      rw [hc,indexedDyadicInterval_left]
    · have hle : 2^n≤j := by omega
      obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hle
      have hd : d<2^n := by rw [Nat.pow_succ] at hj; omega
      obtain ⟨choice,hc⟩ := ih (bisectInterval I true) d hd
      let extended : Nat → Bool := fun k => match k with | 0 => true | k+1 => choice k
      refine ⟨extended, ?_⟩
      rw [bisectionInterval_shift]
      change bisectionInterval (bisectInterval I true) choice n=_
      rw [hc,indexedDyadicInterval_right]

theorem rectangleGridCell_dyadic_coordinates (J : QInterval × QInterval) (n j k : Nat) :
    rectangleGridCell J (2^n) j k=
      (indexedDyadicInterval J.1 n j,indexedDyadicInterval J.2 n k) := by
  unfold rectangleGridCell rectangleGridStepX rectangleGridStepY indexedDyadicInterval
  rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
  simp only [Prod.mk.injEq,QInterval.mk.injEq,Rat.div_def,Rat.one_mul]
  grind only

theorem rectangleGridCell_bisection (J : QInterval × QInterval) (n j k : Nat)
    (hj : j<2^n) (hk : k<2^n) :
    ∃ choice : Nat → Bool × Bool, rectangleBisection J choice n=rectangleGridCell J (2^n) j k := by
  obtain ⟨cx,hcx⟩ := indexedDyadicInterval_bisection J.1 n j hj
  obtain ⟨cy,hcy⟩ := indexedDyadicInterval_bisection J.2 n k hk
  refine ⟨fun r => (cx r,cy r), ?_⟩
  rw [rectangleBisection_coordinates,rectangleGridCell_dyadic_coordinates]
  rw [hcx,hcy]

theorem pairedRiccati_indexed_dyadic_cell_bound (eps W : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ n, N≤n → ∀ j k : Nat, j<2^n → k<2^n →
      Small (pairedRiccatiFullRectangleCycle (rectangleGridCell J (2^n) j k)).val
        (64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)) := by
  obtain ⟨N,hN⟩ := pairedRiccati_uniform_dyadic_midpoint_error eps W J hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn j k hj hk
  obtain ⟨choice,hc⟩ := rectangleGridCell_bisection J n j k hj hk
  have hb := LocalODE.small_scale (by decide +kernel : (0:Rat)≤2) (hN choice n hn)
  rw [hc] at hb
  have he : 2*(32*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n))=
      64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n) := by grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.ModularForms
