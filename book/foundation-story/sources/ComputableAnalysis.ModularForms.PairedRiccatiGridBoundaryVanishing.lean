import ComputableAnalysis.ModularForms.DyadicCellIndexing

/-! Actual midpoint outer-boundary sums tend to zero by cell estimates and
exact shared-edge cancellation. No integral or Cauchy identity is assumed. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem gridScalarSum_bound (n : Nat) (f : Nat → Scalar) (E : Rat) (_hE : 0≤E)
    (ht : ∀ j, j<n → Small (f j).val E) :
    Small (gridScalarSum n f).val ((n:Rat)*E) := by
  induction n with
  | zero =>
    change Small zero (0*E)
    rw [Rat.zero_mul]
    exact Small.zero Rat.le_refl
  | succ n ih =>
    have hb := LocalODE.small_add (ih (fun j hj => ht j (by omega))) (ht n (by omega))
    have he : (n:Rat)*E+E=((n+1:Nat):Rat)*E := by
      rw [Rat.natCast_add]
      change _=((n:Rat)+1)*E
      grind only
    rw [he] at hb
    exact hb

theorem gridScalarDoubleSum_bound (m n : Nat) (f : Nat → Nat → Scalar)
    (E : Rat) (hE : 0≤E) (ht : ∀ j k, j<m → k<n → Small (f j k).val E) :
    Small (gridScalarSum m (fun j => gridScalarSum n (f j))).val ((m:Rat)*((n:Rat)*E)) :=
  gridScalarSum_bound m _ _ (Rat.mul_nonneg Rat.natCast_nonneg hE)
    (fun j hj => gridScalarSum_bound n (f j) E hE (fun k hk => ht j k hj hk))

def pairedRiccatiGridCycleSum (J : QInterval × QInterval) (n : Nat) : Scalar :=
  rectangleGridCycleSum (fun q => pairedEntireRiccatiMap.eval (rationalRectangleScalar q) trivial) J (2^n)

def pairedRiccatiGridBoundary (J : QInterval × QInterval) (n : Nat) : Scalar :=
  rectangleGridBoundary (fun q => pairedEntireRiccatiMap.eval (rationalRectangleScalar q) trivial) J (2^n)

theorem pairedRiccatiGridBoundary_eventual_bound (eps W : QPos)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*W.val) (hy : J.2.width≤2*W.val) :
    ∃ N, ∀ n, N≤n → Small (pairedRiccatiGridBoundary J n).val (64*eps.val*W.val*W.val) := by
  obtain ⟨N,hN⟩ := pairedRiccati_indexed_dyadic_cell_bound eps W J hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn
  let E := 64*eps.val*(W.val*((1:Rat)/2)^n)*(W.val*((1:Rat)/2)^n)
  have hw : 0≤W.val*((1:Rat)/2)^n :=
    Rat.mul_nonneg (Rat.le_of_lt W.property) (Rat.pow_nonneg (by decide +kernel))
  have hE : 0≤E := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property)) hw) hw
  have hb := gridScalarDoubleSum_bound (2^n) (2^n)
    (fun j k => pairedRiccatiFullRectangleCycle (rectangleGridCell J (2^n) j k)) E hE
    (fun j k hj hk => hN n hn j k hj hk)
  have hp := two_pow_half_pow n
  have he : ((2^n:Nat):Rat)*(((2^n:Nat):Rat)*E)=64*eps.val*W.val*W.val := by
    dsimp [E]
    grind only
  rw [he] at hb
  exact Small.congr (pairedRiccatiGridCycleSum J n).property (pairedRiccatiGridBoundary J n).property
    (rectangleGridCycleSum_boundary_agreement
      (fun q => pairedEntireRiccatiMap.eval (rationalRectangleScalar q) trivial) J (2^n)) hb

theorem pairedRiccatiGridBoundary_converges_zero (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (pairedRiccatiGridBoundary J n).val eps.val := by
  let W : QPos := ⟨1+qabs J.1.width+qabs J.2.width,by
    have hx := qabs_nonneg J.1.width
    have hy := qabs_nonneg J.2.width
    grind only⟩
  have hx : J.1.width≤2*W.val := by
    have ha := self_le_qabs J.1.width
    have hb := qabs_nonneg J.1.width
    have hc := qabs_nonneg J.2.width
    change J.1.width≤2*(1+qabs J.1.width+qabs J.2.width)
    grind only
  have hy : J.2.width≤2*W.val := by
    have ha := self_le_qabs J.2.width
    have hb := qabs_nonneg J.1.width
    have hc := qabs_nonneg J.2.width
    change J.2.width≤2*(1+qabs J.1.width+qabs J.2.width)
    grind only
  have hD : 0<64*W.val*W.val :=
    Rat.mul_pos (Rat.mul_pos (by decide +kernel) W.property) W.property
  let eta : QPos := ⟨eps.val/(64*W.val*W.val),by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr hD)⟩
  obtain ⟨N,hN⟩ := pairedRiccatiGridBoundary_eventual_bound eta W J hX hY hx hy
  refine ⟨N, ?_⟩
  intro n hn
  have hb := hN n hn
  have he : eta.val*(64*W.val*W.val)=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt hD)
  have he' : 64*eta.val*W.val*W.val=eps.val := by grind only
  rw [he'] at hb
  exact hb

end ComputableAnalysis.ModularForms
