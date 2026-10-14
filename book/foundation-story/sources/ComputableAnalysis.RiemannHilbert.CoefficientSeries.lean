import ComputableAnalysis.RiemannHilbert.GeometricSeries
import ComputableAnalysis.RiemannHilbert.LocalODESum
import ComputableAnalysis.RiemannHilbert.LocalODEInitialValue

/-! The represented coefficient function defined by its supplied local series. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def seriesTerm (c : Nat → ComplexRaw) (z : ComplexRaw) (n : Nat) : ComplexRaw :=
  mul (c n) (power z n)

theorem seriesTerm_valid (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (hz : z.Valid) (n : Nat) : (seriesTerm c z n).Valid :=
  mul_valid (hc n) (power_valid z hz n)

theorem seriesTerm_bound (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (hz : z.Valid) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ n, Small (c n) (C*K^n)) (hzR : Small z R) (n : Nat) :
    Small (seriesTerm c z n) (2*C*(2*K*R)^n) := by
  have hs := Small.mul (hc n) (power_valid z hz n) (Rat.mul_nonneg hC (Rat.pow_nonneg hK))
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hR)) (hcB n) (power_small z hz R hR hzR n)
  have hp : K^n*(2*R)^n=(2*K*R)^n := by
    rw [← rational_mul_pow]
    congr 1
    grind
  have he : 2*(C*K^n)*(2*R)^n=2*C*(2*K*R)^n := by
    rw [← hp]
    grind
  rw [he] at hs
  exact hs

def coefficientSum (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (hz : z.Valid) (M K R : Rat) : ComplexRaw :=
  ScalarSeries.value (seriesTerm c z) (seriesTerm_valid c z hc hz) M (2*K*R)

theorem coefficientSum_valid (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (hz : z.Valid) (M K R : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ n, Small (c n) (M*K^n)) (hzR : Small z R) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (coefficientSum c z hc hz M K R).Valid :=
  ScalarSeries.value_valid _ _ M (2*K*R) hM
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
    (seriesTerm_bound c z hc hz M K R hM hK hR hcB hzR)

theorem coefficientSum_close (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (hz : z.Valid) (M K R : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ n, Small (c n) (M*K^n)) (hzR : Small z R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub (coefficientSum c z hc hz M K R) (ScalarSeries.block (seriesTerm c z) 0 N))
      (4*M*(2*K*R)^N) :=
  ScalarSeries.value_close _ _ M (2*K*R) hM
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
    (seriesTerm_bound c z hc hz M K R hM hK hR hcB hzR) N

theorem coefficientSum_bound (c : Nat → ComplexRaw) (z : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (hz : z.Valid) (M K R : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ n, Small (c n) (M*K^n)) (hzR : Small z R) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    Small (coefficientSum c z hc hz M K R) (4*M) :=
  ScalarSeries.value_bound _ _ M (2*K*R) hM
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
    (seriesTerm_bound c z hc hz M K R hM hK hR hcB hzR)

theorem coefficientSum_congr (c d : Nat → ComplexRaw) (z w : ComplexRaw)
    (hc : ∀ n, (c n).Valid) (hd : ∀ n, (d n).Valid) (hz : z.Valid) (hw : w.Valid)
    (hcd : ∀ n, (c n).Equiv (d n)) (hzw : z.Equiv w) (M K R : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ n, Small (c n) (M*K^n)) (hzR : Small z R) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (coefficientSum c z hc hz M K R).Equiv (coefficientSum d w hd hw M K R) := by
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  exact ScalarSeries.value_congr _ _ _ _ M (2*K*R) M (2*K*R) hM hq hM hq hlocal hlocal
    (seriesTerm_bound c z hc hz M K R hM hK hR hcB hzR)
    (seriesTerm_bound d w hd hw M K R hM hK hR
      (fun n => Small.congr (hc n) (hd n) (hcd n) (hcB n)) (Small.congr hz hw hzw hzR))
    (fun n => mul_equiv (hc n) (hd n) (power_valid z hz n) (power_valid w hw n)
      (hcd n) (power_congr z w hz hw hzw n))


theorem coefficientSum_congr_of_bounds (c d : Nat → ComplexRaw) (z w : ComplexRaw)
    (hc : ∀ i, (c i).Valid) (hd : ∀ i, (d i).Valid) (hz : z.Valid) (hw : w.Valid)
    (hcd : ∀ i, (c i).Equiv (d i)) (hzw : z.Equiv w) (C K R D L S : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hdB : ∀ i, Small (d i) (D*L^i))
    (hzB : Small z R) (hwB : Small w S)
    (hq : 2*K*R ≤ (1 : Rat)/2) (hr : 2*L*S ≤ (1 : Rat)/2) :
    (coefficientSum c z hc hz C K R).Equiv (coefficientSum d w hd hw D L S) :=
  ScalarSeries.value_congr _ _ _ _ C (2*K*R) D (2*L*S) hC
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hD
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hL) hS) hq hr
    (seriesTerm_bound c z hc hz C K R hC hK hR hcB hzB)
    (seriesTerm_bound d w hd hw D L S hD hL hS hdB hwB)
    (fun i => mul_equiv (hc i) (hd i) (power_valid z hz i) (power_valid w hw i)
      (hcd i) (power_congr z w hz hw hzw i))

theorem coefficientBlock (b : Nat → ComplexRaw) (initial z : ComplexRaw) (N k : Nat) :
    ScalarSeries.block (seriesTerm (coefficient b initial) z) N k = tailBlock b initial z N k := by
  induction k with
  | zero => rfl
  | succ k ih => change add (ScalarSeries.block (seriesTerm (coefficient b initial) z) N k) _ =
                   add (tailBlock b initial z N k) _
                 rw [ih]; rfl

theorem sumValue_as_terms (b : Nat → ComplexRaw) (initial z : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid) (hz : z.Valid) (C K R : Rat) :
    sumValue b initial z hb h0 hz C K R =
      ScalarSeries.value (seriesTerm (coefficient b initial) z)
        (seriesTerm_valid _ z (coefficient_valid b initial hb h0) hz) C (2*K*R) := by
  have hblocks : (fun N => ScalarSeries.block (seriesTerm (coefficient b initial) z) 0 N) =
      (fun N => tailBlock b initial z 0 N) := funext (coefficientBlock b initial z 0)
  unfold sumValue ScalarSeries.value
  simp only [hblocks]
  rfl

/-- Equivalent data and independently certified bounds give the same solution
value on the common domain. The tail algorithms and initial bounds may differ. -/
theorem sumValue_congr_of_bounds (a b : Nat → ComplexRaw) (x y z w : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (hb : ∀ i, (b i).Valid)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) (hw : w.Valid)
    (hab : ∀ i, (a i).Equiv (b i)) (hxy : x.Equiv y) (hzw : z.Equiv w)
    (M C K R P D L S : Rat)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hMK : 2*M ≤ K) (hPL : 2*P ≤ L)
    (haB : ∀ i, Small (a i) (M*K^i)) (hbB : ∀ i, Small (b i) (P*L^i))
    (hxB : Small x C) (hyB : Small y D) (hzB : Small z R) (hwB : Small w S)
    (hq : 2*K*R ≤ (1 : Rat)/2) (hr : 2*L*S ≤ (1 : Rat)/2) :
    (sumValue a x z ha hx hz C K R).Equiv (sumValue b y w hb hy hw D L S) := by
  rw [sumValue_as_terms a x z ha hx hz C K R,
    sumValue_as_terms b y w hb hy hw D L S]
  exact ScalarSeries.value_congr _ _ _ _ C (2*K*R) D (2*L*S) hC
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hD
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hL) hS) hq hr
    (term_majorant a x z ha hx hz M C K R hM hC hK hR hMK haB hxB hzB)
    (term_majorant b y w hb hy hw P D L S hP hD hL hS hPL hbB hyB hwB)
    (fun n => mul_equiv (coefficient_valid a x ha hx n) (coefficient_valid b y hb hy n)
      (power_valid z hz n) (power_valid w hw n)
      (coefficient_congr a b x y ha hb hx hy hab hxy n) (power_congr z w hz hw hzw n))


/-- Every nonempty prefix of a supplied series evaluates to its constant
coefficient at the center. No recurrence equation is needed. -/
theorem coefficientPrefix_zero (c : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid) (N : Nat) :
    (ScalarSeries.block (seriesTerm c zero) 0 (N+1)).Equiv (c 0) := by
  induction N with
  | zero =>
    change (add zero (mul (c 0) one)).Equiv (c 0)
    exact equiv_trans (add_valid (ofQComplex_valid _) (mul_valid (hc 0) (ofQComplex_valid _)))
      (mul_valid (hc 0) (ofQComplex_valid _)) (hc 0)
      (zero_add_equiv _ (mul_valid (hc 0) (ofQComplex_valid _))) (mul_one_equiv _ (hc 0))
  | succ N ih =>
    rw [ScalarSeries.block.eq_2]
    simp only [Nat.zero_add]
    have hp := power_valid zero (ofQComplex_valid _) (N+1)
    have ht : (seriesTerm c zero (N+1)).Equiv zero :=
      equiv_trans (mul_valid (hc _) hp) (mul_valid (hc _) (ofQComplex_valid _))
        (ofQComplex_valid _)
        (mul_equiv (hc _) (hc _) hp (ofQComplex_valid _)
          (equiv_refl _ (hc _)) (power_zero_succ N)) (mul_zero_equiv _ (hc _))
    exact equiv_trans
      (add_valid (ScalarSeries.block_valid _ (seriesTerm_valid c zero hc (ofQComplex_valid _)) 0 (N+1))
        (seriesTerm_valid c zero hc (ofQComplex_valid _) (N+1)))
      (add_valid (hc 0) (ofQComplex_valid _)) (hc 0)
      (add_equiv ih ht) (add_zero_equiv _ (hc 0))

theorem coefficientSum_zero (c : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (coefficientSum c zero hc (ofQComplex_valid _) C K R).Equiv (c 0) := by
  have ht := seriesTerm_valid c zero hc (ofQComplex_valid _)
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  apply RepresentedCauchySum.unique (fun N => ScalarSeries.block (seriesTerm c zero) 0 (N+1))
    (fun N => ScalarSeries.block_valid _ ht 0 (N+1))
    (fun N => 4*C*(2*K*R)^(N+1))
    (SeriesLimitLaws.shrinks_shift _ (tail_bound_shrinks C (2*K*R) hC hq hlocal) 1)
    _ (c 0)
    (coefficientSum_valid c zero hc (ofQComplex_valid _) C K R hC hK hR hcB (Small.zero hR) hlocal)
    (hc 0)
    (fun N => coefficientSum_close c zero hc (ofQComplex_valid _) C K R hC hK hR hcB
      (Small.zero hR) hlocal (N+1))
  intro N
  have hp := ScalarSeries.block_valid _ ht 0 (N+1)
  have he := FunctionTheory.sub_congr (equiv_refl _ (hc 0)) (coefficientPrefix_zero c hc N)
  have hz := equiv_trans (sub_valid (hc 0) hp) (sub_valid (hc 0) (hc 0)) (ofQComplex_valid _)
    he (add_neg_equiv _ (hc 0))
  exact Small.congr (ofQComplex_valid _) (sub_valid (hc 0) hp) (equiv_symm hz)
    (Small.zero (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq)))

end ComputableAnalysis.RiemannHilbert.LocalODE
