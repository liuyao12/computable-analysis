import ComputableAnalysis.RiemannHilbert.LocalODEMajorant
import ComputableAnalysis.RiemannHilbert.RepresentedCauchySum

/-!
# Constructing the scalar local-ODE value series

Finite coefficient recurrence and proved tail estimates construct a valid
represented sum at arbitrary represented arguments in a quantified local
disk. Prefix agreement and implementation invariance are proved. Analytic
differentiation and the functional ODE identity remain subsequent theorems.
-/
namespace ComputableAnalysis.RiemannHilbert.LocalODE

open ComplexRaw FunctionTheory

theorem tailBlock_valid (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N k : Nat) :
    (tailBlock a initial z N k).Valid := by
  induction k with
  | zero => exact ofQComplex_valid QComplex.zero
  | succ k ih =>
      exact add_valid ih
        (mul_valid (coefficient_valid a initial ha h0 _) (power_valid z hz _))

theorem sub_add_cancel (p t : ComplexRaw) (hp : p.Valid) (ht : t.Valid) :
    (sub (add p t) p).Equiv t := by
  intro n
  have hpc := QBox.center_mem (valid_ordered hp n)
  have htc := QBox.center_mem (valid_ordered ht n)
  have hAdd := QBox.add_contains hpc.1 hpc.2 htc.1 htc.2
  have hNeg := QBox.neg_contains hpc
  have hSub := QBox.add_contains hAdd.1 hAdd.2 hNeg.1 hNeg.2
  have he : QComplex.add (QComplex.add (p.compute n).center (t.compute n).center)
      (QComplex.neg (p.compute n).center) = (t.compute n).center := by
    cases (p.compute n).center
    cases (t.compute n).center
    simp only [QComplex.add, QComplex.neg, QComplex.mk.injEq]
    constructor <;> grind
  rw [he] at hSub
  apply (compareAt_overlap_iff _ _ n n).2
  exact QBox.overlaps_of_common_point hSub htc

theorem prefix_append (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N k : Nat) :
    (tailBlock a initial z 0 (N+k)).Equiv
      (add (tailBlock a initial z 0 N) (tailBlock a initial z N k)) := by
  induction k with
  | zero => exact equiv_symm (add_zero_equiv _ (tailBlock_valid a initial z ha h0 hz 0 N))
  | succ k ih =>
      change (add (tailBlock a initial z 0 (N+k))
        (mul (coefficient a initial (0+(N+k))) (power z (0+(N+k))))).Equiv _
      simp only [Nat.zero_add]
      have hp := tailBlock_valid a initial z ha h0 hz 0 N
      have ht := tailBlock_valid a initial z ha h0 hz N k
      have hterm := mul_valid (coefficient_valid a initial ha h0 (N+k))
        (power_valid z hz (N+k))
      apply equiv_trans
        (add_valid (tailBlock_valid a initial z ha h0 hz 0 (N+k)) hterm)
        (add_valid (add_valid hp ht) hterm) (add_valid hp (add_valid ht hterm))
      · exact add_equiv ih (equiv_refl _
          (mul_valid (coefficient_valid a initial ha h0 _) (power_valid z hz _)))
      · exact add_assoc_equiv _ _ _
          (tailBlock_valid a initial z ha h0 hz 0 N)
          (tailBlock_valid a initial z ha h0 hz N k)
          (mul_valid (coefficient_valid a initial ha h0 _) (power_valid z hz _))

theorem prefix_difference_tail (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N k : Nat) :
    (sub (tailBlock a initial z 0 (N+k)) (tailBlock a initial z 0 N)).Equiv
      (tailBlock a initial z N k) := by
  have hp := tailBlock_valid a initial z ha h0 hz 0 N
  have ht := tailBlock_valid a initial z ha h0 hz N k
  exact equiv_trans
    (sub_valid (tailBlock_valid a initial z ha h0 hz 0 (N+k)) hp)
    (sub_valid (add_valid hp ht) hp) ht
    (FunctionTheory.sub_congr (prefix_append a initial z ha h0 hz N k) (equiv_refl _ hp))
    (sub_add_cancel _ _ hp ht)

def valueTail (C K R : Rat) (N : Nat) : Rat := 4*C*(2*K*R)^N

theorem prefix_cauchy (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) (N n : Nat) (hNn : N ≤ n) :
    Small (sub (tailBlock a initial z 0 n) (tailBlock a initial z 0 N)) (valueTail C K R N) := by
  have ht := tailBlock_bound a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint
    hlocal N (n-N)
  have he := prefix_difference_tail a initial z ha h0 hz N (n-N)
  rw [Nat.add_sub_of_le hNn] at he
  exact Small.congr (tailBlock_valid a initial z ha h0 hz N (n-N))
    (sub_valid (tailBlock_valid a initial z ha h0 hz 0 n)
      (tailBlock_valid a initial z ha h0 hz 0 N)) (equiv_symm he) ht

/-- All computations of the sum are rational finite boxes. The numerical
majorant parameters specify the radius used by finite stabilization. -/
def sumValue (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (C K R : Rat) : ComplexRaw :=
  RepresentedCauchySum.value (fun N => tailBlock a initial z 0 N)
    (tailBlock_valid a initial z ha h0 hz 0) (valueTail C K R)

theorem sumValue_valid (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (sumValue a initial z ha h0 hz C K R).Valid :=
  RepresentedCauchySum.value_valid _ _
    (valueTail C K R) (tail_bound_shrinks C (2*K*R) hC
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal)
    (prefix_cauchy a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint hlocal)

/-- The evaluator is certified as this series sum, not merely as a valid
candidate. Error is measured against the actual represented prefixes. -/
theorem sumValue_close_prefix (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) (N : Nat) :
    Small (sub (sumValue a initial z ha h0 hz C K R) (tailBlock a initial z 0 N))
      (valueTail C K R N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (prefix_cauchy a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint hlocal) N

theorem power_congr (z w : ComplexRaw) (hz : z.Valid) (hw : w.Valid) (hzw : z.Equiv w)
    (k : Nat) : (power z k).Equiv (power w k) := by
  induction k with
  | zero => exact equiv_refl _ (ofQComplex_valid QComplex.one)
  | succ k ih => exact mul_equiv (power_valid z hz k) (power_valid w hw k) hz hw ih hzw

theorem tailBlock_congr (a b : Nat → ComplexRaw) (x y z w : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (hb : ∀ i, (b i).Valid)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) (hw : w.Valid)
    (hab : ∀ i, (a i).Equiv (b i)) (hxy : x.Equiv y) (hzw : z.Equiv w) (N k : Nat) :
    (tailBlock a x z N k).Equiv (tailBlock b y w N k) := by
  induction k with
  | zero => exact equiv_refl _ (ofQComplex_valid QComplex.zero)
  | succ k ih =>
      exact add_equiv ih (mul_equiv
        (coefficient_valid a x ha hx _) (coefficient_valid b y hb hy _)
        (power_valid z hz _) (power_valid w hw _)
        (coefficient_congr a b x y ha hb hx hy hab hxy _) (power_congr z w hz hw hzw _))

/-- The summed series respects coefficient, initial-value, and argument
representations. Bounds for the alternative implementation are transported,
not requested independently from the caller. -/
theorem sumValue_congr (a b : Nat → ComplexRaw) (x y z w : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (hb : ∀ i, (b i).Valid)
    (hx : x.Valid) (hy : y.Valid) (hz : z.Valid) (hw : w.Valid)
    (hAB : ∀ i, (a i).Equiv (b i)) (hXY : x.Equiv y) (hZW : z.Equiv w)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small x C) (hpoint : Small z R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    (sumValue a x z ha hx hz C K R).Equiv (sumValue b y w hb hy hw C K R) := by
  have hbBound : ∀ i, Small (b i) (M*K^i) :=
    fun i => Small.congr (ha i) (hb i) (hAB i) (hab i)
  have hyBound := Small.congr hx hy hXY hinit
  have hwBound := Small.congr hz hw hZW hpoint
  have hq : 0 ≤ 2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR
  have ht := tail_bound_shrinks C (2*K*R) hC hq hlocal
  have hnonneg : ∀ N, 0 ≤ valueTail C K R N :=
    fun N => Rat.mul_nonneg (Rat.mul_nonneg (by decide) hC) (Rat.pow_nonneg hq)
  exact RepresentedCauchySum.value_congr _ _ _ _ _ _ ht ht hnonneg hnonneg
    (prefix_cauchy a x z ha hx hz M C K R hM hC hK hR hMK hab hinit hpoint hlocal)
    (prefix_cauchy b y w hb hy hw M C K R hM hC hK hR hMK hbBound hyBound hwBound hlocal)
    (tailBlock_congr a b x y z w ha hb hx hy hz hw hAB hXY hZW 0)

/-- Auxiliary valid tail schedules cannot change the value. The Cauchy
hypotheses are finite bounds, not an assumed equality of the two sums. -/
theorem sumValue_independent (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (C K R D L S : Rat)
    (ht : ShrinksToZero (valueTail C K R)) (hs : ShrinksToZero (valueTail D L S))
    (ht0 : ∀ n, 0 ≤ valueTail C K R n) (hs0 : ∀ n, 0 ≤ valueTail D L S n)
    (hc : ∀ k n, k ≤ n → Small
      (sub (tailBlock a initial z 0 n) (tailBlock a initial z 0 k)) (valueTail C K R k))
    (hd : ∀ k n, k ≤ n → Small
      (sub (tailBlock a initial z 0 n) (tailBlock a initial z 0 k)) (valueTail D L S k)) :
    (sumValue a initial z ha h0 hz C K R).Equiv
      (sumValue a initial z ha h0 hz D L S) :=
  RepresentedCauchySum.value_congr _ _ _ _ _ _ ht hs ht0 hs0 hc hd
    (fun N => equiv_refl _ (tailBlock_valid a initial z ha h0 hz 0 N))

end ComputableAnalysis.RiemannHilbert.LocalODE
