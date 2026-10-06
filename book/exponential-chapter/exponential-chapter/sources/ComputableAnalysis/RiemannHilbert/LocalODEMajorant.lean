import ComputableAnalysis.RiemannHilbert.LocalODECoefficients
import ComputableAnalysis.HolomorphicExamples
import ComputableAnalysis.PowerSeries

/-!
# A quantitative scalar local-ODE majorant

The bound is on represented values (`Small`), not on arbitrarily early boxes.
It is derived from coefficient bounds by finite recurrence. It does not
assert that an arbitrary holomorphic coefficient function has been expanded
into this sequence or that the resulting summed series has been constructed.
-/
namespace ComputableAnalysis.RiemannHilbert.LocalODE

open ComplexRaw FunctionTheory

/-- Exact coordinate bounds add without any completed norm. -/
theorem small_add {z w : ComplexRaw} {r s : Rat}
    (h : Small z r) (k : Small w s) : Small (add z w) (r+s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m
    have hz := h.1 n m; have hw := k.1 n m
    change -r ≤ (z.compute m).hi.re at hz
    change -s ≤ (w.compute m).hi.re at hw
    change -(r+s) ≤ (z.compute m).hi.re + (w.compute m).hi.re
    grind
  · intro n m
    have hz := h.2.1 n m; have hw := k.2.1 n m
    change (z.compute n).lo.re ≤ r at hz
    change (w.compute n).lo.re ≤ s at hw
    change (z.compute n).lo.re + (w.compute n).lo.re ≤ r+s
    grind
  · intro n m
    have hz := h.2.2.1 n m; have hw := k.2.2.1 n m
    change -r ≤ (z.compute m).hi.im at hz
    change -s ≤ (w.compute m).hi.im at hw
    change -(r+s) ≤ (z.compute m).hi.im + (w.compute m).hi.im
    grind
  · intro n m
    have hz := h.2.2.2 n m; have hw := k.2.2.2 n m
    change (z.compute n).lo.im ≤ r at hz
    change (w.compute n).lo.im ≤ s at hw
    change (z.compute n).lo.im + (w.compute n).lo.im ≤ r+s
    grind

theorem small_scale {z : ComplexRaw} {r c : Rat}
    (hc : 0 ≤ c) (h : Small z r) : Small (scaleRat c z) (c*r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m
    have hh := Rat.mul_le_mul_of_nonneg_left (h.1 n m) hc
    change c * (-r) ≤ c * (z.compute m).hi.re at hh
    simpa only [RealRaw.Le, RealRaw.ofRat, ComplexRaw.realPart, ComplexRaw.scaleRat,
      QBox.scaleRat, if_pos hc, Rat.mul_neg] using hh
  · intro n m
    have hh := Rat.mul_le_mul_of_nonneg_left (h.2.1 n m) hc
    change c * (z.compute n).lo.re ≤ c*r at hh
    simpa only [RealRaw.Le, RealRaw.ofRat, ComplexRaw.realPart, ComplexRaw.scaleRat,
      QBox.scaleRat, if_pos hc] using hh
  · intro n m
    have hh := Rat.mul_le_mul_of_nonneg_left (h.2.2.1 n m) hc
    change c * (-r) ≤ c * (z.compute m).hi.im at hh
    simpa only [RealRaw.Le, RealRaw.ofRat, ComplexRaw.imagPart, ComplexRaw.scaleRat,
      QBox.scaleRat, if_pos hc, Rat.mul_neg] using hh
  · intro n m
    have hh := Rat.mul_le_mul_of_nonneg_left (h.2.2.2 n m) hc
    change c * (z.compute n).lo.im ≤ c*r at hh
    simpa only [RealRaw.Le, RealRaw.ofRat, ComplexRaw.imagPart, ComplexRaw.scaleRat,
      QBox.scaleRat, if_pos hc] using hh

theorem small_sum_uniform (zs : List ComplexRaw) (B : Rat) (_hB : 0 ≤ B)
    (h : ∀ z ∈ zs, Small z B) : Small (sum zs) ((zs.length : Rat)*B) := by
  induction zs with
  | nil => simpa [sum] using Small.zero (r := 0) (by decide)
  | cons z zs ih =>
      have hh := small_add (h z (by simp)) (ih (fun w hw => h w (by simp [hw])))
      have he : B + (zs.length : Rat)*B = ((z::zs).length : Rat)*B := by
        simp [Rat.natCast_add, Rat.add_mul, Rat.add_comm]
      rw [he] at hh
      exact hh

theorem rational_pow_add (K : Rat) (i j : Nat) : K^(i+j) = K^i*K^j := by
  induction j with
  | zero => simp [Rat.pow_zero, Rat.mul_one]
  | succ j ih =>
      rw [Nat.add_succ, Rat.pow_succ, Rat.pow_succ, ih]
      exact Rat.mul_assoc _ _ _

theorem rational_mul_pow (x y : Rat) (k : Nat) : (x*y)^k = x^k*y^k := by
  induction k with
  | zero => simp [Rat.pow_zero]
  | succ k ih =>
      rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ, ih]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- A geometric coefficient bound for the actual represented recurrence. -/
theorem coefficient_majorant (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid)
    (M C K : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (hab : ∀ i, Small (a i) (M*K^i)) (hinit : Small initial C) (k : Nat) :
    Small (coefficient a initial k) (C*K^k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero => simpa using hinit
      | succ k =>
          rw [coefficient_succ]
          have hB : 0 ≤ 2*M*C*K^k :=
            Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hC) (Rat.pow_nonneg hK)
          have hconv : Small (convolution a (coefficient a initial) k)
              (((k+1 : Nat) : Rat)*(2*M*C*K^k)) := by
            unfold convolution
            have hs := small_sum_uniform
              ((List.range (k+1)).map (fun i =>
                if i ≤ k then mul (a i) (coefficient a initial (k-i)) else zero))
              (2*M*C*K^k) hB ?_
            · simpa using hs
            · intro z hz
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
              have hik : i ≤ k := by have := List.mem_range.mp hi; omega
              rw [if_pos hik]
              have ht := Small.mul (ha i) (coefficient_valid a initial ha h0 (k-i))
                (Rat.mul_nonneg hM (Rat.pow_nonneg hK))
                (Rat.mul_nonneg hC (Rat.pow_nonneg hK)) (hab i) (ih (k-i) (by omega))
              have hp : K^i * K^(k-i) = K^k := by
                rw [← rational_pow_add]; congr 1; omega
              have he : 2*(M*K^i)*(C*K^(k-i)) = 2*M*C*K^k := by
                calc
                  _ = (2*M*C)*(K^i*K^(k-i)) := by grind [Rat.mul_assoc, Rat.mul_comm]
                  _ = _ := by rw [hp]
              rw [he] at ht
              exact ht
          have hd : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
          have hrecip : 0 ≤ 1 / ((k+1 : Nat) : Rat) := by
            rw [Rat.div_def, Rat.one_mul]
            exact Rat.le_of_lt ((Rat.inv_pos).2 hd)
          have hs := small_scale hrecip hconv
          have he : (1 / ((k+1 : Nat) : Rat)) *
              (((k+1 : Nat) : Rat)*(2*M*C*K^k)) = 2*M*C*K^k := by
            rw [Rat.div_def, Rat.one_mul]
            calc
              _ = (((k+1 : Nat) : Rat)*((k+1 : Nat) : Rat)⁻¹)*(2*M*C*K^k) := by
                grind [Rat.mul_assoc, Rat.mul_comm]
              _ = _ := by rw [Rat.mul_inv_cancel _ (succCast_ne_zero k), Rat.one_mul]
          rw [he] at hs
          apply hs.mono
          have hle : (2*M)*(C*K^k) ≤ K*(C*K^k) := Rat.mul_le_mul_of_nonneg_right hMK
            (Rat.mul_nonneg hC (Rat.pow_nonneg hK))
          rw [Rat.pow_succ]
          grind [Rat.mul_assoc, Rat.mul_comm]

/-- Executable powers at arbitrary valid represented complex arguments. -/
def power (z : ComplexRaw) : Nat → ComplexRaw
  | 0 => one
  | k+1 => mul (power z k) z

theorem power_valid (z : ComplexRaw) (hz : z.Valid) (k : Nat) : (power z k).Valid := by
  induction k with
  | zero => exact ofQComplex_valid QComplex.one
  | succ k ih => exact mul_valid ih hz

theorem power_small (z : ComplexRaw) (hz : z.Valid) (R : Rat) (hR : 0 ≤ R)
    (h : Small z R) (k : Nat) : Small (power z k) ((2*R)^k) := by
  induction k with
  | zero =>
      simp only [Rat.pow_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro n m; change (-1 : Rat) ≤ 1; decide
      · intro n m; change (1 : Rat) ≤ 1; decide
      · intro n m; change (-1 : Rat) ≤ 0; decide
      · intro n m; change (0 : Rat) ≤ 1; decide
  | succ k ih =>
      have hh := Small.mul (power_valid z hz k) hz
        (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hR)) hR ih h
      have he : 2*(2*R)^k*R = (2*R)^(k+1) := by
        rw [Rat.pow_succ]; grind [Rat.mul_assoc, Rat.mul_comm]
      rw [he] at hh
      exact hh

/-- The actual represented value term has a geometric majorant on a
quantitatively specified local disk. The factor two is the complex
coordinate-norm multiplication constant. -/
theorem term_majorant (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R) (k : Nat) :
    Small (mul (coefficient a initial k) (power z k)) (2*C*(2*K*R)^k) := by
  have hh := Small.mul (coefficient_valid a initial ha h0 k) (power_valid z hz k)
    (Rat.mul_nonneg hC (Rat.pow_nonneg hK))
    (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hR))
    (coefficient_majorant a initial ha h0 M C K hM hC hK hMK hab hinit k)
    (power_small z hz R hR hpoint k)
  have hp : K^k * (2*R)^k = (2*K*R)^k := by
    have he : K*(2*R) = 2*K*R := by grind [Rat.mul_assoc, Rat.mul_comm]
    rw [← rational_mul_pow, he]
  have he : 2*(C*K^k)*(2*R)^k = 2*C*(2*K*R)^k := by
    calc
      _ = (2*C)*(K^k*(2*R)^k) := by grind [Rat.mul_assoc]
      _ = _ := by rw [hp]
  rw [he] at hh
  exact hh

/-- A literal finite block of terms, used to prove Cauchy estimates before
constructing an infinite sum. -/
def tailBlock (a : Nat → ComplexRaw) (initial z : ComplexRaw) (N : Nat) : Nat → ComplexRaw
  | 0 => zero
  | k+1 => add (tailBlock a initial z N k)
      (mul (coefficient a initial (N+k)) (power z (N+k)))

theorem tailBlock_majorant (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R) (N k : Nat) :
    Small (tailBlock a initial z N k)
      (RationalMajorant.geomTailPartial (2*C) (2*K*R) N k) := by
  induction k with
  | zero => exact Small.zero (by change (0 : Rat) ≤ 0; decide)
  | succ k ih =>
      exact small_add ih
        (term_majorant a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint (N+k))

/-- Uniform finite-tail bound on the supplied local disk. No infinite-sum
specification or completion has been assumed. -/
theorem tailBlock_bound (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hab : ∀ i, Small (a i) (M*K^i))
    (hinit : Small initial C) (hpoint : Small z R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) (N k : Nat) :
    Small (tailBlock a initial z N k) (4*C*(2*K*R)^N) := by
  have hs := tailBlock_majorant a initial z ha h0 hz M C K R hM hC hK hR hMK hab hinit hpoint N k
  apply hs.mono
  have ht := RationalMajorant.geometric_tail_partial_bound (C := 2*C) (r := 2*K*R) (N := N) (k := k)
    (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 2) hC)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR) hlocal
  have he : (2 : Rat)*2 = 4 := by grind
  simpa only [RationalMajorant.geomTailBound, ← Rat.mul_assoc, he] using ht

private theorem pow_le_half (q : Rat) (hq : 0 ≤ q) (hhalf : q ≤ (1 : Rat)/2) (k : Nat) :
    q^k ≤ ((1 : Rat)/2)^k := by
  induction k with
  | zero => simp [Rat.pow_zero]
  | succ k ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih hq)
        (Rat.mul_le_mul_of_nonneg_left hhalf (Rat.pow_nonneg (by rw [Rat.div_def, Rat.one_mul]; exact Rat.le_of_lt ((Rat.inv_pos).2 (by decide : (0 : Rat) < 2)))))

private theorem rational_nat_bound (q : Rat) : q ≤ ((q.num.natAbs + 1 : Nat) : Rat) := by
  by_cases hpos : 0 < q
  · have hdenpos : 0 < ((q.den : Nat) : Rat) :=
      (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat)) ?_ hdenpos
    rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
    have hnum : 0 ≤ q.num := Int.le_of_lt (rat_num_pos_of_pos hpos)
    have hcast : ((q.num.natAbs : Nat) : Rat) = (q.num : Rat) := by
      exact_mod_cast (Int.natAbs_of_nonneg hnum)
    calc
      (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := hcast.symm
      _ ≤ ((q.num.natAbs + 1 : Nat) : Rat) := by exact_mod_cast (Nat.le_succ q.num.natAbs)
      _ ≤ ((q.num.natAbs + 1 : Nat) : Rat) * ((q.den : Nat) : Rat) := by
        exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
          (Nat.pos_of_ne_zero q.den_nz))
  · exact Rat.le_trans (by grind : q ≤ 0)
      (by exact_mod_cast (Nat.zero_le (q.num.natAbs + 1)))

/-- The proved tail bound has a rational reciprocal-stage convergence
schedule, so it shrinks without an abstract completeness argument. -/
theorem tail_bound_shrinks (C q : Rat) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hhalf : q ≤ (1 : Rat)/2) : ShrinksToZero (fun N => 4*C*q^N) := by
  apply shrinksToZero_of_natOverSuccBound (C := (4*C).num.natAbs + 1)
  intro N
  have hp := Rat.le_trans (pow_le_half q hq hhalf N)
    (RationalMajorant.half_pow_le_one_div_succ N)
  have hm := Rat.mul_le_mul_of_nonneg_left hp (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 4) hC)
  have hb : 4*C*q^N ≤ (4*C) / ((N+1 : Nat) : Rat) := by
    simpa only [Rat.div_def, Rat.one_mul, Rat.mul_assoc] using hm
  apply Rat.le_trans hb
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right (rational_nat_bound (4*C))
    (Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.succ_pos N))))

end ComputableAnalysis.RiemannHilbert.LocalODE
