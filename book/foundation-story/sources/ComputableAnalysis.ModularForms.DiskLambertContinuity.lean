import ComputableAnalysis.ModularForms.DiskLambertSamples
import ComputableAnalysis.FiniteCoordinateInequality

/-! Uniform finite-prefix continuity on arbitrary compact Euclidean disks. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert RationalLambert CauchyTaylor EisensteinUnitDisk
set_option maxHeartbeats 1000000

theorem disk_add (p q : QComplex) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hp : InDisk p r) (hq : InDisk q s) : InDisk (QComplex.add p q) (r+s) := by
  have hc := qcomplex_coordinate_cauchy_schwarz p q
  have hmul := Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hp (normSq_nonneg q))
    (Rat.mul_le_mul_of_nonneg_left hq (rat_square_nonneg_basic r))
  have hdot : p.re*q.re+p.im*q.im≤r*s := by
    by_cases h : p.re*q.re+p.im*q.im≤r*s
    · exact h
    have hpos : 0<(p.re*q.re+p.im*q.im-r*s)*(p.re*q.re+p.im*q.im+r*s) :=
      Rat.mul_pos (by grind only) (by have := Rat.mul_nonneg hr hs; grind only)
    dsimp [InDisk] at *
    simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] at hc
    grind only
  have he := qcomplex_normSq_add_expansion p q
  dsimp [InDisk] at *
  grind only

theorem natPow_eq_pow (q : QComplex) (n : Nat) : QComplex.natPow q n=QComplex.pow q n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [QComplex.natPow,QComplex.pow,ih,QComplex.mul_comm_cert]

theorem power_difference_disk (p q : QComplex) (r D : Rat) (hr : 0≤r) (hD : 0≤D)
    (hp : InDisk p r) (hq : InDisk q r) (hd : InDisk (QComplex.sub p q) D) (n : Nat) :
    InDisk (QComplex.sub (QComplex.natPow p (n+1)) (QComplex.natPow q (n+1))) (((n+1:Nat):Rat)*r^n*D) := by
  induction n with
  | zero =>
    simp only [QComplex.natPow,QComplex.one_mul_cert,Rat.pow_zero,Rat.mul_one]
    simpa only [show ((0+1:Nat):Rat)=1 by decide +kernel,Rat.one_mul] using hd
  | succ n ih =>
    have h1 := disk_mul hp ih
    have h2 := disk_mul hd (disk_power hq (n+1))
    have h := disk_add _ _ _ _ (Rat.mul_nonneg hr (Rat.mul_nonneg (Rat.mul_nonneg Rat.natCast_nonneg (Rat.pow_nonneg hr)) hD))
      (Rat.mul_nonneg hD (Rat.pow_nonneg hr)) h1 h2
    have he : ∀u:QComplex, QComplex.natPow u (n+1+1)=QComplex.mul u (QComplex.natPow u (n+1)) := by
      intro u; rw [QComplex.natPow,QComplex.mul_comm_cert]
    rw [he,he,QComplex.mul_sub_mul_decompose]
    have hid : r*(((n+1:Nat):Rat)*r^n*D)+D*r^(n+1)=((n+1+1:Nat):Rat)*r^(n+1)*D := by
      rw [Rat.pow_succ]; simp only [Rat.natCast_add]; grind only
    rw [hid] at h
    exact h

def inverseBound (r : Rat) : Rat := 3*((1-r)*(1-r))⁻¹

theorem inverseBound_nonneg (r : Rat) (hr1 : r<1) : 0≤inverseBound r :=
  Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos (by grind only) (by grind only))))

theorem power_denominator (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r) (n : Nat) :
    (1-r)*(1-r)≤QComplex.normSq (denominator q n) ∧ (denominator q n).normBound≤3 := by
  have hpr := power_antitone hr (Rat.le_of_lt hr1) (show 1≤n+1 by omega)
  rw [Rat.pow_one] at hpr
  have hp : InDisk (QComplex.natPow q (n+1)) r := Rat.le_trans (disk_power hq _) (square_mono _ _ (Rat.pow_nonneg hr) hpr)
  have hs := denominator_separated hr (Rat.le_of_lt hr1) hp
  have hn := disk_normBound _ _ hr hp
  have hb := QComplex.normBound_sub_le QComplex.one (QComplex.natPow q (n+1))
  have hOne : QComplex.normBound QComplex.one=1 := by decide +kernel
  rw [hOne] at hb
  exact ⟨hs,by change (QComplex.sub QComplex.one (QComplex.natPow q (n+1))).normBound≤3; grind only⟩

private theorem normBound_disk (q : QComplex) : InDisk q q.normBound := by
  have hre := qabs_nonneg q.re
  have him := qabs_nonneg q.im
  have hs := Rat.mul_nonneg hre him
  have he : ∀x:Rat, qabs x*qabs x=x*x := by intro x; unfold qabs; split <;> grind only
  change q.re*q.re+q.im*q.im≤(qabs q.re+qabs q.im)*(qabs q.re+qabs q.im)
  rw [←he q.re,←he q.im]
  grind only

theorem factor_difference (p q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1)
    (hp : InDisk p r) (hq : InDisk q r) (n : Nat) :
    (QComplex.sub (factor p n) (factor q n)).normBound≤
      (inverseBound r)^2*(2*((n+1:Nat):Rat)*r^n)*(QComplex.sub p q).normBound := by
  have hpD := power_denominator p r hr hr1 hp n
  have hqD := power_denominator q r hr hr1 hq n
  have hmargin : 0<(1-r)*(1-r) := Rat.mul_pos (by grind only) (by grind only)
  have hd := QComplex.inverse_difference_normBound_le (by decide +kernel : (0:Rat)≤3) hmargin
    hpD.2 hqD.2 hpD.1 hqD.1
  have hid : QComplex.sub (denominator p n) (denominator q n)=
      QComplex.neg (QComplex.sub (QComplex.natPow p (n+1)) (QComplex.natPow q (n+1))) := by
    simp only [denominator,QComplex.sub,QComplex.add,QComplex.neg,QComplex.one,QComplex.mk.injEq]
    constructor <;> grind only
  rw [hid,QComplex.normBound_neg] at hd
  have hpow := disk_normBound _ _ (Rat.mul_nonneg (Rat.mul_nonneg Rat.natCast_nonneg (Rat.pow_nonneg hr)) (QComplex.normBound_nonneg _))
    (power_difference_disk p q r _ hr (QComplex.normBound_nonneg _) hp hq (normBound_disk _) n)
  have h := Rat.mul_le_mul_of_nonneg_left hpow (Rat.pow_nonneg (inverseBound_nonneg r hr1) (n := 2))
  have factorEq : ∀u:QComplex, InDisk u r → factor u n=QComplex.sub (QComplex.inverse (denominator u n)) QComplex.one := by
    intro u hu
    have hp := disk_power hu (n+1)
    have hpr := power_antitone hr (Rat.le_of_lt hr1) (show 1≤n+1 by omega)
    rw [Rat.pow_one] at hpr
    have hk := kernel_unfold (QComplex.natPow u (n+1))
      (denominator_ne_zero hr hr1 (show InDisk (QComplex.natPow u (n+1)) r from Rat.le_trans hp (square_mono _ _ (Rat.pow_nonneg hr) hpr)))
    dsimp [factor,kernel,denominator,RationalReciprocal.inverse,QComplex.inverse,QComplex.sub,QComplex.add,QComplex.neg,QComplex.one,QComplex.mul] at hk ⊢
    simp only [QComplex.mk.injEq] at hk ⊢
    constructor <;> grind only
  have he : QComplex.sub (factor p n) (factor q n)=QComplex.sub (QComplex.inverse (denominator p n)) (QComplex.inverse (denominator q n)) := by
    rw [factorEq p hp,factorEq q hq]
    simp only [QComplex.sub,QComplex.add,QComplex.neg,QComplex.one,QComplex.mk.injEq]
    constructor <;> grind only
  rw [he]
  dsimp [inverseBound] at h ⊢
  exact Rat.le_trans hd (by have := h; grind only)

/-- Finite sums of the rational majorant, used to bound all prefix derivatives. -/
def majorantPrefix (r : Rat) (k : Nat) : Nat → Rat
  | 0 => 0
  | N+1 => majorantPrefix r k N+majorant r k N

theorem majorantPrefix_nonneg (r : Rat) (hr : 0≤r) (hr1 : r<1) (k N : Nat) : 0≤majorantPrefix r k N := by
  induction N with
  | zero => exact Rat.le_refl
  | succ N ih => exact Rat.add_nonneg ih (majorant_nonneg r hr hr1 k N)

theorem majorantPrefix_mono (r : Rat) (hr : 0≤r) (hr1 : r<1) (k m n : Nat) (hmn : m≤n) : majorantPrefix r k m≤majorantPrefix r k n := by
  induction hmn with
  | refl => exact Rat.le_refl
  | @step n hmn ih =>
    change _≤majorantPrefix r k n+majorant r k n
    have := majorant_nonneg r hr hr1 k n
    grind only

theorem majorantPrefix_bound (r : Rat) (hr : 0≤r) (hr1 : r<1) (k N : Nat) :
    majorantPrefix r k N≤majorantPrefix r k (cutoff r k)+tail r k 0 := by
  by_cases hN : N≤cutoff r k
  · have := majorantPrefix_mono r hr hr1 k N (cutoff r k) hN
    have := tail_nonneg r hr hr1 k 0
    grind only
  · have stronger : ∀d, majorantPrefix r k (cutoff r k+d)≤majorantPrefix r k (cutoff r k)+tail r k 0-tail r k d := by
      intro d
      induction d with
      | zero => simp only [Nat.add_zero]; grind only
      | succ d ih =>
        have ht := majorant_geometric r hr hr1 k d
        have hi := Rat.mul_inv_cancel (1-ratio r) (show 1-ratio r≠0 by dsimp [ratio]; grind only)
        have he : tail r k d-tail r k (d+1)=majorant r k (cutoff r k)*(ratio r)^d := by
          dsimp [tail]; rw [Rat.pow_succ]; grind only
        change majorantPrefix r k (cutoff r k+d)+majorant r k (cutoff r k+d)≤_
        grind only
    have := stronger (N-cutoff r k)
    rw [Nat.add_sub_cancel' (show cutoff r k≤N by omega)] at this
    have := tail_nonneg r hr hr1 k (N-cutoff r k)
    grind only

def continuityFactor (r : Rat) : Rat := (inverseBound r)^2*(1-r)*r⁻¹
def continuityBound (r : Rat) (k : Nat) : Rat := continuityFactor r*(majorantPrefix r (k+1) (cutoff r (k+1))+tail r (k+1) 0)

theorem continuityFactor_nonneg (r : Rat) (hr : 0<r) (hr1 : r<1) : 0≤continuityFactor r := by
  unfold continuityFactor
  exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.pow_nonneg (inverseBound_nonneg r hr1)) (by grind only)) (Rat.le_of_lt (Rat.inv_pos.mpr hr))

theorem continuityBound_nonneg (r : Rat) (hr : 0<r) (hr1 : r<1) (k : Nat) : 0≤continuityBound r k :=
  Rat.mul_nonneg (continuityFactor_nonneg r hr hr1) (Rat.add_nonneg
    (majorantPrefix_nonneg r (Rat.le_of_lt hr) hr1 _ _) (tail_nonneg r (Rat.le_of_lt hr) hr1 _ _))

theorem term_difference (p q : QComplex) (r : Rat) (hr : 0<r) (hr1 : r<1)
    (hp : InDisk p r) (hq : InDisk q r) (k n : Nat) :
    (QComplex.sub (term p k n) (term q k n)).normBound≤continuityFactor r*majorant r (k+1) n*(QComplex.sub p q).normBound := by
  have h := Rat.mul_le_mul_of_nonneg_left (factor_difference p q r (Rat.le_of_lt hr) hr1 hp hq n)
    (Rat.pow_nonneg (n := k) (Rat.natCast_nonneg (a := n+1)))
  dsimp [term]
  rw [QComplex.sub_scaleRat,QComplex.normBound_scaleRat,qabs_eq_self_of_nonneg (Rat.pow_nonneg Rat.natCast_nonneg)]
  have hri := Rat.mul_inv_cancel r (Rat.ne_of_gt hr)
  have hgi := Rat.mul_inv_cancel (1-r) (show 1-r≠0 by grind only)
  have he : continuityFactor r*majorant r (k+1) n=((n+1:Nat):Rat)^k*((inverseBound r)^2*(2*((n+1:Nat):Rat)*r^n)) := by
    dsimp [continuityFactor,majorant]
    rw [Rat.pow_succ (((n+1:Nat):Rat)) k,Rat.pow_succ r n]
    calc
      _ = (((n+1:Nat):Rat)^k*((inverseBound r)^2*(2*((n+1:Nat):Rat)*r^n)))*(r*r⁻¹)*((1-r)*(1-r)⁻¹) := by grind only
      _ = _ := by rw [hri,hgi,Rat.mul_one,Rat.mul_one]
  rw [he]
  grind only

theorem prefix_difference (p q : QComplex) (r : Rat) (hr : 0<r) (hr1 : r<1)
    (hp : InDisk p r) (hq : InDisk q r) (k N : Nat) :
    (QComplex.sub (finitePrefix p k N) (finitePrefix q k N)).normBound≤continuityBound r k*(QComplex.sub p q).normBound := by
  have stronger : ∀N, (QComplex.sub (finitePrefix p k N) (finitePrefix q k N)).normBound≤
      continuityFactor r*majorantPrefix r (k+1) N*(QComplex.sub p q).normBound := by
    intro N
    induction N with
    | zero =>
      simp only [finitePrefix,majorantPrefix,Rat.mul_zero,Rat.zero_mul]
      rw [show (QComplex.sub QComplex.zero QComplex.zero).normBound=0 by decide +kernel]
      exact Rat.le_refl
    | succ N ih =>
      change (QComplex.sub (QComplex.add (finitePrefix p k N) (term p k N)) (QComplex.add (finitePrefix q k N) (term q k N))).normBound≤_
      rw [QComplex.sub_add_sub]
      have ht := term_difference p q r hr hr1 hp hq k N
      have := Rat.le_trans (QComplex.normBound_add_le _ _) (rat_add_le_add ih ht)
      dsimp [majorantPrefix]
      grind only
  have h := Rat.mul_le_mul_of_nonneg_left (majorantPrefix_bound r (Rat.le_of_lt hr) hr1 (k+1) N) (continuityFactor_nonneg r hr hr1)
  have hm := Rat.mul_le_mul_of_nonneg_right h (QComplex.normBound_nonneg (QComplex.sub p q))
  exact Rat.le_trans (stronger N) hm

end ComputableAnalysis.ModularForms.DiskLambert
