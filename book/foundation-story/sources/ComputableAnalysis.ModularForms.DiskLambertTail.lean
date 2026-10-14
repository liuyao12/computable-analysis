import ComputableAnalysis.ModularForms.RationalLambertArithmetic
import ComputableAnalysis.ModularForms.RationalLambertBounds
import ComputableAnalysis.CauchyTaylorKernel
import ComputableAnalysis.ComplexReciprocalCalculus

/-! Finite rational Lambert estimates on every closed Euclidean disk inside
 the unit disk. The cutoff is computed by a rational ceiling. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert RationalLambert CauchyTaylor
set_option maxHeartbeats 1000000

theorem pow_product (a b : Rat) (n : Nat) : (a*b)^n=a^n*b^n := by
  induction n with
  | zero => simp only [Rat.pow_zero,Rat.one_mul]
  | succ n ih => rw [Rat.pow_succ,Rat.pow_succ,Rat.pow_succ,ih]; grind only

theorem pow_add (a : Rat) (m n : Nat) : a^(m+n)=a^m*a^n := by
  induction n with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ n ih => rw [Nat.add_succ,Rat.pow_succ,Rat.pow_succ,ih]; grind only

theorem two_power_ge_one (k : Nat) : 1≤(2:Rat)^k := by
  induction k with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih => rw [Rat.pow_succ]; grind only

theorem binomial_bound (x : Rat) (hx : 0≤x) (hx1 : x≤1) (k : Nat) :
    (1+x)^k≤1+((2:Rat)^k-1)*x := by
  induction k with
  | zero => simp only [Rat.pow_zero]; grind only
  | succ k ih =>
    have h2 := two_power_ge_one k
    have hs := Rat.mul_le_mul_of_nonneg_right hx1 hx
    have hm := Rat.mul_le_mul_of_nonneg_left hs (show 0≤(2:Rat)^k-1 by grind only)
    have h := Rat.mul_le_mul_of_nonneg_right ih (show 0≤1+x by grind only)
    rw [Rat.pow_succ,Rat.pow_succ]
    grind only

def cutoff (r : Rat) (k : Nat) : Nat := (2*(2:Rat)^k/(1-r)).ceil.natAbs+1

theorem cutoff_bound (r : Rat) (k : Nat) : 2*(2:Rat)^k/(1-r)≤(cutoff r k:Rat) := by
  have h := Int.le_natAbs (a := (2*(2:Rat)^k/(1-r)).ceil)
  have hc : ((2*(2:Rat)^k/(1-r)).ceil:Rat)≤(cutoff r k:Rat) := by
    unfold cutoff
    exact_mod_cast (show (2*(2:Rat)^k/(1-r)).ceil≤(2*(2:Rat)^k/(1-r)).ceil.natAbs+1 by omega)
  exact Rat.le_trans Rat.le_ceil hc

def ratio (r : Rat) : Rat := (1+r)/2
def majorant (r : Rat) (k n : Nat) : Rat := 2*((n+1:Nat):Rat)^k*r^(n+1)*(1-r)⁻¹

theorem majorant_nonneg (r : Rat) (hr : 0≤r) (hr1 : r<1) (k n : Nat) : 0≤majorant r k n := by
  unfold majorant
  exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg Rat.natCast_nonneg))
    (Rat.pow_nonneg hr)) (Rat.le_of_lt (Rat.inv_pos.mpr (by grind only)))

theorem majorant_step (r : Rat) (hr : 0≤r) (hr1 : r<1) (k n : Nat) (hn : cutoff r k≤n) :
    majorant r k (n+1)≤majorant r k n*ratio r := by
  let a : Rat := ((n+1:Nat):Rat)
  have ha : 0<a := Rat.natCast_pos.mpr (by omega)
  have ha1 : 1≤a := by dsimp [a]; exact_mod_cast (show 1≤n+1 by omega)
  have hi := Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
  have hai : 0≤a⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr ha)
  have hai1 : a⁻¹≤1 := by
    have h := Rat.inv_antitone_of_pos (by decide +kernel : (0:Rat)<1) ha1
    simpa only [show (1:Rat)⁻¹=1 by decide +kernel] using h
  have hb := binomial_bound (a⁻¹) hai hai1 k
  have hm := Rat.mul_le_mul_of_nonneg_left hb (Rat.pow_nonneg (Rat.le_of_lt ha) (n := k))
  have he : a*(1+a⁻¹)=a+1 := by grind only
  rw [←pow_product,he] at hm
  have hc := cutoff_bound r k
  have hcn : (cutoff r k:Rat)≤(n:Rat) := by exact_mod_cast hn
  have hg : 0<1-r := by grind only
  have hc' := Rat.le_trans hc (show (cutoff r k:Rat)≤a by dsimp [a]; simp only [Rat.natCast_add]; grind only)
  have hiG := Rat.mul_inv_cancel (1-r) (Rat.ne_of_gt hg)
  have hd : 2*(2:Rat)^k≤a*(1-r) := by
    have h := Rat.mul_le_mul_of_nonneg_right hc' (Rat.le_of_lt hg)
    rw [Rat.div_def,Rat.mul_assoc,Rat.inv_mul_cancel (1-r) (Rat.ne_of_gt hg),Rat.mul_one] at h
    exact h
  have h2 : 0≤(2:Rat)^k := Rat.pow_nonneg (by decide +kernel)
  have hx : ((2:Rat)^k-1)*a⁻¹*r≤(1-r)/2 := by
    have h := Rat.mul_le_mul_of_nonneg_right hd hai
    have hid : a*(1-r)*a⁻¹=1-r := by
      rw [Rat.mul_comm a (1-r),Rat.mul_assoc,hi,Rat.mul_one]
    rw [hid] at h
    have hx := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hr1) (Rat.mul_nonneg h2 hai)
    have hy : ((2:Rat)^k-1)*a⁻¹*r≤(2:Rat)^k*a⁻¹*r :=
      Rat.mul_le_mul_of_nonneg_right
        (Rat.mul_le_mul_of_nonneg_right (show (2:Rat)^k-1≤(2:Rat)^k by grind only) hai) hr
    rw [show (1-r)/2=(1-r)*(1/2:Rat) by simp only [Rat.div_def,Rat.one_mul]]
    have hhalf := Rat.mul_le_mul_of_nonneg_right h (by decide +kernel : (0:Rat)≤1/2)
    have hh : 2*(2:Rat)^k*a⁻¹*(1/2:Rat)=(2:Rat)^k*a⁻¹ := by grind only
    rw [hh] at hhalf
    exact Rat.le_trans hy (Rat.le_trans (by simpa only [Rat.one_mul,Rat.mul_comm] using hx) hhalf)
  have hpow : (a+1)^k*r≤a^k*ratio r := by
    have h := Rat.mul_le_mul_of_nonneg_right hm hr
    have hh := Rat.mul_le_mul_of_nonneg_left hx (Rat.pow_nonneg (Rat.le_of_lt ha) (n := k))
    dsimp [ratio]
    grind only
  have hp := Rat.mul_le_mul_of_nonneg_right hpow
    (Rat.mul_nonneg (Rat.pow_nonneg hr (n := n+1)) (Rat.le_of_lt (Rat.inv_pos.mpr hg)))
  unfold majorant
  rw [Rat.pow_succ r (n+1)]
  simp only [Rat.natCast_add] at *
  dsimp [a] at *
  grind only

theorem majorant_geometric (r : Rat) (hr : 0≤r) (hr1 : r<1) (k n : Nat) :
    majorant r k (cutoff r k+n)≤majorant r k (cutoff r k)*(ratio r)^n := by
  induction n with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]; exact Rat.le_refl
  | succ n ih =>
    have h := majorant_step r hr hr1 k (cutoff r k+n) (by omega)
    have hm := Rat.mul_le_mul_of_nonneg_right ih (show 0≤ratio r by dsimp [ratio]; grind only)
    rw [Nat.add_succ,Rat.pow_succ]
    grind only

theorem disk_normBound (z : QComplex) (r : Rat) (hr : 0≤r) (hz : InDisk z r) : z.normBound≤2*r := by
  have h := disk_coordinates hr hz
  unfold QComplex.normBound qabs
  split <;> split <;> grind only

theorem term_bound (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r) (k n : Nat) :
    (term q k n).normBound≤majorant r k n := by
  have hp := disk_power hq (n+1)
  have hpr : 0≤r^(n+1) := Rat.pow_nonneg hr
  have hpr1 : r^(n+1)≤r := by
    simpa only [Rat.pow_one] using power_antitone hr (Rat.le_of_lt hr1) (show 1≤n+1 by omega)
  have hk := kernel_disk hr hr1 (show InDisk (QComplex.natPow q (n+1)) r from
    Rat.le_trans hp (by have h := pow_mono (r^(n+1)) r hpr hpr1 2; simpa only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul] using h))
  have hf := disk_mul hp hk
  have hn : 0≤r^(n+1)*(1-r)⁻¹ := Rat.mul_nonneg hpr (Rat.le_of_lt (Rat.inv_pos.mpr (by grind only)))
  have hb := disk_normBound _ _ hn hf
  have he : RationalReciprocal.inverse (denominator q n)=kernel (QComplex.natPow q (n+1)) := rfl
  unfold term factor
  rw [QComplex.normBound_scaleRat,qabs_eq_self_of_nonneg (Rat.pow_nonneg Rat.natCast_nonneg),he]
  have h := Rat.mul_le_mul_of_nonneg_left hb (Rat.pow_nonneg (n := k) (Rat.natCast_nonneg (a := n+1)))
  dsimp [majorant]
  grind only

def tail (r : Rat) (k N : Nat) : Rat := majorant r k (cutoff r k)*(ratio r)^N*(1-ratio r)⁻¹

theorem tail_nonneg (r : Rat) (hr : 0≤r) (hr1 : r<1) (k N : Nat) : 0≤tail r k N := by
  unfold tail
  exact Rat.mul_nonneg (Rat.mul_nonneg (majorant_nonneg r hr hr1 k _) (Rat.pow_nonneg (show 0≤ratio r by dsimp [ratio]; grind only)))
    (Rat.le_of_lt (Rat.inv_pos.mpr (show 0<1-ratio r by dsimp [ratio]; grind only)))

theorem tail_shrinks (r : Rat) (hr : 0≤r) (hr1 : r<1) (k : Nat) : ShrinksToZero (tail r k) := by
  have hg : 0<1-ratio r := by dsimp [ratio]; grind only
  let C := majorant r k (cutoff r k)*(1-ratio r)⁻¹*(1-ratio r)⁻¹
  have hC : 0≤C := Rat.mul_nonneg (Rat.mul_nonneg (majorant_nonneg r hr hr1 k _)
    (Rat.le_of_lt (Rat.inv_pos.mpr hg))) (Rat.le_of_lt (Rat.inv_pos.mpr hg))
  let B := C.ceil.natAbs+1
  have hCB : C≤(B:Rat) := by
    have hi : C.ceil≤(B:Int) := by dsimp [B]; have := Int.le_natAbs (a := C.ceil); omega
    exact Rat.le_trans Rat.le_ceil (by exact_mod_cast hi)
  apply shrinksToZero_of_natOverSuccBound (C := B)
  intro n
  have hp := power_nat_bound (show 0≤ratio r by dsimp [ratio]; grind only) (show ratio r<1 by dsimp [ratio]; grind only) n
  have hm := Rat.mul_le_mul_of_nonneg_left hp (Rat.mul_nonneg (majorant_nonneg r hr hr1 k (cutoff r k)) (Rat.le_of_lt (Rat.inv_pos.mpr hg)))
  have hx := Rat.mul_le_mul_of_nonneg_right hCB (Rat.le_of_lt (Rat.inv_pos.mpr (show (0:Rat)<((n+1:Nat):Rat) from Rat.natCast_pos.mpr (by omega))))
  dsimp [tail,C] at *
  rw [Rat.div_def] at *
  grind only

theorem tail_antitone (r : Rat) (hr : 0≤r) (hr1 : r<1) (k m n : Nat) (hmn : m≤n) : tail r k n≤tail r k m := by
  have hp := power_antitone (show 0≤ratio r by dsimp [ratio]; grind only) (show ratio r≤1 by dsimp [ratio]; grind only) hmn
  have h := Rat.mul_le_mul_of_nonneg_left hp (majorant_nonneg r hr hr1 k (cutoff r k))
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.inv_pos.mpr (show 0<1-ratio r by dsimp [ratio]; grind only)))

theorem prefix_tail (q : QComplex) (r : Rat) (hr : 0≤r) (hr1 : r<1) (hq : InDisk q r)
    (k N d : Nat) :
    (QComplex.sub (finitePrefix q k (cutoff r k+N+d)) (finitePrefix q k (cutoff r k+N))).normBound≤tail r k N := by
  have stronger : ∀d, (QComplex.sub (finitePrefix q k (cutoff r k+N+d)) (finitePrefix q k (cutoff r k+N))).normBound≤
      tail r k N-tail r k (N+d) := by
    intro d
    induction d with
    | zero =>
      simp only [Nat.add_zero,QComplex.sub,QComplex.add,QComplex.neg,QComplex.normBound]
      have he : ∀a:Rat, a + -a=0 := by intro a; grind only
      simp only [he,show qabs (0:Rat)=0 by decide +kernel]
      grind only
    | succ d ih =>
      have hid : QComplex.sub (finitePrefix q k (cutoff r k+N+(d+1))) (finitePrefix q k (cutoff r k+N))=
        QComplex.add (QComplex.sub (finitePrefix q k (cutoff r k+N+d)) (finitePrefix q k (cutoff r k+N))) (term q k (cutoff r k+N+d)) := by
        simp only [Nat.add_succ,finitePrefix,QComplex.sub,QComplex.add,QComplex.neg,QComplex.mk.injEq]
        constructor <;> grind only
      rw [hid]
      have ht := Rat.le_trans (term_bound q r hr hr1 hq k (cutoff r k+N+d))
        (by simpa only [Nat.add_assoc] using majorant_geometric r hr hr1 k (N+d))
      have h := Rat.le_trans (QComplex.normBound_add_le _ _) (rat_add_le_add ih ht)
      have hi := Rat.mul_inv_cancel (1-ratio r) (show 1-ratio r≠0 by dsimp [ratio]; grind only)
      have he : tail r k (N+d)-tail r k (N+(d+1))=majorant r k (cutoff r k)*(ratio r)^(N+d) := by
        dsimp [tail]
        rw [Nat.add_succ,Rat.pow_succ]
        grind only
      grind only
  have h := stronger d
  have ht := tail_nonneg r hr hr1 k (N+d)
  grind only

end ComputableAnalysis.ModularForms.DiskLambert
